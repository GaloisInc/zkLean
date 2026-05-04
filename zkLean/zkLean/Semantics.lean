import Cslib.Foundations.Control.Monad.Free.Fold
import Init.Data.Array.Basic
import Init.Data.Array.Set
import Init.Prelude
import Mathlib.Algebra.Field.Defs

import zkLean.AST
import zkLean.Builder
import zkLean.SimpSets

/-- Class for Fields with additional properties necessary for zkLean -/
class ZKField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f where
  -- Mask the lower `num_bits` of a field element and convert to a vector of bits.
  field_to_bits {num_bits: Nat} (val: f) : Vector f num_bits
  field_to_nat (val: f) : Nat

structure RamState f [ZKField f] where
  capacity: ℕ
  state: (Std.HashMap f f)

abbrev RamStates f [ZKField f] := Array (RamState f)

structure ZKState (f : Type) [ZKField f] where
  allocated_witness_count: Nat
  witness: Array f
  rams: RamStates f
deriving instance Inhabited for ZKState


/-- Interprets a ZK operation give a state. On success, it returns the result of the operation and the updated state. If a constraint in the circuit is not satisfied, it short circuits and returns `.none`. -/
@[simp_ZKBuilder]
def ZKOpInterp [ZKField f] {β} (op : ZKOp f β) : StateT (ZKState f) Option β :=
  match op with
  | ZKOp.AllocWitness => do
      let st ← get
      let idx := st.allocated_witness_count
      set ({ st with allocated_witness_count := idx + 1 })
      .pure (ZKExpr.Field (<- st.witness[idx]?))

  | ZKOp.ConstrainEq x y => do
      if x.eval == y.eval then
        .pure ()
      else
        .none
  | ZKOp.ConstrainR1CS a b c => do
      let fa := a.eval
      let fb := b.eval
      let fc := c.eval
      if fa * fb == fc then
        .pure ()
      else
        .none
  | ZKOp.ComposedLookupMLE tbl args => -- #v[c0, c1, c2, c3] => do
      let chunks := args.map (λ e => ZKField.field_to_bits e.eval)
      let res := evalComposedLookupTable tbl chunks
      .pure (ZKExpr.Field res)
  | ZKOp.LookupMLE n tbl arg1 arg2 =>
      let res := evalLookupTableMLE tbl
         (ZKField.field_to_bits (num_bits := n) arg1.eval)
         (ZKField.field_to_bits (num_bits := n) arg2.eval)
      pure (ZKExpr.Field res)
  | ZKOp.LookupMaterialized table arg => do
      let res ← table[ZKField.field_to_nat arg.eval]?
      pure (ZKExpr.Field res)
  | ZKOp.MuxLookup chunks cases =>
      let chunks := chunks.map (λ e => ZKField.field_to_bits e.eval)
      let sum := Array.foldl (fun acc (flag, tbl) =>
        acc + flag.eval * (evalComposedLookupTable tbl chunks)) 0 cases
      pure (ZKExpr.Field sum)
  | ZKOp.RamNew n => do
      let st ← get
      let id := st.rams.size
      let state := { capacity:= n, state:= Std.HashMap.emptyWithCapacity n }
      set ({st with rams := st.rams.push state})
      pure ({id := { ram_id := id}})
  | ZKOp.RamRead ram_id a => do
      let st ← get
      let addr_f := a.eval
      let ram ← st.rams[ram_id.id.ram_id]?
      let val ← ram.state[addr_f]?
      pure (ZKExpr.Field val)
  | ZKOp.RamWrite ram_id a v => do
      let st ← get
      let addr_f := a.eval
      let val_f := v.eval
      if h:ram_id.id.ram_id < st.rams.size then
        let ram := st.rams[ram_id.id.ram_id]
        let new_ram := {ram with state := ram.state.insert addr_f val_f}
        let new_rams := st.rams.set ram_id.id.ram_id new_ram
        set {st with rams := new_rams}
        pure ()
      else
        .none

@[simp_ZKBuilder]
def runZKBuilder [ZKField f] : ZKBuilder f α → StateT (ZKState f) Option α :=
  Cslib.FreeM.foldFreeM
    -- pure case : just return the value, leaving the state untouched
    (fun a => .pure a)
    -- bind case : interpret one primitive with `ZKOpInterp`, then feed the
    -- resulting value into the continuation on the updated state.
    (fun op k => do
      let b ← ZKOpInterp op
      k b)

/-- Main semantics function

It takes a ZK circuit and list of witnesses and returns a boolean indicating
whether the circuit is satisfied.
-/
@[simp_ZKSemantics]
def semantics [ZKField f] (circuit: ZKBuilder f α) (witness: List f) : Bool :=
  let st : ZKState f := {witness := witness.toArray, allocated_witness_count := 0, rams:= Array.empty}
  let res := runZKBuilder circuit st
  res.isSome
