import Cslib.Foundations.Control.Monad.Free
import Lean.Elab.Term
import Lean.Meta.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Kleene
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Std.Data.HashMap.Basic
import Std.Do
import Std.Tactic.BVDecide

import zkLean
import zkLean.SimpSets

open Lean Meta Elab Term
open Std Do

attribute [simp_FreeM] bind
attribute [simp_FreeM] default
attribute [simp_FreeM] Cslib.FreeM.bind
attribute [simp_FreeM] Cslib.FreeM.foldFreeM

attribute [simp_Triple] Std.Do.Triple
attribute [simp_Triple] Std.Do.SPred.entails
attribute [simp_Triple] Std.Do.PredTrans.apply
attribute [simp_Triple] Std.Do.PredTrans.pure
attribute [simp_Triple] Std.Do.wp

-- ZKProof 7 examples

def example1 [ZKField f] : ZKBuilder f (ZKExpr f) := do
  let x: ZKExpr f <- Witnessable.witness
  let one: ZKExpr f := 1
  ZKBuilder.constrainEq (x * (x - one)) 0
  return x

def eq8 [Field f] : Subtable f 16 :=
  let product v := Traversable.foldl (. * .) 1 v.toList
  let first_half (v: Vector _ 16) : Vector _ 8 := Vector.take v 8
  let second_half (v: Vector _ 16) : Vector _ 8 := Vector.drop v 8
  let mle_on_pair a b:= product (Vector.zipWith (λ x y => (x * x + (1 - x) * (1 - y))) a b)
  let mle (v: Vector f 16): f := mle_on_pair (first_half v) (second_half v)
  subtableFromMLE mle

def eq32 [Field f] : ComposedLookupTable f 16 4 :=
  mkComposedLookupTable
    #[ (eq8, 0), (eq8, 1), (eq8, 2), (eq8, 3) ].toVector
    (fun results => results.foldl (· * ·) 1)

structure RISCVState (f: Type) where
  pc: ZKExpr f
  registers: Vector (ZKExpr f) 32
deriving instance Inhabited for RISCVState

instance: Witnessable f (RISCVState f) where
  witness := do
   let pc <- Witnessable.witness
   let registers <- Witnessable.witness
   pure { pc:=pc, registers := registers}


def step [ZKField f] (prev_st : RISCVState f) : ZKBuilder f (RISCVState f) := do
  let new_st: RISCVState f <- Witnessable.witness -- allocate a wire for witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- ZKBuilder.lookup_mle_composed eq32 #v[r1, r1, r2, r2] -- Note: This example doesn't really make sense anymore.
  ZKBuilder.constrainEq new_st.registers[0] isEq

  return new_st


def rv_circ [ZKField f]: ZKBuilder f (List (RISCVState f))  := do
  let (init_state : RISCVState f) <- Witnessable.witness -- fix this
  let (state1 : RISCVState f) <- step init_state
  let (state2 : RISCVState f) <- step state1
  let (state3 : RISCVState f) <- step state2
  pure [init_state, state1, state2, state3]







-- Jolt examples

def eqSubtable [ZKField f] : Subtable f 2 := subtableFromMLE (λ x => (x[0] * x[1] + (1 - x[0]) * (1 - x[1])))

-- forall x y : F . 0 <= x < 2^n && 0 <= y < 2^n => eqSubtable (bits x) (bits y) == (toI32 x == toI32 y)


structure JoltR1CSInputs (f : Type):  Type where
  chunk_1: ZKExpr f
  chunk_2: ZKExpr f
  /- ... -/

-- A[0] = C * 1 + var[3] * 829 + ...
-- Example of what we extract from Jolt
-- TODO: Make a struct for the witness variables in a Jolt step. Automatically extract this from JoltInputs enum?
def uniform_jolt_constraint [ZKField f] (jolt_inputs: JoltR1CSInputs f) : ZKBuilder f PUnit := do
  ZKBuilder.constrainR1CS ((1 +  jolt_inputs.chunk_1 ) * 829) 1 1
  ZKBuilder.constrainR1CS 1 1 ((1 +  jolt_inputs.chunk_1 ) * 829)
  -- ...

--   ...
-- def non_uniform_jolt_constraint step_1 step_2 = do
--   constrainR1CS (step_1.jolt_flag * 123) (step_2.jolt_flag + 1) (1)
--   constrainR1CS (step_1.jolt_flag * 872187687 + ...) (step_2.jolt_flag + 1) (1)
--   ...

attribute [simp_circuit] runZKBuilder

@[simp_circuit]
def run_circuit' [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  semantics circuit witness


-- {} constrainEq2 a b {a_f == b_f}
-- {} run_circuit (constrainEq2 a b) {state ws res => res <-> (eval a · ·  == eval b ws state)}
-- run_circuit : ReaderT [f] (ReaderT (ZKBuilderState f)) bool
@[simp_ZKBuilder]
def constrainEq2 [ZKField f] (a b : ZKExpr f) : ZKBuilder f PUnit := do
  -- NOTE: equivalently `constrainR1CS (a - b) 1 0`
  ZKBuilder.constrainR1CS a 1 b

@[simp_circuit]
def circuit1 [ZKField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

-- {} constrainEq3 a b c {a == c}
def constrainEq3 [ZKField f] (a b c : ZKExpr f) : ZKBuilder f PUnit := do
  constrainEq2 a b
  constrainEq2 b c


instance : Fact (Nat.Prime 7) := by decide
instance : ZKField (ZMod 7) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  field_to_bits {num_bits: Nat} f :=
    let bv : BitVec 3 := BitVec.ofFin (Fin.castSucc f)
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)
  field_to_nat f := f.val

#check run_circuit'

#eval run_circuit' (f := ZMod 7) circuit1 [1, 1]
#eval run_circuit' (f := ZMod 7) circuit1 [1, 2]

def circuit12 : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

#eval run_circuit' circuit12 [0, 1]
#eval run_circuit' circuit12 [0, 0]


#check StateT.run_bind
attribute [local simp] StateT.run_bind


lemma match_if {α: Type} (cond: Prop) [Decidable cond] (a b: β) (s1: α):
  -- Note: this is the same as `match`, but if we were to use `match` syntax, it
  -- would not unify correctly with our goal when applying it below.
  PredTrans.pushOption.match_1 _
    (if cond then some s1 else none)
    (fun _ => a)
    (fun () => b)
  = (if cond then a else b) := by
    split
    · grind
    · grind

theorem constrainEq2.soundness [ZKField f] (a b : ZKExpr f) :
  ⦃ λ _s => ⌜True⌝ ⦄
  constrainEq2 a b
  ⦃ ⇓? _r _s => ⌜a.eval = b.eval⌝ ⦄
  := by
  mintro _ ∀s
  simp
    [ simp_FreeM, simp_ZKBuilder, simp_Triple, simp_circuit, wpZKBuilder, OptionT.mk
    , ExceptConds.true, ExceptConds.const, liftM, monadLift, MonadLift.monadLift, StateT.run
    , StateT.pure, bind, StateT.bind, StateT.pure]
  rw [ite_apply]
  simp [StateT.pure, StateT.lift, match_if]
  split
  . aesop
  · simp

theorem constrainEq3.soundness [ZKField f] (a b c : ZKExpr f) :
  ⦃ λ _s => ⌜True⌝ ⦄
  constrainEq3 a b c
  ⦃ ⇓? _r _s => ⌜a.eval = c.eval⌝ ⦄
  := by
  mintro _ ∀s0
  unfold constrainEq3
  mspec (constrainEq2.soundness a b)
  mrename_i Eq1
  mpure Eq1
  mspec (constrainEq2.soundness b c)
  mrename_i Eq2
  mpure Eq2
  aesop

