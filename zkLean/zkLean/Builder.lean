import Cslib.Foundations.Control.Monad.Free
import Std.Data.HashMap.Basic
import Std.Do
import Std.Tactic.Do

import zkLean.AST
import zkLean.LookupTable
import zkLean.SimpSets


/-- Type to identify a specific RAM -/
structure RamId where
  ram_id: Nat
deriving instance Inhabited for RamId

/-- Type for RAM -/
structure RAM (f: Type) where
  id: RamId
deriving instance Inhabited for RAM

/-- Primitive instructions for the circuit DSL - the effect 'functor'. -/
inductive ZKOp (f : Type) : Type → Type
| AllocWitness                         : ZKOp f (ZKExpr f)
| ConstrainEq    (x y    : ZKExpr f)   : ZKOp f PUnit
| ConstrainR1CS  (a b c  : ZKExpr f)   : ZKOp f PUnit
| ComposedLookupMLE (tbl : ComposedLookupTable f 16 4)
                    (args : Vector (ZKExpr f) 4) : ZKOp f (ZKExpr f)
| LookupMLE (n : Nat) (lookupMLE: LookupTableMLE f (n + n))
            (arg1 arg2: ZKExpr f) : ZKOp f (ZKExpr f)
| LookupMaterialized (table: Vector f n) (arg: ZKExpr f) : ZKOp f (ZKExpr f)
| MuxLookup      (chunks : Vector (ZKExpr f) 4)
                 (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
                                                     : ZKOp f (ZKExpr f)
| RamNew         (size   : Nat)                       : ZKOp f (RAM f)
| RamRead        (ram    : RAM f) (addr  : ZKExpr f)  : ZKOp f (ZKExpr f)
| RamWrite       (ram    : RAM f) (addr v: ZKExpr f)  : ZKOp f PUnit

/-- Type for the ZK circuit builder monad. -/
@[simp_ZKBuilder]
def ZKBuilder (f : Type) := Cslib.FreeM (ZKOp f)

@[simp_ZKBuilder]
instance : Monad (ZKBuilder f) := by
 unfold ZKBuilder
 infer_instance

instance : LawfulMonad (ZKBuilder f) := by
  unfold ZKBuilder
  infer_instance

namespace ZKBuilder

open Cslib

-- We define helper functions for each of the primitive operations in the DSL, using `liftM` to lift them to the `ZKBuilder` monad.

/-- Get a fresh witness variable. -/
@[simp_ZKBuilder]
def witness : ZKBuilder f (ZKExpr f) :=
  FreeM.lift ZKOp.AllocWitness

/-- Constrain two expressions to be equal in circuit. -/
@[simp_ZKBuilder]
def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainEq x y)

/--
Helper function to create a single row of a R1CS constraint (Az * Bz = Cz).
Here's an example to constrain `b` to be a boolean (0 or 1):
```
constrainR1CS (b) (1 - b) (0)
```
-/
@[simp_ZKBuilder]
def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainR1CS a b c)

/--
Perform a lookup into the given MLE composed table with the provided argument chunks.
-/
@[simp_ZKBuilder]
def lookup_mle_composed (tbl : ComposedLookupTable f 16 4)
  (args : Vector (ZKExpr f) 4) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.ComposedLookupMLE tbl args)

/--
Perform a lookup into the given MLE table with the provided arguments.
-/
def lookup_mle (tbl : LookupTableMLE f (n + n)) (e1 e2: ZKExpr f) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.LookupMLE n tbl e1 e2)

/--
Perform a lookup in a given materialized table with the provided argument.
-/
def lookup_materialized (tbl: Vector f n) (e: ZKExpr f) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.LookupMaterialized tbl e)


/--
Helper function to perform a mux over a set of lookup tables.
We use zkLean to compute the product of every flag with the result of the lookup.
This corresponds to the [`prove_primary_sumcheck`](https://github.com/a16z/jolt/blob/main/jolt-core/src/jolt/vm/instruction_lookups.rs#L980) function in Jolt.
All flags in `flags_and_lookups` should be 0 or 1 with only a single flag being set to 1.
Example:
```
mux_lookup
    #v[arg0, arg1, arg2, arg3]
    #[
      (addFlag, addInstruction),
      (andFlag, andInstruction),
      ...
    ]
```
-/
@[simp_ZKBuilder]
def muxLookup (chunks : Vector (ZKExpr f) 4)
              (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
  : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.MuxLookup chunks cases)

/--
Create a new oblivious RAM in circuit of the given size.
-/
@[simp_ZKBuilder]
def ramNew (n : Nat) : ZKBuilder f (RAM f) :=
  FreeM.lift (ZKOp.RamNew n)

/--
Perform an oblivious RAM read.
Here's an example of how you might perform a CPU load instruction:
```
-- INSTR: load rs_13 rd_7
let addr <- ram_read  ram_reg  13
let v    <- ram_read  ram_mem  addr
            ram_write ram_reg  7    v
```
-/
@[simp_ZKBuilder]
def ramRead (r : RAM f) (a : ZKExpr f) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.RamRead r a)

/--
Perform an oblivious RAM write.
Here's an example of how you might perform a CPU load instruction:
```
-- INSTR: load rs_13 rd_7
let addr <- ram_read  ram_reg  13
let v    <- ram_read  ram_mem  addr
            ram_write ram_reg  7    v
```
-/
@[simp_ZKBuilder]
def ramWrite (r : RAM f) (a v : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.RamWrite r a v)

end ZKBuilder

open ZKBuilder

/--
A type is Witnessable if is has an associated building process.
-/
class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/- Expressions of type `ZKExpr` are `Witnessable`. -/
@[simp_ZKBuilder]
instance : Witnessable f (ZKExpr f) where
  witness := witness

/- A vector of  `Witnessable` expressions is `Witnessable`. -/
@[simp_ZKBuilder]
instance [Witnessable f a] : Witnessable f (Vector a n) where
  witness := Vector.ofFnM (λ _ => Witnessable.witness)
