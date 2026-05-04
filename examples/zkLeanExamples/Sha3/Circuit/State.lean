
import BVModEq.Mappings
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import zkLean
import zkLeanExamples.Sha3.Spec

-- From ArkLib: BN254 scalar
@[reducible]
def scalarFieldSize : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev f := ZMod scalarFieldSize

theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  -- Proof is in ArkLib
  sorry
instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩
instance : Field f := ZMod.instField scalarFieldSize
instance : ZKField f where
  hash x := x.val.toUInt64
  field_to_bits {num_bits: Nat} felt :=
    sorry
    -- let bv : BitVec 64 := BitVec.ofFin ⟨n.val, Nat.lt_trans (ZMod.val_lt felt) (by decide : felt < 2 ^ 64)⟩
    -- -- TODO: Double check the endianess.
    -- Vector.map (fun i =>
    --   if _:i < 3 then
    --     if bv[i] then 1 else 0
    --   else
    --     0
    -- ) (Vector.range num_bits)
  field_to_nat f := f.val

-- State of keccak
structure State where
  lanes : Vector (ZKExpr f) 25

/-- Get lane at position (x, y) --/
def State.get (s : State) (x y : Fin 5) : ZKExpr f :=
  s.lanes[y.val * 5 + x.val]

-- Check that a field element expression is equal to a bitvector.
def eqF (felt : ZKExpr f) (bv : BitVec 64) : Bool :=
  felt.eval == (bv.toNat : f)

lemma eqFIff : some bv = BVModEq.map_f_to_bv 64 felt ↔ eqF (ZKExpr.Field felt) bv := by
  constructor

  simp [BVModEq.map_f_to_bv, eqF, ZKExpr.eval]
  intros h1 h2
  rw [h2]
  simp
  rw [Nat.mod_eq_of_lt h1]
  simp

  simp [BVModEq.map_f_to_bv, eqF, ZKExpr.eval]
  intros h1
  rw [h1]
  have h2 : bv.toNat < 18446744073709551616 := by
    apply BitVec.isLt
  have h3: bv.toNat < scalarFieldSize := by
    apply (lt_trans h2)
    decide
  constructor
  ·
    simp
    rw [Nat.mod_eq_of_lt h3]
    assumption
  ·
    simp
    rw [Nat.mod_eq_of_lt h3]
    simp

lemma eqFhelper : eqF x a -> a = b -> eqF x b := by
  intros h1 h2
  rw [← h2]
  assumption

-- Check that a state of field elements is equal to a state of bitvectors.
def eqState (s : State) (sBV : SHA3.State) : Bool :=
  (s.lanes.zip sBV.lanes).all (λ (felt, bv) => eqF felt bv)
