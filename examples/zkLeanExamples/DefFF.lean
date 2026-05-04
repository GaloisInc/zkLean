import Mathlib.Algebra.Field.ZMod
import zkLean.Formalism
import BVModEq.TranslateAll

abbrev ff := 17179869263

instance : Fact (Nat.Prime ff) := by sorry

instance : ZKField (ZMod ff) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  field_to_bits {num_bits: Nat} f :=
    let bv : BitVec 64 := BitVec.ofFin ⟨f.val, Nat.lt_trans (ZMod.val_lt f) (by decide : ff < 2 ^ 64)⟩
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)
  field_to_nat f := f.val


instance : Witnessable (ZMod ff) (ZMod ff) := by sorry

instance NotTwo: BVModEq.GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry

#check (inferInstance : SubNegMonoid (ZMod ff))

instance IsThisTrue: SubNegMonoid (ZMod ff) :=
  inferInstance
