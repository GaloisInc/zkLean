import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma split_one {x : ℕ} : (x ≤ 1) → (x = 0 ∨ x = 1) := by omega


lemma Nat.lt_sub {a c: ℕ} : (a - c) ≤ a := by omega


lemma Nat.mux_if_then {a y x : ℕ} (h: a ≤ 1) :
  (1 - a) * x + (a * y) = if a == 0 then x else y := by
  apply split_one at h
  cases h <;> subst a <;> simp


lemma ZMod.val_sub_mod {ff: ℕ} [h: NeZero ff] {y x : ZMod ff}  (h : x.val ≤ y.val)
  : (y - x).val = (y.val - x.val) := by
  have hx:= ZMod.val_lt x
  have hy := ZMod.val_lt y
  rw [ZMod.val_sub]
  apply h
