import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma split_one {x : ℕ} : (x ≤ 1) → (x = 0 ∨ x = 1) := by omega


lemma Nat.lt_sub {a c: ℕ} : (a - c) ≤ a := by omega


lemma Nat.mux_if_then {a y x : ℕ} (h: a ≤ 1) :
  (1 - a) * x + (a * y) = if a == 0 then x else y := by
  apply split_one at h
  cases h <;> subst a <;> simp


