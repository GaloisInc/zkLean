import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace BVModEq

/-- A typeclass wrapper for moduli known to be greater than two. -/
class GtTwo (n : ℕ) : Prop where
  out : 2 < n

/-- Extract the proof carried by `GtTwo`. -/
theorem GtTwo.gt_two [G : GtTwo n] : 2 < n :=
  G.out

/-- A natural number bounded by `1` is either `0` or `1`. -/
lemma split_one {x : ℕ} : x ≤ 1 → x = 0 ∨ x = 1 := by
  omega

/-- Natural subtraction is bounded above by the minuend. -/
lemma Nat.lt_sub {a c : ℕ} : a - c ≤ a := by
  omega

/-- Natural subtraction is always nonnegative. -/
lemma Nat.gt_sub {a c : ℕ} : a - c ≥ 0 := by
  omega

/-- Commute a numeral multiplier on the left. -/
lemma Nat.mul_comm_ofNat (a n : Nat) :
    (OfNat.ofNat n) * a = a * (OfNat.ofNat n : Nat) := by
  rw [Nat.mul_comm]

/-- Commute a natural-number multiplier on the left. -/
lemma mul_comm_num_left (n t : ℕ) :
    (n : ℕ) * t = t * (n : ℕ) := by
  simpa using Nat.mul_comm (n : ℕ) t

/-- Convert the arithmetic encoding of a Boolean mux into an `if`. -/
lemma Nat.mux_if_then {a x y : ℕ} (h : a ≤ 1) :
    (1 - a) * x + a * y = if a == 0 then x else y := by
  apply split_one at h
  cases h <;> subst a <;> simp

/-- `BitVec.toNat` is bounded above by `2^bw - 1`. -/
lemma BitVec.toNatLT {bw : Nat} {a : BitVec bw} :
    a.toNat ≤ 2 ^ bw - 1 := by
  have h : a.toNat < 2 ^ bw := a.toFin.isLt
  exact Nat.le_pred_of_lt h

/-- `BitVec.toNat` is nonnegative. -/
lemma BitVec.toNatGT {bw : Nat} {a : BitVec bw} :
    0 ≤ a.toNat := by
  exact Nat.zero_le a.toNat

/-- Rewrite `-a + b` as subtraction. -/
lemma neg_add_to_sub {α : Type*} [AddCommGroup α] (a b : α) :
    -a + b = b - a := by
  rw [sub_eq_add_neg]
  rw [add_comm (-a) b]

/-- Normalize a nested subtraction inside addition over `ZMod`. -/
lemma neg_param (x y z : ZMod p) :
    x + (-y - z) = (x - y) - z := by
  ring_nf

/-- Reassociate subtraction and addition. -/
lemma sub_add_right_recursive {α : Type*} [AddCommGroup α] (a b c : α) :
    a - b + c = (a + c) - b := by
  rw [sub_eq_add_neg, add_assoc]
  rw [sub_eq_add_neg]
  rw [add_comm (-b) c]
  rw [add_assoc]

/-- Reassociate a parenthesized subtraction on the left over `ZMod`. -/
lemma sub_add_right_recursive_paren_l (a b c : ZMod p) :
    (a - b) + c = a + c - b := by
  ring

/-- Reassociate a parenthesized subtraction on the right over `ZMod`. -/
lemma sub_add_right_recursive_paren_r (a b c : ZMod p) :
    c + (a - b) = a + c - b := by
  ring

/-- Duplicate an equality hypothesis when a tactic needs two copies. -/
lemma duplicate {b a : ZMod f} :
    b = a ↔ b = a ∧ b = a := by
  simp

/-- Duplicate a natural-number inequality hypothesis when a tactic needs two copies. -/
lemma duplicate_leq {b a : Nat} :
    b ≤ a ↔ b ≤ a ∧ b ≤ a := by
  simp

/-- Values of `ZMod n` are bounded above by `n`. -/
lemma ZMod.toNatLT {n : Nat} {a : ZMod n} (h : n > 0) :
    a.val ≤ n := by
  haveI : NeZero n := ⟨Nat.ne_of_gt h⟩
  have hlt : a.val < n := ZMod.val_lt a
  have hlt' : a.val < n.succ := lt_trans hlt (Nat.lt_succ_self n)
  exact Nat.le_of_lt_succ hlt'

/-- Values of `ZMod n` are nonnegative. -/
lemma ZMod.toNatGT {n : Nat} {a : ZMod n} (_h : n > 0) :
    a.val ≥ 0 := by
  exact Nat.zero_le a.val

/-- A modulo result is bounded by the predecessor of a positive modulus. -/
lemma mod_le_pred {m k : ℕ} (hm : m > 0) :
    k % m ≤ m - 1 := by
  have hlt : k % m < m := Nat.mod_lt k hm
  exact Nat.le_pred_of_lt hlt

/-- Equality in `ZMod` is equivalent to equality of representatives. -/
lemma ZMod.eq_if_val [NeZero ff] (a b : ZMod ff) :
    (a = b) ↔ a.val = b.val := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    apply ZMod.val_injective at h
    exact h

/-- Equality of bounded naturals is equivalent to equality after `BitVec.ofNat`. -/
lemma BitVec_ofNat_eq_iff (n : ℕ) {x y : ℕ}
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    (x = y) ↔ BitVec.ofNat n x = BitVec.ofNat n y := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at h'
    rw [Nat.mod_eq_of_lt hx] at h'
    rw [Nat.mod_eq_of_lt hy] at h'
    exact h'

/-- Move a natural modulo operation through `BitVec.ofNat` under range assumptions. -/
lemma BitVec.ofNat_mod_move {f n w : Nat} [hfne : NeZero f] [NeZero w]
    (hn : n < 2 ^ w) (hf : f < 2 ^ w) :
    BitVec.ofNat w (n % f) = BitVec.ofNat w n % BitVec.ofNat w f := by
  unfold BitVec.ofNat
  apply congrArg
  simp_all
  apply Fin.eq_of_val_eq
  simp_all
  rw [Nat.mod_eq_of_lt]
  nth_rewrite 3 [Nat.mod_eq_of_lt]
  nth_rewrite 3 [Nat.mod_eq_of_lt]
  simp
  exact hf
  exact hn
  have hmod : n % f < f := by
    apply Nat.mod_lt
    exact Nat.pos_of_ne_zero hfne.out
  simp
  exact lt_trans hmod hf

/-- Bound a `ZMod.val` after embedding it into a sufficiently wide bitvector. -/
lemma ZMod.val_le_BV {n : ℕ} [k : NeZero n] (a : ZMod n) (w : ℕ)
    (h : n < 2 ^ w) :
    BitVec.ofNat w a.val ≤ BitVec.ofNat w n := by
  unfold BitVec.ofNat
  simp
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  · apply ZMod.toNatLT
    exact Nat.pos_of_ne_zero k.out
  · exact h
  · exact lt_trans (ZMod.val_lt a) h

/-- Strict representative formula for subtraction in `ZMod`. -/
lemma ZMod.val_sub_strict {f : Nat} [NeZero f] (x y : ZMod f) :
    (x - y).val = (x.val + f - y.val) % f := by
  by_cases h : y.val ≤ x.val
  · rw [ZMod.val_sub]
    have h1 : (x.val - y.val) % f = x.val - y.val := by
      rw [Nat.mod_eq_of_lt]
      apply Nat.lt_of_le_of_lt
      apply Nat.lt_sub
      apply ZMod.val_lt
    have h2 : (x.val - y.val) % f = (x.val + f - y.val) % f := by
      rw [← Nat.add_comm]
      rw [← Nat.add_mod_right]
      rw [← Nat.add_comm]
      rw [Nat.add_sub_assoc]
      exact h
    rw [← h1]
    rw [← h2]
    exact h
  · have hxy : x - y = x + (-y) := by ring_nf
    rw [hxy]
    rw [ZMod.val_add]
    rw [ZMod.neg_val']
    simp
    rw [Nat.add_sub_assoc]
    apply ZMod.val_le

/-- Rephrase negation as subtraction from zero. -/
lemma ZMod.val_neg_sub_zero {p : Nat} {x : ZMod p} :
    (-x : ZMod p) = 0 - x := by
  simp

end BVModEq
