import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith

import BVModEq.Lemmas

namespace BVModEq

/-- SMT-style sign extension. -/
def smtSignExtend (k : Nat) {w : Nat} (a : BitVec w) : BitVec (w + k) :=
  BitVec.signExtend (w + k) a

/-- Backwards-compatible alias for sign extension. -/
def zeroSignExtend (k : Nat) {w : Nat} (a : BitVec w) : BitVec (w + k) :=
  BitVec.signExtend (w + k) a

/-- SMT-style zero extension. -/
def smtZeroExtend (k : Nat) {w : Nat} (a : BitVec w) : BitVec (w + k) :=
  BitVec.zeroExtend (w + k) a

/-- Bitvector unsigned remainder wrapper used by generated terms. -/
def BitVec.mod (a b : BitVec w) : BitVec w :=
  a % b

/-- Encode a Boolean as a bitvector. -/
def bool_to_bv (n : ℕ) (b : Bool) : BitVec n :=
  if b then 1#n else 0#n

/-- Interpret a bitvector as a field element through its natural representative. -/
def map_bv_to_f {bw : Nat} (n : ℕ) (b : BitVec bw) : ZMod n :=
  (b.toNat : ZMod n)

/-- CirC-style field-to-bitvector map: out-of-range values map to zero. -/
def map_f_to_bv_circ {ff : ℕ} (n : ℕ) (rs1_val : ZMod ff) : BitVec n :=
  let m : ℕ := ZMod.val rs1_val
  if m ≤ 2 ^ n then
    BitVec.ofNat n m
  else
    BitVec.ofNat n 0

/-- Specification of `map_f_to_bv_circ` on in-range values. -/
lemma map_f_to_bv_circ_spec {ff n : ℕ} (rs1_val : ZMod ff)
    (h : ZMod.val rs1_val ≤ 2 ^ n) :
    map_f_to_bv_circ n rs1_val = BitVec.ofNat n (ZMod.val rs1_val) := by
  simp [map_f_to_bv_circ, h]

/-- Partial field-to-bitvector map: returns `none` when the representative is too large. -/
def map_f_to_bv {ff : ℕ} (n : Nat) (rs1_val : ZMod ff) : Option (BitVec n) :=
  let m : ℕ := ZMod.val rs1_val
  if m < 2 ^ n then
    some (BitVec.ofNat n m)
  else
    none

set_option maxHeartbeats 2000000

/--
If a field representative is bounded by `b`, then every sufficiently wide
bitvector embedding preserves the corresponding order comparison.
-/
lemma extract_bv_leq {ff : ℕ} {b : ℕ} {x : ZMod ff} :
    x.val ≤ b →
      ∀ w : ℕ, 2 ^ w > b →
        BitVec.ofNat w x.val ≤ BitVec.ofNat w b := by
  intro hxb w hw
  unfold BitVec.ofNat
  simp
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  · exact hxb
  · exact hw
  · exact lt_of_le_of_lt hxb hw

/--
Relate successful Boolean field-to-bitvector extraction to the representative
being Boolean-valued and preserved at wider bitwidths.
-/
lemma extract_bv_rel {b : ℕ} {x : ZMod ff} [h0 : NeZero b] :
    some (bool_to_bv b bf) = map_f_to_bv b x →
      x.val ≤ 1 ∧
        ∀ w : Nat, w > b →
          (if bf then 1#w else 0#w) = BitVec.ofNat w x.val := by
  unfold map_f_to_bv
  unfold bool_to_bv
  dsimp
  simp
  intro h h2
  constructor
  · cases hx : x.val with
    | zero =>
        decide
    | succ n =>
        cases n with
        | zero =>
            decide
        | succ m =>
            exfalso
            rw [hx] at h2

            have h' := congrArg BitVec.toNat h2
            simp [BitVec.toNat_ofNat] at h'

            have mod_eq : (m + 2) % (2 ^ b) = m + 2 := by
              rw [← hx]
              apply Nat.mod_eq_of_lt
              exact h

            rw [← h'] at mod_eq

            cases hb : bf with
            | true =>
                rw [hb] at mod_eq
                simp at mod_eq
                have h1 : 1 % 2 ^ b = 1 := by
                  apply Nat.mod_eq_of_lt
                  exact Nat.one_lt_two_pow h0.out
                rw [h1] at mod_eq
                simp at mod_eq
            | false =>
                rw [hb] at mod_eq
                simp at mod_eq

  · intro w hw
    cases bf
    · simp
      simp at h2
      have hx0 : x.val = 0 := by
        have ht := congrArg BitVec.toNat h2
        have hmod : x.val % 2 ^ b = 0 := by
          simpa [BitVec.toNat_ofNat] using ht.symm
        rw [Nat.mod_eq_of_lt] at hmod
        · exact hmod
        · exact h
      simp [hx0]

    · simp
      have hx1 : x.val = 1 := by
        have ht := congrArg BitVec.toNat h2
        have hmod : x.val % 2 ^ b = 1 := by
          simp [BitVec.toNat_ofNat] at ht
          rw [Nat.mod_eq_of_lt] at ht
          · exact ht.symm
          · exact Nat.one_lt_two_pow h0.out
        rw [Nat.mod_eq_of_lt] at hmod
        · exact hmod
        · exact h
      simp [hx1]

/--
Over a prime field, the equation `x * x = x` characterizes Boolean-valued
field elements, exposed through a bitvector representative.
-/
lemma square_eq_one_zero {n : ℕ} [p : Fact (Nat.Prime n)] {x : ZMod n}
    (w : ℕ) [ne : NeZero w] :
    x * x = x ↔
      x.val <= 1 ∧
        (BitVec.ofNat w x.val = 0#w ∨ BitVec.ofNat w x.val = 1#w) := by
  constructor
  · intro h
    have h0 : x * (x - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two]
      rw [← pow_two] at h
      rw [h]
      simp
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h0 with h | h
    · rw [h]
      simp
    · rw [sub_eq_zero] at h
      rw [h]
      rw [ZMod.val_one]
      simp
  · intro h
    rw [ZMod.eq_if_val]
    rw [ZMod.val_mul]
    rcases h with ⟨h1, h2⟩
    rw [Nat.mod_eq_of_lt]
    rw [BitVec_ofNat_eq_iff w]
    rw [BitVec.ofNat_mul]
    · rcases h2 with x1 | x2
      · rw [x1]
        simp
      · rw [x2]
        simp
    · apply Nat.lt_of_le_of_lt
      · apply Nat.mul_le_mul
        · exact h1
        · exact h1
      · simp
        exact ne.out
    · apply Nat.lt_of_le_of_lt
      · exact h1
      · simp
        exact ne.out
    · apply Nat.lt_of_le_of_lt
      · apply Nat.mul_le_mul
        · exact h1
        · exact h1
      · simp
        exact p.out.two_le


end BVModEq
