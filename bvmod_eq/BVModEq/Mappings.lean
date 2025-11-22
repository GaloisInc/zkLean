import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith

namespace BVModEq

def smtSignExtend (k : Nat) {w} (a : BitVec w) : BitVec (w + k) :=
  BitVec.signExtend (w + k) a

def smtZeroExtend (k : Nat) {w} (a : BitVec w) : BitVec (w + k) :=
  BitVec.zeroExtend (w + k) a

def BitVec.mod (a b : BitVec w) : BitVec w :=
  a % b

class GtTwo (n : ℕ) : Prop where
  out : 2 < n

theorem GtTwo.gt_two [G : GtTwo n] : 2 < n :=
  G.out

def bool_to_bv (n: ℕ) (b: Bool) : (BitVec n) := if b then 1#n else 0#n

def map_bv_to_f {bw} (n: ℕ) (b : BitVec bw) : ZMod n :=
  (b.toNat : ZMod n)


def map_f_to_bv_circ {ff : ℕ} (n: ℕ)  (rs1_val : ZMod ff) : BitVec n :=
  let m : ℕ := ZMod.val rs1_val
  if m <= 2^n then
    BitVec.ofNat n m
  else
    BitVec.ofNat n 0

lemma map_f_to_bv_circ_spec {ff n : ℕ} (rs1_val : ZMod ff)
  (h : ZMod.val rs1_val <= 2^n) :
  map_f_to_bv_circ n rs1_val = BitVec.ofNat n (ZMod.val rs1_val) := by
  simp [map_f_to_bv_circ]
  simp [h]

def map_f_to_bv {ff : ℕ} n (rs1_val : ZMod ff) : Option (BitVec n) :=
  let m : ℕ := ZMod.val rs1_val
  if m < 2^n then
    some (BitVec.ofNat n m)
  else
    none

set_option maxHeartbeats 2000000

lemma extract_bv_rel {b: ℕ} {x : ZMod ff} [h0: NeZero b]  :
  some (bool_to_bv b bf) = map_f_to_bv b x
  ↔ (x.val <= 1 ∧ (if bf then 1#b else 0#b) = BitVec.ofNat b x.val)
  := by
  unfold map_f_to_bv
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ m =>
      exfalso
      rw [a] at h
      unfold BitVec.ofNat at h
      unfold Fin.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % (2^b) = m + 2 := by
        rw [← a]
        apply Nat.mod_eq_of_lt
        apply hx
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
        have h1 : 1 % 2 ^ b = 1 := by
          apply Nat.mod_eq_of_lt (Nat.one_lt_two_pow h0.out)
        rw [h1] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  apply Nat.lt_of_le_of_lt
  apply h
  apply Nat.one_lt_two_pow h0.out


lemma ZMod.eq_if_val [NeZero ff]  (a b : ZMod ff) :
  (a = b) ↔ (a.val = b.val) := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h

lemma BitVec_ofNat_eq_iff (n : ℕ) {x y : ℕ} (hx : x < 2^n) (hy : y < 2^n) :
  (x = y) ↔ (BitVec.ofNat n x = BitVec.ofNat n y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^n = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx




lemma square_eq_one_zero {n :ℕ} [p: Fact (Nat.Prime n)] {x : ZMod n} (w:ℕ) [ne: NeZero w]  : x * x = x <-> ( x.val <= 1)  /\ (( BitVec.ofNat w x.val = 0#w  ) \/ ( BitVec.ofNat w x.val = 1#w) ):= by
  constructor
  intro h
  --rw [BVModEq.ZMod.eq_if_val] at h
  --rw [ZMod.val_mul] at h
  have h0 : x * (x - 1) = 0 := by
        rw [mul_sub, mul_one, <- pow_two]
        rw [<- pow_two] at h
        rw [h]
        simp
  --haveI := (inferInstance : IsDomain (ZMod n))
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h0 with h | h
  rw [h]
  simp
  rw [sub_eq_zero] at h
  rw [h]
  rw [ZMod.val_one]
  simp
  intro h
  rw [ZMod.eq_if_val]
  rw [ZMod.val_mul]
  rcases h with ⟨h1, h2⟩
  rw [Nat.mod_eq_of_lt]
  rw [BitVec_ofNat_eq_iff w]
  rw [BitVec.ofNat_mul]
  rcases h2 with x1 | x2
  rw [x1]
  simp
  rw [x2]
  simp
  apply Nat.lt_of_le_of_lt
  apply Nat.mul_le_mul
  apply h1
  apply h1
  simp
  apply ne.out
  apply Nat.lt_of_le_of_lt
  apply h1
  simp
  apply ne.out
  apply Nat.lt_of_le_of_lt
  apply Nat.mul_le_mul
  apply h1
  apply h1
  simp
  apply p.out.two_le










      -- since n is
