import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Vector.Basic

/-- Half of a natural number, rounded down -/
def half_down (n : Nat) := n / 2
/-- Half of a natural number, rounded up -/
def half_up (n : Nat) := if n % 2 == 0 then n / 2 else n / 2 + 1

theorem half_up_of_succ_odd : n % 2 = 1 → half_up (n + 1) = half_up n := by
  repeat rw [half_up]
  intro H
  simp [H]
  rw [Nat.add_mod_eq_add_mod_right (b := 1)]
  simp
  omega
  exact H

theorem half_up_of_succ_even : n % 2 = 0 → half_up (n + 1) = half_up n + 1 := by
  repeat rw [half_up]
  intro H
  simp [H]
  rw [Nat.add_mod_eq_add_mod_right (b := 0)]
  simp
  omega
  exact H

theorem half_up_of_succ_succ (n : Nat) : half_up (n + 2) = half_up n + 1 := by
  by_cases H1 : n % 2 = 0
  rw [half_up_of_succ_odd, half_up_of_succ_even]
  omega
  omega
  rw [half_up_of_succ_even, half_up_of_succ_odd]
  omega
  omega

theorem half_down_of_succ_odd : n % 2 = 1 → half_down (n + 1) = half_down n + 1 := by
  repeat rw [half_down]
  omega

theorem half_down_of_succ_even : n % 2 = 0 → half_down (n + 1) = half_down n := by
  repeat rw [half_down]
  omega

theorem half_down_of_succ_succ (n : Nat) : half_down (n + 2) = half_down n + 1 := by
  by_cases H1 : n % 2 = 0
  rw [half_down_of_succ_odd, half_down_of_succ_even]
  omega
  omega
  rw [half_down_of_succ_even, half_down_of_succ_odd]
  omega
  omega

/-- Returns two vectors with the 0-indexed even elements on the left, the
0-indexed odd elements on the right. -/
def deinterleave (input : Vector f n) : (Vector f (half_up n) × Vector f (half_down n)) :=
  match n, input with
  | 0, Vector.mk (Array.mk []) s => (#v[], #v[])
  | 1, Vector.mk (Array.mk [a]) s => by
    rw [half_up, half_down]
    simp
    exact (#v[a], #v[])
  | .succ (.succ n), v => by
    let (d1, d2) := deinterleave v.tail.tail
    simp [half_up_of_succ_succ, half_down_of_succ_succ]
    repeat rw [Nat.add_comm (m := 1)]
    exact (#v[v[0]] ++ d1, #v[v[1]] ++ d2)

/-- Interleaves two vectors starting with the first element of the first vector. -/
def interleave (a b : Vector f n) : Vector f (n + n) :=
  match n with
  | 0 => #v[]
  | .succ n => by
    have H : n.succ + n.succ = 2 + (n + n) := by omega
    rw [H]
    exact (#v[a[0]] ++ #v[b[0]] ++ interleave a.tail b.tail)
