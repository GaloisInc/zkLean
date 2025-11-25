-- no imports
def huge (n : Nat) : Nat :=
  match n with
  | 0     => 0
  | n+1   => huge n + 1

-- force compilation of a huge recursive unfolding
def bigValue : Nat :=
  huge 40000   -- adjust to increase compile time

theorem bigValue_pos : bigValue ≥ 0 := by
  -- trivial, but Lean must compile bigValue first
  exact Nat.zero_le _
