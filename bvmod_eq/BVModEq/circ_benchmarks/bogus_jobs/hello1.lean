-- no imports
def hugeMatch (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  -- repeat hundreds or thousands of cases
  | 50000 => 50000
  | _ => 0

theorem hm_ok : hugeMatch 3 = 3 := rfl
