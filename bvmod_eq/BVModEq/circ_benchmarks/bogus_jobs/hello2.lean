-- no imports
def bigRec : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ r => r + 1) 70000

theorem bigRec_pos : bigRec ≥ 0 := by
  exact Nat.zero_le _
