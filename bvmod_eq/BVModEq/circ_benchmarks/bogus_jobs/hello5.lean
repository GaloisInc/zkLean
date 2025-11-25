-- no imports
def hugeTuple : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (1,2,3,4,5,6,7,8,9)

def repeated : Nat :=
  (Nat.rec 0 (fun _ r => r + hugeTuple.1) 50000)

theorem repeated_nonneg : repeated ≥ 0 := by
  exact Nat.zero_le _
