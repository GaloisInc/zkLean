-- no imports
-- ~2 minutes to compile

def twoMinuteJob : Nat :=
  Nat.rec
    (motive := fun _ => Nat)
    0
    (fun _ r => r + 1)
    230000   -- tune: 200k ~1.7m, 230k ~2m, 260k ~2.3m

theorem twoMinuteJob_nonneg : twoMinuteJob ≥ 0 := by
  exact Nat.zero_le _
