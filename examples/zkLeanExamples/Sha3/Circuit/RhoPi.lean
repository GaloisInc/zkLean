import zkLean
import zkLeanExamples.Sha3.Circuit.Shift
import zkLeanExamples.Sha3.Circuit.State

def rho_pi (s: State) : ZKBuilder f State := do
  let lanes := #v[
    ← rotateLeft64 s.lanes[0] 0,
    ← rotateLeft64 s.lanes[6] 44,
    ← rotateLeft64 s.lanes[12] 43,
    ← rotateLeft64 s.lanes[18] 21,
    ← rotateLeft64 s.lanes[24] 14,
    ← rotateLeft64 s.lanes[3] 28,
    ← rotateLeft64 s.lanes[9] 20,
    ← rotateLeft64 s.lanes[10] 3,
    ← rotateLeft64 s.lanes[16] 45,
    ← rotateLeft64 s.lanes[22] 61,
    ← rotateLeft64 s.lanes[1] 1,
    ← rotateLeft64 s.lanes[7] 6,
    ← rotateLeft64 s.lanes[13] 25,
    ← rotateLeft64 s.lanes[19] 8,
    ← rotateLeft64 s.lanes[20] 18,
    ← rotateLeft64 s.lanes[4] 27,
    ← rotateLeft64 s.lanes[5] 36,
    ← rotateLeft64 s.lanes[11] 10,
    ← rotateLeft64 s.lanes[17] 15,
    ← rotateLeft64 s.lanes[23] 56,
    ← rotateLeft64 s.lanes[2] 62,
    ← rotateLeft64 s.lanes[8] 55,
    ← rotateLeft64 s.lanes[14] 39,
    ← rotateLeft64 s.lanes[15] 41,
    ← rotateLeft64 s.lanes[21] 2
  ]
  pure { lanes := lanes }
