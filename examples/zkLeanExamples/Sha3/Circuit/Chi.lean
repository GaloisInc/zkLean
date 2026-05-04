import zkLean
import zkLeanExamples.Sha3.Circuit.And
import zkLeanExamples.Sha3.Circuit.Not
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Circuit.Xor

def chi (s: State) : ZKBuilder f State := do
  let lanes := #v[
    ← xor64 s.lanes[0] (← and64 (← not64 s.lanes[1]) s.lanes[2]),
    ← xor64 s.lanes[1] (← and64 (← not64 s.lanes[2]) s.lanes[3]),
    ← xor64 s.lanes[2] (← and64 (← not64 s.lanes[3]) s.lanes[4]),
    ← xor64 s.lanes[3] (← and64 (← not64 s.lanes[4]) s.lanes[0]),
    ← xor64 s.lanes[4] (← and64 (← not64 s.lanes[0]) s.lanes[1]),
    ← xor64 s.lanes[5] (← and64 (← not64 s.lanes[6]) s.lanes[7]),
    ← xor64 s.lanes[6] (← and64 (← not64 s.lanes[7]) s.lanes[8]),
    ← xor64 s.lanes[7] (← and64 (← not64 s.lanes[8]) s.lanes[9]),
    ← xor64 s.lanes[8] (← and64 (← not64 s.lanes[9]) s.lanes[5]),
    ← xor64 s.lanes[9] (← and64 (← not64 s.lanes[5]) s.lanes[6]),
    ← xor64 s.lanes[10] (← and64 (← not64 s.lanes[11]) s.lanes[12]),
    ← xor64 s.lanes[11] (← and64 (← not64 s.lanes[12]) s.lanes[13]),
    ← xor64 s.lanes[12] (← and64 (← not64 s.lanes[13]) s.lanes[14]),
    ← xor64 s.lanes[13] (← and64 (← not64 s.lanes[14]) s.lanes[10]),
    ← xor64 s.lanes[14] (← and64 (← not64 s.lanes[10]) s.lanes[11]),
    ← xor64 s.lanes[15] (← and64 (← not64 s.lanes[16]) s.lanes[17]),
    ← xor64 s.lanes[16] (← and64 (← not64 s.lanes[17]) s.lanes[18]),
    ← xor64 s.lanes[17] (← and64 (← not64 s.lanes[18]) s.lanes[19]),
    ← xor64 s.lanes[18] (← and64 (← not64 s.lanes[19]) s.lanes[15]),
    ← xor64 s.lanes[19] (← and64 (← not64 s.lanes[15]) s.lanes[16]),
    ← xor64 s.lanes[20] (← and64 (← not64 s.lanes[21]) s.lanes[22]),
    ← xor64 s.lanes[21] (← and64 (← not64 s.lanes[22]) s.lanes[23]),
    ← xor64 s.lanes[22] (← and64 (← not64 s.lanes[23]) s.lanes[24]),
    ← xor64 s.lanes[23] (← and64 (← not64 s.lanes[24]) s.lanes[20]),
    ← xor64 s.lanes[24] (← and64 (← not64 s.lanes[20]) s.lanes[21])
  ]
  pure { lanes := lanes }
