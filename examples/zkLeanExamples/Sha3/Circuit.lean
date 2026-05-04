import zkLeanExamples.Sha3.Circuit.Chi
import zkLeanExamples.Sha3.Circuit.Iota
import zkLeanExamples.Sha3.Circuit.RhoPi
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Circuit.Theta

def keccakRound (s : State) (round : Fin 24) : ZKBuilder f State := do
  theta s >>= rho_pi >>= chi >>= (iota · round)

/-- Full Keccak-f[1600] permutation (24 rounds) --/
def keccakF (s : State) : ZKBuilder f State :=
  (Array.finRange 24).foldlM (fun acc i => keccakRound acc i) s
