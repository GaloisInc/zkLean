import zkLean
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Circuit.Shift
import zkLeanExamples.Sha3.Circuit.Xor


def theta (s : State) : ZKBuilder f State := do
  let c ← Vector.ofFnM fun (x : Fin 5) => do
    xor64 (← xor64 (← xor64 (← xor64 (s.get x 0) (s.get x 1)) (s.get x 2)) (s.get x 3)) (s.get x 4)
  let d ← Vector.ofFnM fun (x : Fin 5) => do
    xor64 (c.get ⟨(x.val + 4) % 5, by omega⟩) (← rotateLeft64 (c.get ⟨(x.val + 1) % 5, by omega⟩) 1)
  let lanes ← Vector.ofFnM fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    xor64 (s.get ⟨x, by omega⟩ ⟨y, by omega⟩) d[x]
  pure { lanes := lanes }
