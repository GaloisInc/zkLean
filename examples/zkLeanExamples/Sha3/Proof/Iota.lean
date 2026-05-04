import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Circuit.Iota
import zkLeanExamples.Sha3.Proof.Xor
import zkLeanExamples.Sha3.Spec

open Std Do

-- Helper: extract lane equality from eqState
theorem eqState_implies_lane_eq (s : State) (sBV : SHA3.State) (i : Fin 25) :
    eqState s sBV → eqF s.lanes[i] sBV.lanes[i] := by
  intro h
  unfold eqState at h
  simp_rw [Vector.all_iff_forall] at h
  simp at h
  fin_cases i
  <;> (simp; apply h)

-- Helper: circuit roundConstants equals spec roundConstants
-- The circuit and spec round constants are the same values
theorem roundConstants_eqF (i : Fin 24) :
    eqF (roundConstants[i]) (SHA3.roundConstants[i]) := by
  simp [eqF,roundConstants,SHA3.roundConstants]
  fin_cases i
  <;> (simp; decide)

-- Helper: eqState is preserved when updating the same lane with equal values
theorem eqState_set
    (s : State) (sBV : SHA3.State)
    (v : ZKExpr f) (vBV : BitVec 64)
    (h_state : eqState s sBV = true)
    (h_val : eqF v vBV = true)
    (i : Fin 25)
    : eqState { lanes := s.lanes.set i v } { lanes := sBV.lanes.set i vBV } := by
  unfold eqState at *
  simp at h_state
  simp
  intro j hj
  rw [Vector.getElem_set] -- [Vector.getElem_set] -- [Vector.get_set]


  by_cases hij: (i = j)
  simp [hij]
  exact h_val

  simp [hij]
  simp [h_state]

def iota.soundness (s0 : State) (round : Fin 24) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  iota s0 round
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.iota s0_bv round)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold iota SHA3.iota SHA3.State.set SHA3.State.get
  -- The circuit does: xor64 s0.lanes[0] roundConstants[round] >>= pure ∘ set
  -- The spec does: set lane 0 to (lane 0 ^^^ roundConstants[round])
  mpure h_eq
  mspec (xor64.soundness (bv1 := s0_bv.lanes[0]) (bv2 := SHA3.roundConstants[round.val]) s0.lanes[0] roundConstants[round.val])
  -- Goal 1: Prove precondition for xor64.soundness
  · simp
    constructor
    · apply (eqState_implies_lane_eq s0 s0_bv 0)
      exact h_eq
    · apply (roundConstants_eqF round)
  -- Goal 2: Prove postcondition (eqState for updated state)
  · mrename_i h
    rename_i r

    mintro ∀e'
    mpure h
    whnf
    simp
    whnf
    simp at h
    apply (eqState_set _ _ _ _ h_eq h 0)
