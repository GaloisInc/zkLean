import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Proof.Iota
import zkLeanExamples.Sha3.Proof.Shift
import zkLeanExamples.Sha3.Spec

open Std Do

-- Helper: eqState holds when we construct new states with all lanes equal via eqF
theorem eqState_mk_lanes (lanes : Vector (ZKExpr f) 25) (lanesBV : Vector (BitVec 64) 25)
    (h : ∀ i : Fin 25, eqF lanes[i] lanesBV[i]) :
    eqState { lanes := lanes } { lanes := lanesBV } := by
  unfold eqState
  simp
  intro i hi
  exact h ⟨i, hi⟩

set_option maxHeartbeats 400000 in
def rho_pi.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  rho_pi s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.rho_pi s0_bv)⌝ ⦄
  := by
  mintro h ∀e
  unfold rho_pi
  mpure h

  -- Lane 0: s0.lanes[0] rotateLeft 0
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[0]) (bv2 := 0) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 0 h)
  · decide
  mrename_i h0
  mpure h0

  -- Lane 1: s0.lanes[6] rotateLeft 44
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[6]) (bv2 := 44) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 6 h)
  · decide
  mrename_i h1
  mpure h1

  -- Lane 2: s0.lanes[12] rotateLeft 43
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[12]) (bv2 := 43) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 12 h)
  · decide
  mrename_i h2
  mpure h2

  -- Lane 3: s0.lanes[18] rotateLeft 21
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[18]) (bv2 := 21) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 18 h)
  · decide
  mrename_i h3
  mpure h3

  -- Lane 4: s0.lanes[24] rotateLeft 14
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[24]) (bv2 := 14) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 24 h)
  · decide
  mrename_i h4
  mpure h4

  -- Lane 5: s0.lanes[3] rotateLeft 28
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[3]) (bv2 := 28) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 3 h)
  · decide
  mrename_i h5
  mpure h5

  -- Lane 6: s0.lanes[9] rotateLeft 20
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[9]) (bv2 := 20) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 9 h)
  · decide
  mrename_i h6
  mpure h6

  -- Lane 7: s0.lanes[10] rotateLeft 3
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[10]) (bv2 := 3) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 10 h)
  · decide
  mrename_i h7
  mpure h7

  -- Lane 8: s0.lanes[16] rotateLeft 45
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[16]) (bv2 := 45) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 16 h)
  · decide
  mrename_i h8
  mpure h8

  -- Lane 9: s0.lanes[22] rotateLeft 61
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[22]) (bv2 := 61) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 22 h)
  · decide
  mrename_i h9
  mpure h9

  -- Lane 10: s0.lanes[1] rotateLeft 1
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[1]) (bv2 := 1) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 1 h)
  · decide
  mrename_i h10
  mpure h10

  -- Lane 11: s0.lanes[7] rotateLeft 6
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[7]) (bv2 := 6) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 7 h)
  · decide
  mrename_i h11
  mpure h11

  -- Lane 12: s0.lanes[13] rotateLeft 25
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[13]) (bv2 := 25) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 13 h)
  · decide
  mrename_i h12
  mpure h12

  -- Lane 13: s0.lanes[19] rotateLeft 8
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[19]) (bv2 := 8) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 19 h)
  · decide
  mrename_i h13
  mpure h13

  -- Lane 14: s0.lanes[20] rotateLeft 18
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[20]) (bv2 := 18) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 20 h)
  · decide
  mrename_i h14
  mpure h14

  -- Lane 15: s0.lanes[4] rotateLeft 27
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[4]) (bv2 := 27) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 4 h)
  · decide
  mrename_i h15
  mpure h15

  -- Lane 16: s0.lanes[5] rotateLeft 36
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[5]) (bv2 := 36) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 5 h)
  · decide
  mrename_i h16
  mpure h16

  -- Lane 17: s0.lanes[11] rotateLeft 10
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[11]) (bv2 := 10) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 11 h)
  · decide
  mrename_i h17
  mpure h17

  -- Lane 18: s0.lanes[17] rotateLeft 15
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[17]) (bv2 := 15) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 17 h)
  · decide
  mrename_i h18
  mpure h18

  -- Lane 19: s0.lanes[23] rotateLeft 56
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[23]) (bv2 := 56) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 23 h)
  · decide
  mrename_i h19
  mpure h19

  -- Lane 20: s0.lanes[2] rotateLeft 62
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[2]) (bv2 := 62) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 2 h)
  · decide
  mrename_i h20
  mpure h20

  -- Lane 21: s0.lanes[8] rotateLeft 55
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[8]) (bv2 := 55) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 8 h)
  · decide
  mrename_i h21
  mpure h21

  -- Lane 22: s0.lanes[14] rotateLeft 39
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[14]) (bv2 := 39) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 14 h)
  · decide
  mrename_i h22
  mpure h22

  -- Lane 23: s0.lanes[15] rotateLeft 41
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[15]) (bv2 := 41) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 15 h)
  · decide
  mrename_i h23
  mpure h23

  -- Lane 24: s0.lanes[21] rotateLeft 2
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[21]) (bv2 := 2) _ _)
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 21 h)
  · decide
  mrename_i h24
  mpure h24

  -- Final postcondition: prove eqState for the constructed state
  -- All h0..h24 hypotheses are now preserved and available
  mintro ∀e'
  mpure_intro
  simp only [SHA3.rho_pi, eqF] at *
  unfold eqState
  simp only [Vector.all_iff_forall]
  intro i hi
  simp only [Vector.getElem_zip, eqF]
  interval_cases i <;> assumption
