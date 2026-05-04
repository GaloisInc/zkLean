import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Proof.And
import zkLeanExamples.Sha3.Proof.Not
import zkLeanExamples.Sha3.Proof.Xor
import zkLeanExamples.Sha3.Proof.Iota
import zkLeanExamples.Sha3.Spec

open Std Do

set_option maxHeartbeats 4000000 in
def chi.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  chi s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.chi s0_bv)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold chi
  mpure h_eq

  -- Lane 0
  mspec (not64.soundness (bv := s0_bv.lanes[1]) _); · simp; exact eqState_implies_lane_eq _ _ 1 h_eq
  mrename_i h0n; mpure h0n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[1]) (bv2 := s0_bv.lanes[2]) _ _)
  · simp; exact ⟨h0n, eqState_implies_lane_eq _ _ 2 h_eq⟩
  mrename_i h0a; mpure h0a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[0]) (bv2 := (~~~s0_bv.lanes[1]) &&& s0_bv.lanes[2]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 0 h_eq, h0a⟩
  mrename_i h0; mpure h0

  -- Lane 1
  mspec (not64.soundness (bv := s0_bv.lanes[2]) _); · simp; exact eqState_implies_lane_eq _ _ 2 h_eq
  mrename_i h1n; mpure h1n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[2]) (bv2 := s0_bv.lanes[3]) _ _)
  · simp; exact ⟨h1n, eqState_implies_lane_eq _ _ 3 h_eq⟩
  mrename_i h1a; mpure h1a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[1]) (bv2 := (~~~s0_bv.lanes[2]) &&& s0_bv.lanes[3]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 1 h_eq, h1a⟩
  mrename_i h1; mpure h1

  -- Lane 2
  mspec (not64.soundness (bv := s0_bv.lanes[3]) _); · simp; exact eqState_implies_lane_eq _ _ 3 h_eq
  mrename_i h2n; mpure h2n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[3]) (bv2 := s0_bv.lanes[4]) _ _)
  · simp; exact ⟨h2n, eqState_implies_lane_eq _ _ 4 h_eq⟩
  mrename_i h2a; mpure h2a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[2]) (bv2 := (~~~s0_bv.lanes[3]) &&& s0_bv.lanes[4]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 2 h_eq, h2a⟩
  mrename_i h2; mpure h2

  -- Lane 3
  mspec (not64.soundness (bv := s0_bv.lanes[4]) _); · simp; exact eqState_implies_lane_eq _ _ 4 h_eq
  mrename_i h3n; mpure h3n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[4]) (bv2 := s0_bv.lanes[0]) _ _)
  · simp; exact ⟨h3n, eqState_implies_lane_eq _ _ 0 h_eq⟩
  mrename_i h3a; mpure h3a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[3]) (bv2 := (~~~s0_bv.lanes[4]) &&& s0_bv.lanes[0]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 3 h_eq, h3a⟩
  mrename_i h3; mpure h3

  -- Lane 4
  mspec (not64.soundness (bv := s0_bv.lanes[0]) _); · simp; exact eqState_implies_lane_eq _ _ 0 h_eq
  mrename_i h4n; mpure h4n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[0]) (bv2 := s0_bv.lanes[1]) _ _)
  · simp; exact ⟨h4n, eqState_implies_lane_eq _ _ 1 h_eq⟩
  mrename_i h4a; mpure h4a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[4]) (bv2 := (~~~s0_bv.lanes[0]) &&& s0_bv.lanes[1]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 4 h_eq, h4a⟩
  mrename_i h4; mpure h4

  -- Lane 5
  mspec (not64.soundness (bv := s0_bv.lanes[6]) _); · simp; exact eqState_implies_lane_eq _ _ 6 h_eq
  mrename_i h5n; mpure h5n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[6]) (bv2 := s0_bv.lanes[7]) _ _)
  · simp; exact ⟨h5n, eqState_implies_lane_eq _ _ 7 h_eq⟩
  mrename_i h5a; mpure h5a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[5]) (bv2 := (~~~s0_bv.lanes[6]) &&& s0_bv.lanes[7]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 5 h_eq, h5a⟩
  mrename_i h5; mpure h5

  -- Lane 6
  mspec (not64.soundness (bv := s0_bv.lanes[7]) _); · simp; exact eqState_implies_lane_eq _ _ 7 h_eq
  mrename_i h6n; mpure h6n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[7]) (bv2 := s0_bv.lanes[8]) _ _)
  · simp; exact ⟨h6n, eqState_implies_lane_eq _ _ 8 h_eq⟩
  mrename_i h6a; mpure h6a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[6]) (bv2 := (~~~s0_bv.lanes[7]) &&& s0_bv.lanes[8]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 6 h_eq, h6a⟩
  mrename_i h6; mpure h6

  -- Lane 7
  mspec (not64.soundness (bv := s0_bv.lanes[8]) _); · simp; exact eqState_implies_lane_eq _ _ 8 h_eq
  mrename_i h7n; mpure h7n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[8]) (bv2 := s0_bv.lanes[9]) _ _)
  · simp; exact ⟨h7n, eqState_implies_lane_eq _ _ 9 h_eq⟩
  mrename_i h7a; mpure h7a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[7]) (bv2 := (~~~s0_bv.lanes[8]) &&& s0_bv.lanes[9]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 7 h_eq, h7a⟩
  mrename_i h7; mpure h7

  -- Lane 8
  mspec (not64.soundness (bv := s0_bv.lanes[9]) _); · simp; exact eqState_implies_lane_eq _ _ 9 h_eq
  mrename_i h8n; mpure h8n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[9]) (bv2 := s0_bv.lanes[5]) _ _)
  · simp; exact ⟨h8n, eqState_implies_lane_eq _ _ 5 h_eq⟩
  mrename_i h8a; mpure h8a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[8]) (bv2 := (~~~s0_bv.lanes[9]) &&& s0_bv.lanes[5]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 8 h_eq, h8a⟩
  mrename_i h8; mpure h8

  -- Lane 9
  mspec (not64.soundness (bv := s0_bv.lanes[5]) _); · simp; exact eqState_implies_lane_eq _ _ 5 h_eq
  mrename_i h9n; mpure h9n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[5]) (bv2 := s0_bv.lanes[6]) _ _)
  · simp; exact ⟨h9n, eqState_implies_lane_eq _ _ 6 h_eq⟩
  mrename_i h9a; mpure h9a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[9]) (bv2 := (~~~s0_bv.lanes[5]) &&& s0_bv.lanes[6]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 9 h_eq, h9a⟩
  mrename_i h9; mpure h9

  -- Lane 10
  mspec (not64.soundness (bv := s0_bv.lanes[11]) _); · simp; exact eqState_implies_lane_eq _ _ 11 h_eq
  mrename_i h10n; mpure h10n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[11]) (bv2 := s0_bv.lanes[12]) _ _)
  · simp; exact ⟨h10n, eqState_implies_lane_eq _ _ 12 h_eq⟩
  mrename_i h10a; mpure h10a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[10]) (bv2 := (~~~s0_bv.lanes[11]) &&& s0_bv.lanes[12]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 10 h_eq, h10a⟩
  mrename_i h10; mpure h10

  -- Lane 11
  mspec (not64.soundness (bv := s0_bv.lanes[12]) _); · simp; exact eqState_implies_lane_eq _ _ 12 h_eq
  mrename_i h11n; mpure h11n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[12]) (bv2 := s0_bv.lanes[13]) _ _)
  · simp; exact ⟨h11n, eqState_implies_lane_eq _ _ 13 h_eq⟩
  mrename_i h11a; mpure h11a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[11]) (bv2 := (~~~s0_bv.lanes[12]) &&& s0_bv.lanes[13]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 11 h_eq, h11a⟩
  mrename_i h11; mpure h11

  -- Lane 12
  mspec (not64.soundness (bv := s0_bv.lanes[13]) _); · simp; exact eqState_implies_lane_eq _ _ 13 h_eq
  mrename_i h12n; mpure h12n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[13]) (bv2 := s0_bv.lanes[14]) _ _)
  · simp; exact ⟨h12n, eqState_implies_lane_eq _ _ 14 h_eq⟩
  mrename_i h12a; mpure h12a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[12]) (bv2 := (~~~s0_bv.lanes[13]) &&& s0_bv.lanes[14]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 12 h_eq, h12a⟩
  mrename_i h12; mpure h12

  -- Lane 13
  mspec (not64.soundness (bv := s0_bv.lanes[14]) _); · simp; exact eqState_implies_lane_eq _ _ 14 h_eq
  mrename_i h13n; mpure h13n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[14]) (bv2 := s0_bv.lanes[10]) _ _)
  · simp; exact ⟨h13n, eqState_implies_lane_eq _ _ 10 h_eq⟩
  mrename_i h13a; mpure h13a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[13]) (bv2 := (~~~s0_bv.lanes[14]) &&& s0_bv.lanes[10]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 13 h_eq, h13a⟩
  mrename_i h13; mpure h13

  -- Lane 14
  mspec (not64.soundness (bv := s0_bv.lanes[10]) _); · simp; exact eqState_implies_lane_eq _ _ 10 h_eq
  mrename_i h14n; mpure h14n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[10]) (bv2 := s0_bv.lanes[11]) _ _)
  · simp; exact ⟨h14n, eqState_implies_lane_eq _ _ 11 h_eq⟩
  mrename_i h14a; mpure h14a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[14]) (bv2 := (~~~s0_bv.lanes[10]) &&& s0_bv.lanes[11]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 14 h_eq, h14a⟩
  mrename_i h14; mpure h14

  -- Lane 15
  mspec (not64.soundness (bv := s0_bv.lanes[16]) _); · simp; exact eqState_implies_lane_eq _ _ 16 h_eq
  mrename_i h15n; mpure h15n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[16]) (bv2 := s0_bv.lanes[17]) _ _)
  · simp; exact ⟨h15n, eqState_implies_lane_eq _ _ 17 h_eq⟩
  mrename_i h15a; mpure h15a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[15]) (bv2 := (~~~s0_bv.lanes[16]) &&& s0_bv.lanes[17]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 15 h_eq, h15a⟩
  mrename_i h15; mpure h15

  -- Lane 16
  mspec (not64.soundness (bv := s0_bv.lanes[17]) _); · simp; exact eqState_implies_lane_eq _ _ 17 h_eq
  mrename_i h16n; mpure h16n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[17]) (bv2 := s0_bv.lanes[18]) _ _)
  · simp; exact ⟨h16n, eqState_implies_lane_eq _ _ 18 h_eq⟩
  mrename_i h16a; mpure h16a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[16]) (bv2 := (~~~s0_bv.lanes[17]) &&& s0_bv.lanes[18]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 16 h_eq, h16a⟩
  mrename_i h16; mpure h16

  -- Lane 17
  mspec (not64.soundness (bv := s0_bv.lanes[18]) _); · simp; exact eqState_implies_lane_eq _ _ 18 h_eq
  mrename_i h17n; mpure h17n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[18]) (bv2 := s0_bv.lanes[19]) _ _)
  · simp; exact ⟨h17n, eqState_implies_lane_eq _ _ 19 h_eq⟩
  mrename_i h17a; mpure h17a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[17]) (bv2 := (~~~s0_bv.lanes[18]) &&& s0_bv.lanes[19]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 17 h_eq, h17a⟩
  mrename_i h17; mpure h17

  -- Lane 18
  mspec (not64.soundness (bv := s0_bv.lanes[19]) _); · simp; exact eqState_implies_lane_eq _ _ 19 h_eq
  mrename_i h18n; mpure h18n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[19]) (bv2 := s0_bv.lanes[15]) _ _)
  · simp; exact ⟨h18n, eqState_implies_lane_eq _ _ 15 h_eq⟩
  mrename_i h18a; mpure h18a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[18]) (bv2 := (~~~s0_bv.lanes[19]) &&& s0_bv.lanes[15]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 18 h_eq, h18a⟩
  mrename_i h18; mpure h18

  -- Lane 19
  mspec (not64.soundness (bv := s0_bv.lanes[15]) _); · simp; exact eqState_implies_lane_eq _ _ 15 h_eq
  mrename_i h19n; mpure h19n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[15]) (bv2 := s0_bv.lanes[16]) _ _)
  · simp; exact ⟨h19n, eqState_implies_lane_eq _ _ 16 h_eq⟩
  mrename_i h19a; mpure h19a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[19]) (bv2 := (~~~s0_bv.lanes[15]) &&& s0_bv.lanes[16]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 19 h_eq, h19a⟩
  mrename_i h19; mpure h19

  -- Lane 20
  mspec (not64.soundness (bv := s0_bv.lanes[21]) _); · simp; exact eqState_implies_lane_eq _ _ 21 h_eq
  mrename_i h20n; mpure h20n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[21]) (bv2 := s0_bv.lanes[22]) _ _)
  · simp; exact ⟨h20n, eqState_implies_lane_eq _ _ 22 h_eq⟩
  mrename_i h20a; mpure h20a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[20]) (bv2 := (~~~s0_bv.lanes[21]) &&& s0_bv.lanes[22]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 20 h_eq, h20a⟩
  mrename_i h20; mpure h20

  -- Lane 21
  mspec (not64.soundness (bv := s0_bv.lanes[22]) _); · simp; exact eqState_implies_lane_eq _ _ 22 h_eq
  mrename_i h21n; mpure h21n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[22]) (bv2 := s0_bv.lanes[23]) _ _)
  · simp; exact ⟨h21n, eqState_implies_lane_eq _ _ 23 h_eq⟩
  mrename_i h21a; mpure h21a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[21]) (bv2 := (~~~s0_bv.lanes[22]) &&& s0_bv.lanes[23]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 21 h_eq, h21a⟩
  mrename_i h21; mpure h21

  -- Lane 22
  mspec (not64.soundness (bv := s0_bv.lanes[23]) _); · simp; exact eqState_implies_lane_eq _ _ 23 h_eq
  mrename_i h22n; mpure h22n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[23]) (bv2 := s0_bv.lanes[24]) _ _)
  · simp; exact ⟨h22n, eqState_implies_lane_eq _ _ 24 h_eq⟩
  mrename_i h22a; mpure h22a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[22]) (bv2 := (~~~s0_bv.lanes[23]) &&& s0_bv.lanes[24]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 22 h_eq, h22a⟩
  mrename_i h22; mpure h22

  -- Lane 23
  mspec (not64.soundness (bv := s0_bv.lanes[24]) _); · simp; exact eqState_implies_lane_eq _ _ 24 h_eq
  mrename_i h23n; mpure h23n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[24]) (bv2 := s0_bv.lanes[20]) _ _)
  · simp; exact ⟨h23n, eqState_implies_lane_eq _ _ 20 h_eq⟩
  mrename_i h23a; mpure h23a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[23]) (bv2 := (~~~s0_bv.lanes[24]) &&& s0_bv.lanes[20]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 23 h_eq, h23a⟩
  mrename_i h23; mpure h23

  -- Lane 24
  mspec (not64.soundness (bv := s0_bv.lanes[20]) _); · simp; exact eqState_implies_lane_eq _ _ 20 h_eq
  mrename_i h24n; mpure h24n
  mspec (and64.soundness (bv1 := ~~~s0_bv.lanes[20]) (bv2 := s0_bv.lanes[21]) _ _)
  · simp; exact ⟨h24n, eqState_implies_lane_eq _ _ 21 h_eq⟩
  mrename_i h24a; mpure h24a
  mspec (xor64.soundness (bv1 := s0_bv.lanes[24]) (bv2 := (~~~s0_bv.lanes[20]) &&& s0_bv.lanes[21]) _ _)
  · simp; exact ⟨eqState_implies_lane_eq _ _ 24 h_eq, h24a⟩
  mrename_i h24; mpure h24

  -- Final postcondition
  mintro ∀e'
  mpure_intro
  simp only [SHA3.chi, eqF] at *
  unfold eqState
  simp only [Vector.all_iff_forall]
  intro i hi
  simp only [Vector.getElem_zip, eqF]
  interval_cases i <;> assumption
