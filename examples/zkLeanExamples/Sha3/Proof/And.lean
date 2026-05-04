import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.Not
import zkLeanExamples.Sha3.Spec

open Std Do

def and64.soundness (felt1 felt2 : ZKExpr f) :
  ⦃ λ _e => ⌜eqF felt1 bv1 && eqF felt2 bv2⌝ ⦄
  and64 felt1 felt2
  ⦃ ⇓? o _e => ⌜eqF o (bv1 &&& bv2)⌝ ⦄
  := by

  sorry
