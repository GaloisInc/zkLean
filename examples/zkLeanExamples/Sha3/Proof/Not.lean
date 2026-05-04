import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.Not
import zkLeanExamples.Sha3.Spec

open Std Do

def not64.soundness (felt : ZKExpr f) :
  ⦃ λ _e => ⌜eqF felt bv⌝ ⦄
  not64 felt
  ⦃ ⇓? s1 _e => ⌜eqF s1 (~~~bv)⌝ ⦄
  := by

  sorry
