import BVModEq.TranslateAll

abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry 
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry 
set_option maxHeartbeats  20000000000000000000
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
variable (fresh_pf0_sum_bit0 : FF0)
variable (f : BitVec 1)
variable (e : BitVec 1)
variable (d : BitVec 1)
variable (c : BitVec 1)
variable (b : BitVec 1)
variable (a : BitVec 1)
variable (fresh_pf5_sum_bit5 : FF0)
variable (fresh_pf4_sum_bit4 : FF0)
variable (fresh_pf3_sum_bit3 : FF0)
variable (fresh_pf2_sum_bit2 : FF0)
variable (fresh_pf1_sum_bit1 : FF0)
lemma correct :
((((((((fresh_pf0_sum_bit0) * (fresh_pf0_sum_bit0))) = (fresh_pf0_sum_bit0))) ∧ (((((fresh_pf1_sum_bit1) * (fresh_pf1_sum_bit1))) = (fresh_pf1_sum_bit1))) ∧ (((((fresh_pf2_sum_bit2) * (fresh_pf2_sum_bit2))) = (fresh_pf2_sum_bit2))) ∧ (((((fresh_pf3_sum_bit3) * (fresh_pf3_sum_bit3))) = (fresh_pf3_sum_bit3))) ∧ (((((fresh_pf4_sum_bit4) * (fresh_pf4_sum_bit4))) = (fresh_pf4_sum_bit4))) ∧ (((((fresh_pf5_sum_bit5) * (fresh_pf5_sum_bit5))) = (fresh_pf5_sum_bit5))) ∧ ((((fresh_pf0_sum_bit0) + (((fresh_pf1_sum_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_sum_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf3_sum_bit3) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf4_sum_bit4) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf5_sum_bit5) * (32 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  d) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  e) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  f))))) → (((if (((BVModEq.bool_to_bv 1 (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul a b) c) d) e) f)[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf0_sum_bit0)))))
 := by translate_all
