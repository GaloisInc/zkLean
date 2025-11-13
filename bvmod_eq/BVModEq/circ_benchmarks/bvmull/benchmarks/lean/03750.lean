import BVModEq.TranslateAll

abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry 
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry 
set_option maxHeartbeats  20000000000000000000
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
variable (fresh_pf1_sum_bit1 : FF0)
variable (n : BitVec 2)
variable (m : BitVec 2)
variable (l : BitVec 2)
variable (k : BitVec 2)
variable (j : BitVec 2)
variable (i : BitVec 2)
variable (h : BitVec 2)
variable (g : BitVec 2)
variable (f : BitVec 2)
variable (e : BitVec 2)
variable (d : BitVec 2)
variable (c : BitVec 2)
variable (b : BitVec 2)
variable (a : BitVec 2)
variable (fresh_pf0_sum_bit0 : FF0)
variable (fresh_pf27_sum_bit27 : FF0)
variable (fresh_pf26_sum_bit26 : FF0)
variable (fresh_pf25_sum_bit25 : FF0)
variable (fresh_pf24_sum_bit24 : FF0)
variable (fresh_pf23_sum_bit23 : FF0)
variable (fresh_pf22_sum_bit22 : FF0)
variable (fresh_pf21_sum_bit21 : FF0)
variable (fresh_pf20_sum_bit20 : FF0)
variable (fresh_pf19_sum_bit19 : FF0)
variable (fresh_pf18_sum_bit18 : FF0)
variable (fresh_pf17_sum_bit17 : FF0)
variable (fresh_pf16_sum_bit16 : FF0)
variable (fresh_pf15_sum_bit15 : FF0)
variable (fresh_pf14_sum_bit14 : FF0)
variable (fresh_pf13_sum_bit13 : FF0)
variable (fresh_pf12_sum_bit12 : FF0)
variable (fresh_pf11_sum_bit11 : FF0)
variable (fresh_pf10_sum_bit10 : FF0)
variable (fresh_pf9_sum_bit9 : FF0)
variable (fresh_pf8_sum_bit8 : FF0)
variable (fresh_pf7_sum_bit7 : FF0)
variable (fresh_pf6_sum_bit6 : FF0)
variable (fresh_pf5_sum_bit5 : FF0)
variable (fresh_pf4_sum_bit4 : FF0)
variable (fresh_pf3_sum_bit3 : FF0)
variable (fresh_pf2_sum_bit2 : FF0)
lemma correct :
((((((((fresh_pf0_sum_bit0) * (fresh_pf0_sum_bit0))) = (fresh_pf0_sum_bit0))) ∧ (((((fresh_pf1_sum_bit1) * (fresh_pf1_sum_bit1))) = (fresh_pf1_sum_bit1))) ∧ (((((fresh_pf2_sum_bit2) * (fresh_pf2_sum_bit2))) = (fresh_pf2_sum_bit2))) ∧ (((((fresh_pf3_sum_bit3) * (fresh_pf3_sum_bit3))) = (fresh_pf3_sum_bit3))) ∧ (((((fresh_pf4_sum_bit4) * (fresh_pf4_sum_bit4))) = (fresh_pf4_sum_bit4))) ∧ (((((fresh_pf5_sum_bit5) * (fresh_pf5_sum_bit5))) = (fresh_pf5_sum_bit5))) ∧ (((((fresh_pf6_sum_bit6) * (fresh_pf6_sum_bit6))) = (fresh_pf6_sum_bit6))) ∧ (((((fresh_pf7_sum_bit7) * (fresh_pf7_sum_bit7))) = (fresh_pf7_sum_bit7))) ∧ (((((fresh_pf8_sum_bit8) * (fresh_pf8_sum_bit8))) = (fresh_pf8_sum_bit8))) ∧ (((((fresh_pf9_sum_bit9) * (fresh_pf9_sum_bit9))) = (fresh_pf9_sum_bit9))) ∧ (((((fresh_pf10_sum_bit10) * (fresh_pf10_sum_bit10))) = (fresh_pf10_sum_bit10))) ∧ (((((fresh_pf11_sum_bit11) * (fresh_pf11_sum_bit11))) = (fresh_pf11_sum_bit11))) ∧ (((((fresh_pf12_sum_bit12) * (fresh_pf12_sum_bit12))) = (fresh_pf12_sum_bit12))) ∧ (((((fresh_pf13_sum_bit13) * (fresh_pf13_sum_bit13))) = (fresh_pf13_sum_bit13))) ∧ (((((fresh_pf14_sum_bit14) * (fresh_pf14_sum_bit14))) = (fresh_pf14_sum_bit14))) ∧ (((((fresh_pf15_sum_bit15) * (fresh_pf15_sum_bit15))) = (fresh_pf15_sum_bit15))) ∧ (((((fresh_pf16_sum_bit16) * (fresh_pf16_sum_bit16))) = (fresh_pf16_sum_bit16))) ∧ (((((fresh_pf17_sum_bit17) * (fresh_pf17_sum_bit17))) = (fresh_pf17_sum_bit17))) ∧ (((((fresh_pf18_sum_bit18) * (fresh_pf18_sum_bit18))) = (fresh_pf18_sum_bit18))) ∧ (((((fresh_pf19_sum_bit19) * (fresh_pf19_sum_bit19))) = (fresh_pf19_sum_bit19))) ∧ (((((fresh_pf20_sum_bit20) * (fresh_pf20_sum_bit20))) = (fresh_pf20_sum_bit20))) ∧ (((((fresh_pf21_sum_bit21) * (fresh_pf21_sum_bit21))) = (fresh_pf21_sum_bit21))) ∧ (((((fresh_pf22_sum_bit22) * (fresh_pf22_sum_bit22))) = (fresh_pf22_sum_bit22))) ∧ (((((fresh_pf23_sum_bit23) * (fresh_pf23_sum_bit23))) = (fresh_pf23_sum_bit23))) ∧ (((((fresh_pf24_sum_bit24) * (fresh_pf24_sum_bit24))) = (fresh_pf24_sum_bit24))) ∧ (((((fresh_pf25_sum_bit25) * (fresh_pf25_sum_bit25))) = (fresh_pf25_sum_bit25))) ∧ (((((fresh_pf26_sum_bit26) * (fresh_pf26_sum_bit26))) = (fresh_pf26_sum_bit26))) ∧ (((((fresh_pf27_sum_bit27) * (fresh_pf27_sum_bit27))) = (fresh_pf27_sum_bit27))) ∧ ((((fresh_pf0_sum_bit0) + (((fresh_pf1_sum_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_sum_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf3_sum_bit3) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf4_sum_bit4) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf5_sum_bit5) * (32 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf6_sum_bit6) * (64 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf7_sum_bit7) * (128 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf8_sum_bit8) * (256 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf9_sum_bit9) * (512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf10_sum_bit10) * (1024 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf11_sum_bit11) * (2048 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf12_sum_bit12) * (4096 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf13_sum_bit13) * (8192 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf14_sum_bit14) * (16384 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf15_sum_bit15) * (32768 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf16_sum_bit16) * (65536 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf17_sum_bit17) * (131072 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf18_sum_bit18) * (262144 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf19_sum_bit19) * (524288 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf20_sum_bit20) * (1048576 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf21_sum_bit21) * (2097152 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf22_sum_bit22) * (4194304 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf23_sum_bit23) * (8388608 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf24_sum_bit24) * (16777216 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf25_sum_bit25) * (33554432 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf26_sum_bit26) * (67108864 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf27_sum_bit27) * (134217728 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  d) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  e) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  f) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  g) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  h) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  i) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  j) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  k) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  l) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  m) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  n))))) → (((((if (((BVModEq.bool_to_bv 1 (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul a b) c) d) e) f) g) h) i) j) k) l) m) n)[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf0_sum_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul (BitVec.mul a b) c) d) e) f) g) h) i) j) k) l) m) n)[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf1_sum_bit1)))))))
 := by translate_all
