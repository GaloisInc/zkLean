import BVModEq.TranslateAll
set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900
abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
abbrev f := FF0

def BNE_32 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => 1 - (x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61]))*(x[62]*x[63] + (1 - x[62])*(1 - x[63])))


lemma not_eq_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
  some bvoutput = BVModEq.map_f_to_bv 32 foutput ->
   some (BVModEq.bool_to_bv 32 bv1[31])  = BVModEq.map_f_to_bv 32 fv1[0]  ->
   some (BVModEq.bool_to_bv 32 bv2[31]) = BVModEq.map_f_to_bv 32 fv1[1]  ->
   some (BVModEq.bool_to_bv 32 bv1[30]) = BVModEq.map_f_to_bv 32 fv1[2]  ->
   some (BVModEq.bool_to_bv 32 bv2[30]) = BVModEq.map_f_to_bv 32 fv1[3]  ->
   some (BVModEq.bool_to_bv 32 bv1[29]) = BVModEq.map_f_to_bv 32 fv1[4]  ->
   some (BVModEq.bool_to_bv 32 bv2[29]) = BVModEq.map_f_to_bv 32 fv1[5]  ->
   some (BVModEq.bool_to_bv 32 bv1[28]) = BVModEq.map_f_to_bv 32 fv1[6]  ->
   some (BVModEq.bool_to_bv 32 bv2[28]) = BVModEq.map_f_to_bv 32 fv1[7]  ->
   some (BVModEq.bool_to_bv 32 bv1[27])  = BVModEq.map_f_to_bv 32 fv1[8]  ->
   some (BVModEq.bool_to_bv 32 bv2[27]) = BVModEq.map_f_to_bv 32 fv1[9]  ->
   some (BVModEq.bool_to_bv 32 bv1[26]) = BVModEq.map_f_to_bv 32 fv1[10]  ->
   some (BVModEq.bool_to_bv 32 bv2[26]) = BVModEq.map_f_to_bv 32 fv1[11]  ->
   some (BVModEq.bool_to_bv 32 bv1[25]) = BVModEq.map_f_to_bv 32 fv1[12]  ->
   some (BVModEq.bool_to_bv 32 bv2[25]) = BVModEq.map_f_to_bv 32 fv1[13]  ->
   some (BVModEq.bool_to_bv 32 bv1[24]) = BVModEq.map_f_to_bv 32 fv1[14]  ->
   some (BVModEq.bool_to_bv 32 bv2[24]) = BVModEq.map_f_to_bv 32 fv1[15]  ->
   some (BVModEq.bool_to_bv 32 bv1[23])  = BVModEq.map_f_to_bv 32 fv1[16]  ->
   some (BVModEq.bool_to_bv 32 bv2[23]) = BVModEq.map_f_to_bv 32 fv1[17]  ->
   some (BVModEq.bool_to_bv 32 bv1[22]) = BVModEq.map_f_to_bv 32 fv1[18]  ->
   some (BVModEq.bool_to_bv 32 bv2[22]) = BVModEq.map_f_to_bv 32 fv1[19]  ->
   some (BVModEq.bool_to_bv 32 bv1[21]) = BVModEq.map_f_to_bv 32 fv1[20]  ->
   some (BVModEq.bool_to_bv 32 bv2[21]) = BVModEq.map_f_to_bv 32 fv1[21]  ->
   some (BVModEq.bool_to_bv 32 bv1[20]) = BVModEq.map_f_to_bv 32 fv1[22]  ->
   some (BVModEq.bool_to_bv 32 bv2[20]) = BVModEq.map_f_to_bv 32 fv1[23]  ->
   some (BVModEq.bool_to_bv 32 bv1[19])  = BVModEq.map_f_to_bv 32 fv1[24]  ->
   some (BVModEq.bool_to_bv 32 bv2[19]) = BVModEq.map_f_to_bv 32 fv1[25]  ->
   some (BVModEq.bool_to_bv 32 bv1[18]) = BVModEq.map_f_to_bv 32 fv1[26]  ->
   some (BVModEq.bool_to_bv 32 bv2[18]) = BVModEq.map_f_to_bv 32 fv1[27]  ->
   some (BVModEq.bool_to_bv 32 bv1[17]) = BVModEq.map_f_to_bv 32 fv1[28]  ->
   some (BVModEq.bool_to_bv 32 bv2[17]) = BVModEq.map_f_to_bv 32 fv1[29]  ->
   some (BVModEq.bool_to_bv 32 bv1[16]) = BVModEq.map_f_to_bv 32 fv1[30]  ->
   some (BVModEq.bool_to_bv 32 bv2[16]) = BVModEq.map_f_to_bv 32 fv1[31]  ->
  some (BVModEq.bool_to_bv 32 bv1[15])  = BVModEq.map_f_to_bv 32 fv2[0]  ->
   some (BVModEq.bool_to_bv 32 bv2[15]) = BVModEq.map_f_to_bv 32 fv2[1]  ->
   some (BVModEq.bool_to_bv 32 bv1[14]) = BVModEq.map_f_to_bv 32 fv2[2]  ->
   some (BVModEq.bool_to_bv 32 bv2[14]) = BVModEq.map_f_to_bv 32 fv2[3]  ->
   some (BVModEq.bool_to_bv 32 bv1[13]) = BVModEq.map_f_to_bv 32 fv2[4]  ->
   some (BVModEq.bool_to_bv 32 bv2[13]) = BVModEq.map_f_to_bv 32 fv2[5]  ->
   some (BVModEq.bool_to_bv 32 bv1[12]) = BVModEq.map_f_to_bv 32 fv2[6]  ->
   some (BVModEq.bool_to_bv 32 bv2[12]) = BVModEq.map_f_to_bv 32 fv2[7]  ->
  some (BVModEq.bool_to_bv 32 bv1[11]) = BVModEq.map_f_to_bv 32 fv2[8]  ->
  some (BVModEq.bool_to_bv 32 bv2[11]) = BVModEq.map_f_to_bv 32 fv2[9]  ->
  some (BVModEq.bool_to_bv 32 bv1[10]) = BVModEq.map_f_to_bv 32  fv2[10]  ->
  some (BVModEq.bool_to_bv 32 bv2[10]) = BVModEq.map_f_to_bv 32 fv2[11]  ->
  some (BVModEq.bool_to_bv 32 bv1[9]) = BVModEq.map_f_to_bv 32 fv2[12]  ->
  some (BVModEq.bool_to_bv 32 bv2[9]) = BVModEq.map_f_to_bv 32 fv2[13]  ->
  some (BVModEq.bool_to_bv 32 bv1[8]) = BVModEq.map_f_to_bv 32 fv2[14]  ->
  some (BVModEq.bool_to_bv 32 bv2[8]) = BVModEq.map_f_to_bv 32 fv2[15]  ->
   some (BVModEq.bool_to_bv 32 bv1[7])  = BVModEq.map_f_to_bv 32 fv2[16]  ->
   some (BVModEq.bool_to_bv 32 bv2[7]) = BVModEq.map_f_to_bv 32 fv2[17]  ->
   some (BVModEq.bool_to_bv 32 bv1[6]) = BVModEq.map_f_to_bv 32 fv2[18]  ->
   some (BVModEq.bool_to_bv 32 bv2[6]) = BVModEq.map_f_to_bv 32 fv2[19]  ->
   some (BVModEq.bool_to_bv 32 bv1[5]) = BVModEq.map_f_to_bv 32 fv2[20]  ->
   some (BVModEq.bool_to_bv 32 bv2[5]) = BVModEq.map_f_to_bv 32 fv2[21]  ->
   some (BVModEq.bool_to_bv 32 bv1[4]) = BVModEq.map_f_to_bv 32 fv2[22]  ->
   some (BVModEq.bool_to_bv 32 bv2[4]) = BVModEq.map_f_to_bv 32 fv2[23]  ->
  some (BVModEq.bool_to_bv 32 bv1[3]) = BVModEq.map_f_to_bv 32 fv2[24]  ->
  some (BVModEq.bool_to_bv 32 bv2[3]) = BVModEq.map_f_to_bv 32 fv2[25]  ->
  some (BVModEq.bool_to_bv 32 bv1[2]) = BVModEq.map_f_to_bv 32  fv2[26]  ->
  some (BVModEq.bool_to_bv 32 bv2[2]) = BVModEq.map_f_to_bv 32 fv2[27]  ->
  some (BVModEq.bool_to_bv 32 bv1[1]) = BVModEq.map_f_to_bv 32 fv2[28]  ->
  some (BVModEq.bool_to_bv 32 bv2[1]) = BVModEq.map_f_to_bv 32 fv2[29]  ->
  some (BVModEq.bool_to_bv 32 bv1[0]) = BVModEq.map_f_to_bv 32 fv2[30]  ->
  some (BVModEq.bool_to_bv 32 bv2[0]) = BVModEq.map_f_to_bv 32 fv2[31]  ->
  (bvoutput = BVModEq.bool_to_bv 32 !(bv1 = bv2))
  =
  (foutput = evalSubtable BNE_32 (Vector.append fv1 fv2))
:= by
  unfold BNE_32
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
--  sorry
--  apply h_1
--  have h :  1 -
--     (ZMod.val fv1[0] * ZMod.val fv1[1] + (1 - ZMod.val fv1[0]) * (1 - ZMod.val fv1[1])) *
--       ((ZMod.val fv1[2] * ZMod.val fv1[3] + (1 - ZMod.val fv1[2]) * (1 - ZMod.val fv1[3])) *
--         (ZMod.val fv1[4] * ZMod.val fv1[5] + (1 - ZMod.val fv1[4]) * (1 - ZMod.val fv1[5]))) <
--   4294967296  := by sorry
--  apply Nat.lt_of_lt_of_le
--  apply h
--  decide
--  exact Nat.lt_of_lt_of_le h (by decide)


--  have h : (ZMod.val fv1[0] * ZMod.val fv1[1] + (1 - ZMod.val fv1[0]) * (1 - ZMod.val fv1[1])) *
--           (ZMod.val fv1[2] * ZMod.val fv1[3] + (1 - ZMod.val fv1[2]) * (1 - ZMod.val fv1[3])) *
--         (ZMod.val fv1[4] * ZMod.val fv1[5] + (1 - ZMod.val fv1[4]) * (1 - ZMod.val fv1[5])) *
--       (ZMod.val fv1[6] * ZMod.val fv1[7] + (1 - ZMod.val fv1[6]) * (1 - ZMod.val fv1[7])) *
--     (ZMod.val fv1[8] * ZMod.val fv1[9] + (1 - ZMod.val fv1[8]) * (1 - ZMod.val fv1[9])) ≤
--   1 := by sorry
--  simp [ Nat.mul_assoc] at h
--  bvify [h]
--  intro NatLeq; intro ZLeq; intro Eq; simp at Eq ; rw [Eq]
--  valify [h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1,
-- h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1,
-- h17_1, h18_1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1,
-- h25_1, h26_1, h27_1, h28_1, h29_1, h30_1, h31_1, h32_1,
-- h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1, h40_1,
-- h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1,
-- h49_1, h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1,
-- h57_1, h58_1, h59_1, h60_1, h61_1, h62_1, h63_1, h64_1]
--  findModLT 32
--  sorry
--  intro Leq
--  rw [Nat.mod_eq_of_lt]
--  rw [BitVec_ofNat_eq_iff_32]
--  simp [Nat.lt_succ_iff] at NatLeq
--  bvify [NatLeq, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1,
-- h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1,
-- h17_1, h18_1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1,
-- h25_1, h26_1, h27_1, h28_1, h29_1, h30_1, h31_1, h32_1,
-- h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1, h40_1,
-- h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1,
-- h49_1, h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1,
-- h57_1, h58_1, h59_1, h60_1, h61_1, h62_1, h63_1, h64_1 ]
-- bv_dec
--  have h : (ZMod.val fv1[0] * ZMod.val fv1[1] + (1 - ZMod.val fv1[0]) * (1 - ZMod.val fv1[1])) *
--                                                                 (ZMod.val fv1[2] * ZMod.val fv1[3] +
--                                                                   (1 - ZMod.val fv1[2]) * (1 - ZMod.val fv1[3])) *
--                                                               (ZMod.val fv1[4] * ZMod.val fv1[5] +
--                                                                 (1 - ZMod.val fv1[4]) * (1 - ZMod.val fv1[5])) *
--                                                             (ZMod.val fv1[6] * ZMod.val fv1[7] +
--                                                               (1 - ZMod.val fv1[6]) * (1 - ZMod.val fv1[7])) *
--                                                           (ZMod.val fv1[8] * ZMod.val fv1[9] +
--                                                             (1 - ZMod.val fv1[8]) * (1 - ZMod.val fv1[9])) *
--                                                         (ZMod.val fv1[10] * ZMod.val fv1[11] +
--                                                           (1 - ZMod.val fv1[10]) * (1 - ZMod.val fv1[11])) *
--                                                       (ZMod.val fv1[12] * ZMod.val fv1[13] +
--                                                         (1 - ZMod.val fv1[12]) * (1 - ZMod.val fv1[13])) *
--                                                     (ZMod.val fv1[14] * ZMod.val fv1[15] +
--                                                       (1 - ZMod.val fv1[14]) * (1 - ZMod.val fv1[15])) *
--                                                   (ZMod.val fv1[16] * ZMod.val fv1[17] +
--                                                     (1 - ZMod.val fv1[16]) * (1 - ZMod.val fv1[17])) *
--                                                 (ZMod.val fv1[18] * ZMod.val fv1[19] +
--                                                   (1 - ZMod.val fv1[18]) * (1 - ZMod.val fv1[19])) *
--                                               (ZMod.val fv1[20] * ZMod.val fv1[21] +
--                                                 (1 - ZMod.val fv1[20]) * (1 - ZMod.val fv1[21])) *
--                                             (ZMod.val fv1[22] * ZMod.val fv1[23] +
--                                               (1 - ZMod.val fv1[22]) * (1 - ZMod.val fv1[23])) *
--                                           (ZMod.val fv1[24] * ZMod.val fv1[25] +
--                                             (1 - ZMod.val fv1[24]) * (1 - ZMod.val fv1[25])) *
--                                         (ZMod.val fv1[26] * ZMod.val fv1[27] +
--                                           (1 - ZMod.val fv1[26]) * (1 - ZMod.val fv1[27])) *
--                                       (ZMod.val fv1[28] * ZMod.val fv1[29] +
--                                         (1 - ZMod.val fv1[28]) * (1 - ZMod.val fv1[29])) *
--                                     (ZMod.val fv1[30] * ZMod.val fv1[31] +
--                                       (1 - ZMod.val fv1[30]) * (1 - ZMod.val fv1[31])) *
--                                   (ZMod.val fv2[0] * ZMod.val fv2[1] + (1 - ZMod.val fv2[0]) * (1 - ZMod.val fv2[1])) *
--                                 (ZMod.val fv2[2] * ZMod.val fv2[3] + (1 - ZMod.val fv2[2]) * (1 - ZMod.val fv2[3])) *
--                               (ZMod.val fv2[4] * ZMod.val fv2[5] + (1 - ZMod.val fv2[4]) * (1 - ZMod.val fv2[5])) *
--                             (ZMod.val fv2[6] * ZMod.val fv2[7] + (1 - ZMod.val fv2[6]) * (1 - ZMod.val fv2[7])) *
--                           (ZMod.val fv2[8] * ZMod.val fv2[9] + (1 - ZMod.val fv2[8]) * (1 - ZMod.val fv2[9])) *
--                         (ZMod.val fv2[10] * ZMod.val fv2[11] + (1 - ZMod.val fv2[10]) * (1 - ZMod.val fv2[11])) *
--                       (ZMod.val fv2[12] * ZMod.val fv2[13] + (1 - ZMod.val fv2[12]) * (1 - ZMod.val fv2[13])) *
--                     (ZMod.val fv2[14] * ZMod.val fv2[15] + (1 - ZMod.val fv2[14]) * (1 - ZMod.val fv2[15])) *
--                   (ZMod.val fv2[16] * ZMod.val fv2[17] + (1 - ZMod.val fv2[16]) * (1 - ZMod.val fv2[17])) *
--                 (ZMod.val fv2[18] * ZMod.val fv2[19] + (1 - ZMod.val fv2[18]) * (1 - ZMod.val fv2[19])) *
--               (ZMod.val fv2[20] * ZMod.val fv2[21] + (1 - ZMod.val fv2[20]) * (1 - ZMod.val fv2[21])) *
--             (ZMod.val fv2[22] * ZMod.val fv2[23] + (1 - ZMod.val fv2[22]) * (1 - ZMod.val fv2[23])) *
--           (ZMod.val fv2[24] * ZMod.val fv2[25] + (1 - ZMod.val fv2[24]) * (1 - ZMod.val fv2[25])) *
--         (ZMod.val fv2[26] * ZMod.val fv2[27] + (1 - ZMod.val fv2[26]) * (1 - ZMod.val fv2[27])) *
--       (ZMod.val fv2[28] * ZMod.val fv2[29] + (1 - ZMod.val fv2[28]) * (1 - ZMod.val fv2[29])) *
--     (ZMod.val fv2[30] * ZMod.val fv2[31] + (1 - ZMod.val fv2[30]) * (1 - ZMod.val fv2[31])) <
--   2 := by sorry
--  simp [<- Nat.lt_add_one_iff]
--  simp [Nat.mul_assoc] at h
--  apply h
