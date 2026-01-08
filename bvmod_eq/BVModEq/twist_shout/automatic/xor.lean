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

def XOR_32 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => 0 + 2147483648*((1 - x[0])*x[1] + x[0]*(1 - x[1])) + 1073741824*((1 - x[2])*x[3] + x[2]*(1 - x[3])) + 536870912*((1 - x[4])*x[5] + x[4]*(1 - x[5])) + 268435456*((1 - x[6])*x[7] + x[6]*(1 - x[7])) + 134217728*((1 - x[8])*x[9] + x[8]*(1 - x[9])) + 67108864*((1 - x[10])*x[11] + x[10]*(1 - x[11])) + 33554432*((1 - x[12])*x[13] + x[12]*(1 - x[13])) + 16777216*((1 - x[14])*x[15] + x[14]*(1 - x[15])) + 8388608*((1 - x[16])*x[17] + x[16]*(1 - x[17])) + 4194304*((1 - x[18])*x[19] + x[18]*(1 - x[19])) + 2097152*((1 - x[20])*x[21] + x[20]*(1 - x[21])) + 1048576*((1 - x[22])*x[23] + x[22]*(1 - x[23])) + 524288*((1 - x[24])*x[25] + x[24]*(1 - x[25])) + 262144*((1 - x[26])*x[27] + x[26]*(1 - x[27])) + 131072*((1 - x[28])*x[29] + x[28]*(1 - x[29])) + 65536*((1 - x[30])*x[31] + x[30]*(1 - x[31])) + 32768*((1 - x[32])*x[33] + x[32]*(1 - x[33])) + 16384*((1 - x[34])*x[35] + x[34]*(1 - x[35])) + 8192*((1 - x[36])*x[37] + x[36]*(1 - x[37])) + 4096*((1 - x[38])*x[39] + x[38]*(1 - x[39])) + 2048*((1 - x[40])*x[41] + x[40]*(1 - x[41])) + 1024*((1 - x[42])*x[43] + x[42]*(1 - x[43])) + 512*((1 - x[44])*x[45] + x[44]*(1 - x[45])) + 256*((1 - x[46])*x[47] + x[46]*(1 - x[47])) + 128*((1 - x[48])*x[49] + x[48]*(1 - x[49])) + 64*((1 - x[50])*x[51] + x[50]*(1 - x[51])) + 32*((1 - x[52])*x[53] + x[52]*(1 - x[53])) + 16*((1 - x[54])*x[55] + x[54]*(1 - x[55])) + 8*((1 - x[56])*x[57] + x[56]*(1 - x[57])) + 4*((1 - x[58])*x[59] + x[58]*(1 - x[59])) + 2*((1 - x[60])*x[61] + x[60]*(1 - x[61])) + 1*((1 - x[62])*x[63] + x[62]*(1 - x[63])))


lemma xor_32_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
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
  (bvoutput = BitVec.xor bv1 bv2)
  =
  (foutput = evalSubtable XOR_32 (Vector.append fv1 fv2))
:= by
   unfold XOR_32
   unfold evalSubtable
   unfold subtableFromMLE
   unfold Vector.append
   translate_all false
