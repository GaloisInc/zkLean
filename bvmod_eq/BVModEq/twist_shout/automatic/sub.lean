import BVModEq.TranslateAll
set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900
set_option profiler true
set_option profiler.threshold 50

abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
abbrev f := FF0

def SUB_32 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => 0 + 2147483648*x[32] + 1073741824*x[33] + 536870912*x[34] + 268435456*x[35] + 134217728*x[36] + 67108864*x[37] + 33554432*x[38] + 16777216*x[39] + 8388608*x[40] + 4194304*x[41] + 2097152*x[42] + 1048576*x[43] + 524288*x[44] + 262144*x[45] + 131072*x[46] + 65536*x[47] + 32768*x[48] + 16384*x[49] + 8192*x[50] + 4096*x[51] + 2048*x[52] + 1024*x[53] + 512*x[54] + 256*x[55] + 128*x[56] + 64*x[57] + 32*x[58] + 16*x[59] + 8*x[60] + 4*x[61] + 2*x[62] + 1*x[63])




lemma sub_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
  some bvoutput = BVModEq.map_f_to_bv 32 foutput ->
    some (BVModEq.bool_to_bv 32 bv1[31])  = BVModEq.map_f_to_bv 32 fv1[0]  ->
   some (BVModEq.bool_to_bv 32 bv1[30]) = BVModEq.map_f_to_bv 32 fv1[1]  ->
   some (BVModEq.bool_to_bv 32 bv1[29]) = BVModEq.map_f_to_bv 32 fv1[2]  ->
   some (BVModEq.bool_to_bv 32 bv1[28]) = BVModEq.map_f_to_bv 32 fv1[3]  ->
   some (BVModEq.bool_to_bv 32 bv1[27]) = BVModEq.map_f_to_bv 32 fv1[4]  ->
   some (BVModEq.bool_to_bv 32 bv1[26]) = BVModEq.map_f_to_bv 32 fv1[5]  ->
   some (BVModEq.bool_to_bv 32 bv1[25]) = BVModEq.map_f_to_bv 32 fv1[6]  ->
   some (BVModEq.bool_to_bv 32 bv1[24]) = BVModEq.map_f_to_bv 32 fv1[7]  ->
   some (BVModEq.bool_to_bv 32 bv1[23])  = BVModEq.map_f_to_bv 32 fv1[8]  ->
   some (BVModEq.bool_to_bv 32 bv1[22]) = BVModEq.map_f_to_bv 32 fv1[9]  ->
   some (BVModEq.bool_to_bv 32 bv1[21]) = BVModEq.map_f_to_bv 32 fv1[10]  ->
   some (BVModEq.bool_to_bv 32 bv1[20]) = BVModEq.map_f_to_bv 32 fv1[11]  ->
   some (BVModEq.bool_to_bv 32 bv1[19]) = BVModEq.map_f_to_bv 32 fv1[12]  ->
   some (BVModEq.bool_to_bv 32 bv1[18]) = BVModEq.map_f_to_bv 32 fv1[13]  ->
   some (BVModEq.bool_to_bv 32 bv1[17]) = BVModEq.map_f_to_bv 32 fv1[14]  ->
   some (BVModEq.bool_to_bv 32 bv1[16]) = BVModEq.map_f_to_bv 32 fv1[15]  ->
   some (BVModEq.bool_to_bv 32 bv1[15])  = BVModEq.map_f_to_bv 32 fv1[16]  ->
   some (BVModEq.bool_to_bv 32 bv1[14]) = BVModEq.map_f_to_bv 32 fv1[17]  ->
   some (BVModEq.bool_to_bv 32 bv1[13]) = BVModEq.map_f_to_bv 32 fv1[18]  ->
   some (BVModEq.bool_to_bv 32 bv1[12]) = BVModEq.map_f_to_bv 32 fv1[19]  ->
   some (BVModEq.bool_to_bv 32 bv1[11]) = BVModEq.map_f_to_bv 32 fv1[20]  ->
   some (BVModEq.bool_to_bv 32 bv1[10]) = BVModEq.map_f_to_bv 32 fv1[21]  ->
   some (BVModEq.bool_to_bv 32 bv1[9]) = BVModEq.map_f_to_bv 32 fv1[22]  ->
   some (BVModEq.bool_to_bv 32 bv1[8]) = BVModEq.map_f_to_bv 32 fv1[23]  ->
   some (BVModEq.bool_to_bv 32 bv1[7])  = BVModEq.map_f_to_bv 32 fv1[24]  ->
   some (BVModEq.bool_to_bv 32 bv1[6]) = BVModEq.map_f_to_bv 32 fv1[25]  ->
   some (BVModEq.bool_to_bv 32 bv1[5]) = BVModEq.map_f_to_bv 32 fv1[26]  ->
   some (BVModEq.bool_to_bv 32 bv1[4]) = BVModEq.map_f_to_bv 32 fv1[27]  ->
   some (BVModEq.bool_to_bv 32 bv1[3]) = BVModEq.map_f_to_bv 32 fv1[28]  ->
   some (BVModEq.bool_to_bv 32 bv1[2]) = BVModEq.map_f_to_bv 32 fv1[29]  ->
   some (BVModEq.bool_to_bv 32 bv1[1]) = BVModEq.map_f_to_bv 32 fv1[30]  ->
   some (BVModEq.bool_to_bv 32 bv1[0]) = BVModEq.map_f_to_bv 32 fv1[31]  ->
  some (BVModEq.bool_to_bv 32 bv2[31])  = BVModEq.map_f_to_bv 32 fv2[0]  ->
   some (BVModEq.bool_to_bv 32 bv2[30]) = BVModEq.map_f_to_bv 32 fv2[1]  ->
   some (BVModEq.bool_to_bv 32 bv2[29]) = BVModEq.map_f_to_bv 32 fv2[2]  ->
   some (BVModEq.bool_to_bv 32 bv2[28]) = BVModEq.map_f_to_bv 32 fv2[3]  ->
   some (BVModEq.bool_to_bv 32 bv2[27]) = BVModEq.map_f_to_bv 32 fv2[4]  ->
   some (BVModEq.bool_to_bv 32 bv2[26]) = BVModEq.map_f_to_bv 32 fv2[5]  ->
   some (BVModEq.bool_to_bv 32 bv2[25]) = BVModEq.map_f_to_bv 32 fv2[6]  ->
   some (BVModEq.bool_to_bv 32 bv2[24]) = BVModEq.map_f_to_bv 32 fv2[7]  ->
  some (BVModEq.bool_to_bv 32 bv2[23]) = BVModEq.map_f_to_bv 32 fv2[8]  ->
  some (BVModEq.bool_to_bv 32 bv2[22]) = BVModEq.map_f_to_bv 32 fv2[9]  ->
  some (BVModEq.bool_to_bv 32 bv2[21]) = BVModEq.map_f_to_bv 32  fv2[10]  ->
  some (BVModEq.bool_to_bv 32 bv2[20]) = BVModEq.map_f_to_bv 32 fv2[11]  ->
  some (BVModEq.bool_to_bv 32 bv2[19]) = BVModEq.map_f_to_bv 32 fv2[12]  ->
  some (BVModEq.bool_to_bv 32 bv2[18]) = BVModEq.map_f_to_bv 32 fv2[13]  ->
  some (BVModEq.bool_to_bv 32 bv2[17]) = BVModEq.map_f_to_bv 32 fv2[14]  ->
  some (BVModEq.bool_to_bv 32 bv2[16]) = BVModEq.map_f_to_bv 32 fv2[15]  ->
   some (BVModEq.bool_to_bv 32 bv2[15])  = BVModEq.map_f_to_bv 32 fv2[16]  ->
   some (BVModEq.bool_to_bv 32 bv2[14]) = BVModEq.map_f_to_bv 32 fv2[17]  ->
   some (BVModEq.bool_to_bv 32 bv2[13]) = BVModEq.map_f_to_bv 32 fv2[18]  ->
   some (BVModEq.bool_to_bv 32 bv2[12]) = BVModEq.map_f_to_bv 32 fv2[19]  ->
   some (BVModEq.bool_to_bv 32 bv2[11]) = BVModEq.map_f_to_bv 32 fv2[20]  ->
   some (BVModEq.bool_to_bv 32 bv2[10]) = BVModEq.map_f_to_bv 32 fv2[21]  ->
   some (BVModEq.bool_to_bv 32 bv2[9]) = BVModEq.map_f_to_bv 32 fv2[22]  ->
   some (BVModEq.bool_to_bv 32 bv2[8]) = BVModEq.map_f_to_bv 32 fv2[23]  ->
  some (BVModEq.bool_to_bv 32 bv2[7]) = BVModEq.map_f_to_bv 32 fv2[24]  ->
  some (BVModEq.bool_to_bv 32 bv2[6]) = BVModEq.map_f_to_bv 32 fv2[25]  ->
  some (BVModEq.bool_to_bv 32 bv2[5]) = BVModEq.map_f_to_bv 32  fv2[26]  ->
  some (BVModEq.bool_to_bv 32 bv2[4]) = BVModEq.map_f_to_bv 32 fv2[27]  ->
  some (BVModEq.bool_to_bv 32 bv2[3]) = BVModEq.map_f_to_bv 32 fv2[28]  ->
  some (BVModEq.bool_to_bv 32 bv2[2]) = BVModEq.map_f_to_bv 32 fv2[29]  ->
  some (BVModEq.bool_to_bv 32 bv2[1]) = BVModEq.map_f_to_bv 32 fv2[30]  ->
  some (BVModEq.bool_to_bv 32 bv2[0]) = BVModEq.map_f_to_bv 32 fv2[31] ->
( (bvoutput =bv2)
  =
  (foutput = evalSubtable SUB_32  (Vector.append fv1 fv2))) := by

   unfold SUB_32
   unfold evalSubtable
   unfold subtableFromMLE
   unfold Vector.append
   translate_all false
