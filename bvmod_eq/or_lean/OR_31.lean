-- AUTO-GENERATED — DO NOT EDIT


def OR_31  : Subtable FF0 62 :=
  subtableFromMLE (fun x => 1*(x[61] + x[30] - x[61]*x[30]) + 2*(x[60] + x[29] - x[60]*x[29]) + 4*(x[59] + x[28] - x[59]*x[28]) + 8*(x[58] + x[27] - x[58]*x[27]) + 16*(x[57] + x[26] - x[57]*x[26]) + 32*(x[56] + x[25] - x[56]*x[25]) + 64*(x[55] + x[24] - x[55]*x[24]) + 128*(x[54] + x[23] - x[54]*x[23]) + 256*(x[53] + x[22] - x[53]*x[22]) + 512*(x[52] + x[21] - x[52]*x[21]) + 1024*(x[51] + x[20] - x[51]*x[20]) + 2048*(x[50] + x[19] - x[50]*x[19]) + 4096*(x[49] + x[18] - x[49]*x[18]) + 8192*(x[48] + x[17] - x[48]*x[17]) + 16384*(x[47] + x[16] - x[47]*x[16]) + 32768*(x[46] + x[15] - x[46]*x[15]) + 65536*(x[45] + x[14] - x[45]*x[14]) + 131072*(x[44] + x[13] - x[44]*x[13]) + 262144*(x[43] + x[12] - x[43]*x[12]) + 524288*(x[42] + x[11] - x[42]*x[11]) + 1048576*(x[41] + x[10] - x[41]*x[10]) + 2097152*(x[40] + x[9] - x[40]*x[9]) + 4194304*(x[39] + x[8] - x[39]*x[8]) + 8388608*(x[38] + x[7] - x[38]*x[7]) + 16777216*(x[37] + x[6] - x[37]*x[6]) + 33554432*(x[36] + x[5] - x[36]*x[5]) + 67108864*(x[35] + x[4] - x[35]*x[4]) + 134217728*(x[34] + x[3] - x[34]*x[3]) + 268435456*(x[33] + x[2] - x[33]*x[2]) + 536870912*(x[32] + x[1] - x[32]*x[1]) + 1073741824*(x[31] + x[0] - x[31]*x[0]))

lemma or_mle_31_chunk
  (bv1 bv2 : BitVec 31)
  (fv1 fv2 : Vector FF0 31) :
  some bvoutput = BVModEq.map_f_to_bv 31 foutput ->
  some (BVModEq.bool_to_bv 31 bv1[30]) = BVModEq.map_f_to_bv 31 fv1[0]  ->
  some (BVModEq.bool_to_bv 31 bv1[29]) = BVModEq.map_f_to_bv 31 fv1[1]  ->
  some (BVModEq.bool_to_bv 31 bv1[28]) = BVModEq.map_f_to_bv 31 fv1[2]  ->
  some (BVModEq.bool_to_bv 31 bv1[27]) = BVModEq.map_f_to_bv 31 fv1[3]  ->
  some (BVModEq.bool_to_bv 31 bv1[26]) = BVModEq.map_f_to_bv 31 fv1[4]  ->
  some (BVModEq.bool_to_bv 31 bv1[25]) = BVModEq.map_f_to_bv 31 fv1[5]  ->
  some (BVModEq.bool_to_bv 31 bv1[24]) = BVModEq.map_f_to_bv 31 fv1[6]  ->
  some (BVModEq.bool_to_bv 31 bv1[23]) = BVModEq.map_f_to_bv 31 fv1[7]  ->
  some (BVModEq.bool_to_bv 31 bv1[22]) = BVModEq.map_f_to_bv 31 fv1[8]  ->
  some (BVModEq.bool_to_bv 31 bv1[21]) = BVModEq.map_f_to_bv 31 fv1[9]  ->
  some (BVModEq.bool_to_bv 31 bv1[20]) = BVModEq.map_f_to_bv 31 fv1[10]  ->
  some (BVModEq.bool_to_bv 31 bv1[19]) = BVModEq.map_f_to_bv 31 fv1[11]  ->
  some (BVModEq.bool_to_bv 31 bv1[18]) = BVModEq.map_f_to_bv 31 fv1[12]  ->
  some (BVModEq.bool_to_bv 31 bv1[17]) = BVModEq.map_f_to_bv 31 fv1[13]  ->
  some (BVModEq.bool_to_bv 31 bv1[16]) = BVModEq.map_f_to_bv 31 fv1[14]  ->
  some (BVModEq.bool_to_bv 31 bv1[15]) = BVModEq.map_f_to_bv 31 fv1[15]  ->
  some (BVModEq.bool_to_bv 31 bv1[14]) = BVModEq.map_f_to_bv 31 fv1[16]  ->
  some (BVModEq.bool_to_bv 31 bv1[13]) = BVModEq.map_f_to_bv 31 fv1[17]  ->
  some (BVModEq.bool_to_bv 31 bv1[12]) = BVModEq.map_f_to_bv 31 fv1[18]  ->
  some (BVModEq.bool_to_bv 31 bv1[11]) = BVModEq.map_f_to_bv 31 fv1[19]  ->
  some (BVModEq.bool_to_bv 31 bv1[10]) = BVModEq.map_f_to_bv 31 fv1[20]  ->
  some (BVModEq.bool_to_bv 31 bv1[9]) = BVModEq.map_f_to_bv 31 fv1[21]  ->
  some (BVModEq.bool_to_bv 31 bv1[8]) = BVModEq.map_f_to_bv 31 fv1[22]  ->
  some (BVModEq.bool_to_bv 31 bv1[7]) = BVModEq.map_f_to_bv 31 fv1[23]  ->
  some (BVModEq.bool_to_bv 31 bv1[6]) = BVModEq.map_f_to_bv 31 fv1[24]  ->
  some (BVModEq.bool_to_bv 31 bv1[5]) = BVModEq.map_f_to_bv 31 fv1[25]  ->
  some (BVModEq.bool_to_bv 31 bv1[4]) = BVModEq.map_f_to_bv 31 fv1[26]  ->
  some (BVModEq.bool_to_bv 31 bv1[3]) = BVModEq.map_f_to_bv 31 fv1[27]  ->
  some (BVModEq.bool_to_bv 31 bv1[2]) = BVModEq.map_f_to_bv 31 fv1[28]  ->
  some (BVModEq.bool_to_bv 31 bv1[1]) = BVModEq.map_f_to_bv 31 fv1[29]  ->
  some (BVModEq.bool_to_bv 31 bv1[0]) = BVModEq.map_f_to_bv 31 fv1[30]  ->
  some (BVModEq.bool_to_bv 31 bv2[30]) = BVModEq.map_f_to_bv 31 fv2[0]  ->
  some (BVModEq.bool_to_bv 31 bv2[29]) = BVModEq.map_f_to_bv 31 fv2[1]  ->
  some (BVModEq.bool_to_bv 31 bv2[28]) = BVModEq.map_f_to_bv 31 fv2[2]  ->
  some (BVModEq.bool_to_bv 31 bv2[27]) = BVModEq.map_f_to_bv 31 fv2[3]  ->
  some (BVModEq.bool_to_bv 31 bv2[26]) = BVModEq.map_f_to_bv 31 fv2[4]  ->
  some (BVModEq.bool_to_bv 31 bv2[25]) = BVModEq.map_f_to_bv 31 fv2[5]  ->
  some (BVModEq.bool_to_bv 31 bv2[24]) = BVModEq.map_f_to_bv 31 fv2[6]  ->
  some (BVModEq.bool_to_bv 31 bv2[23]) = BVModEq.map_f_to_bv 31 fv2[7]  ->
  some (BVModEq.bool_to_bv 31 bv2[22]) = BVModEq.map_f_to_bv 31 fv2[8]  ->
  some (BVModEq.bool_to_bv 31 bv2[21]) = BVModEq.map_f_to_bv 31 fv2[9]  ->
  some (BVModEq.bool_to_bv 31 bv2[20]) = BVModEq.map_f_to_bv 31 fv2[10]  ->
  some (BVModEq.bool_to_bv 31 bv2[19]) = BVModEq.map_f_to_bv 31 fv2[11]  ->
  some (BVModEq.bool_to_bv 31 bv2[18]) = BVModEq.map_f_to_bv 31 fv2[12]  ->
  some (BVModEq.bool_to_bv 31 bv2[17]) = BVModEq.map_f_to_bv 31 fv2[13]  ->
  some (BVModEq.bool_to_bv 31 bv2[16]) = BVModEq.map_f_to_bv 31 fv2[14]  ->
  some (BVModEq.bool_to_bv 31 bv2[15]) = BVModEq.map_f_to_bv 31 fv2[15]  ->
  some (BVModEq.bool_to_bv 31 bv2[14]) = BVModEq.map_f_to_bv 31 fv2[16]  ->
  some (BVModEq.bool_to_bv 31 bv2[13]) = BVModEq.map_f_to_bv 31 fv2[17]  ->
  some (BVModEq.bool_to_bv 31 bv2[12]) = BVModEq.map_f_to_bv 31 fv2[18]  ->
  some (BVModEq.bool_to_bv 31 bv2[11]) = BVModEq.map_f_to_bv 31 fv2[19]  ->
  some (BVModEq.bool_to_bv 31 bv2[10]) = BVModEq.map_f_to_bv 31 fv2[20]  ->
  some (BVModEq.bool_to_bv 31 bv2[9]) = BVModEq.map_f_to_bv 31 fv2[21]  ->
  some (BVModEq.bool_to_bv 31 bv2[8]) = BVModEq.map_f_to_bv 31 fv2[22]  ->
  some (BVModEq.bool_to_bv 31 bv2[7]) = BVModEq.map_f_to_bv 31 fv2[23]  ->
  some (BVModEq.bool_to_bv 31 bv2[6]) = BVModEq.map_f_to_bv 31 fv2[24]  ->
  some (BVModEq.bool_to_bv 31 bv2[5]) = BVModEq.map_f_to_bv 31 fv2[25]  ->
  some (BVModEq.bool_to_bv 31 bv2[4]) = BVModEq.map_f_to_bv 31 fv2[26]  ->
  some (BVModEq.bool_to_bv 31 bv2[3]) = BVModEq.map_f_to_bv 31 fv2[27]  ->
  some (BVModEq.bool_to_bv 31 bv2[2]) = BVModEq.map_f_to_bv 31 fv2[28]  ->
  some (BVModEq.bool_to_bv 31 bv2[1]) = BVModEq.map_f_to_bv 31 fv2[29]  ->
  some (BVModEq.bool_to_bv 31 bv2[0]) = BVModEq.map_f_to_bv 31 fv2[30]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_31 (Vector.append fv1 fv2))
:= by
  unfold OR_31
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
