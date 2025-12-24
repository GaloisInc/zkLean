-- AUTO-GENERATED — DO NOT EDIT


def OR_29  : Subtable FF0 58 :=
  subtableFromMLE (fun x => 1*(x[57] + x[28] - x[57]*x[28]) + 2*(x[56] + x[27] - x[56]*x[27]) + 4*(x[55] + x[26] - x[55]*x[26]) + 8*(x[54] + x[25] - x[54]*x[25]) + 16*(x[53] + x[24] - x[53]*x[24]) + 32*(x[52] + x[23] - x[52]*x[23]) + 64*(x[51] + x[22] - x[51]*x[22]) + 128*(x[50] + x[21] - x[50]*x[21]) + 256*(x[49] + x[20] - x[49]*x[20]) + 512*(x[48] + x[19] - x[48]*x[19]) + 1024*(x[47] + x[18] - x[47]*x[18]) + 2048*(x[46] + x[17] - x[46]*x[17]) + 4096*(x[45] + x[16] - x[45]*x[16]) + 8192*(x[44] + x[15] - x[44]*x[15]) + 16384*(x[43] + x[14] - x[43]*x[14]) + 32768*(x[42] + x[13] - x[42]*x[13]) + 65536*(x[41] + x[12] - x[41]*x[12]) + 131072*(x[40] + x[11] - x[40]*x[11]) + 262144*(x[39] + x[10] - x[39]*x[10]) + 524288*(x[38] + x[9] - x[38]*x[9]) + 1048576*(x[37] + x[8] - x[37]*x[8]) + 2097152*(x[36] + x[7] - x[36]*x[7]) + 4194304*(x[35] + x[6] - x[35]*x[6]) + 8388608*(x[34] + x[5] - x[34]*x[5]) + 16777216*(x[33] + x[4] - x[33]*x[4]) + 33554432*(x[32] + x[3] - x[32]*x[3]) + 67108864*(x[31] + x[2] - x[31]*x[2]) + 134217728*(x[30] + x[1] - x[30]*x[1]) + 268435456*(x[29] + x[0] - x[29]*x[0]))

lemma or_mle_29_chunk
  (bv1 bv2 : BitVec 29)
  (fv1 fv2 : Vector FF0 29) :
  some bvoutput = BVModEq.map_f_to_bv 29 foutput ->
  some (BVModEq.bool_to_bv 29 bv1[28]) = BVModEq.map_f_to_bv 29 fv1[0]  ->
  some (BVModEq.bool_to_bv 29 bv1[27]) = BVModEq.map_f_to_bv 29 fv1[1]  ->
  some (BVModEq.bool_to_bv 29 bv1[26]) = BVModEq.map_f_to_bv 29 fv1[2]  ->
  some (BVModEq.bool_to_bv 29 bv1[25]) = BVModEq.map_f_to_bv 29 fv1[3]  ->
  some (BVModEq.bool_to_bv 29 bv1[24]) = BVModEq.map_f_to_bv 29 fv1[4]  ->
  some (BVModEq.bool_to_bv 29 bv1[23]) = BVModEq.map_f_to_bv 29 fv1[5]  ->
  some (BVModEq.bool_to_bv 29 bv1[22]) = BVModEq.map_f_to_bv 29 fv1[6]  ->
  some (BVModEq.bool_to_bv 29 bv1[21]) = BVModEq.map_f_to_bv 29 fv1[7]  ->
  some (BVModEq.bool_to_bv 29 bv1[20]) = BVModEq.map_f_to_bv 29 fv1[8]  ->
  some (BVModEq.bool_to_bv 29 bv1[19]) = BVModEq.map_f_to_bv 29 fv1[9]  ->
  some (BVModEq.bool_to_bv 29 bv1[18]) = BVModEq.map_f_to_bv 29 fv1[10]  ->
  some (BVModEq.bool_to_bv 29 bv1[17]) = BVModEq.map_f_to_bv 29 fv1[11]  ->
  some (BVModEq.bool_to_bv 29 bv1[16]) = BVModEq.map_f_to_bv 29 fv1[12]  ->
  some (BVModEq.bool_to_bv 29 bv1[15]) = BVModEq.map_f_to_bv 29 fv1[13]  ->
  some (BVModEq.bool_to_bv 29 bv1[14]) = BVModEq.map_f_to_bv 29 fv1[14]  ->
  some (BVModEq.bool_to_bv 29 bv1[13]) = BVModEq.map_f_to_bv 29 fv1[15]  ->
  some (BVModEq.bool_to_bv 29 bv1[12]) = BVModEq.map_f_to_bv 29 fv1[16]  ->
  some (BVModEq.bool_to_bv 29 bv1[11]) = BVModEq.map_f_to_bv 29 fv1[17]  ->
  some (BVModEq.bool_to_bv 29 bv1[10]) = BVModEq.map_f_to_bv 29 fv1[18]  ->
  some (BVModEq.bool_to_bv 29 bv1[9]) = BVModEq.map_f_to_bv 29 fv1[19]  ->
  some (BVModEq.bool_to_bv 29 bv1[8]) = BVModEq.map_f_to_bv 29 fv1[20]  ->
  some (BVModEq.bool_to_bv 29 bv1[7]) = BVModEq.map_f_to_bv 29 fv1[21]  ->
  some (BVModEq.bool_to_bv 29 bv1[6]) = BVModEq.map_f_to_bv 29 fv1[22]  ->
  some (BVModEq.bool_to_bv 29 bv1[5]) = BVModEq.map_f_to_bv 29 fv1[23]  ->
  some (BVModEq.bool_to_bv 29 bv1[4]) = BVModEq.map_f_to_bv 29 fv1[24]  ->
  some (BVModEq.bool_to_bv 29 bv1[3]) = BVModEq.map_f_to_bv 29 fv1[25]  ->
  some (BVModEq.bool_to_bv 29 bv1[2]) = BVModEq.map_f_to_bv 29 fv1[26]  ->
  some (BVModEq.bool_to_bv 29 bv1[1]) = BVModEq.map_f_to_bv 29 fv1[27]  ->
  some (BVModEq.bool_to_bv 29 bv1[0]) = BVModEq.map_f_to_bv 29 fv1[28]  ->
  some (BVModEq.bool_to_bv 29 bv2[28]) = BVModEq.map_f_to_bv 29 fv2[0]  ->
  some (BVModEq.bool_to_bv 29 bv2[27]) = BVModEq.map_f_to_bv 29 fv2[1]  ->
  some (BVModEq.bool_to_bv 29 bv2[26]) = BVModEq.map_f_to_bv 29 fv2[2]  ->
  some (BVModEq.bool_to_bv 29 bv2[25]) = BVModEq.map_f_to_bv 29 fv2[3]  ->
  some (BVModEq.bool_to_bv 29 bv2[24]) = BVModEq.map_f_to_bv 29 fv2[4]  ->
  some (BVModEq.bool_to_bv 29 bv2[23]) = BVModEq.map_f_to_bv 29 fv2[5]  ->
  some (BVModEq.bool_to_bv 29 bv2[22]) = BVModEq.map_f_to_bv 29 fv2[6]  ->
  some (BVModEq.bool_to_bv 29 bv2[21]) = BVModEq.map_f_to_bv 29 fv2[7]  ->
  some (BVModEq.bool_to_bv 29 bv2[20]) = BVModEq.map_f_to_bv 29 fv2[8]  ->
  some (BVModEq.bool_to_bv 29 bv2[19]) = BVModEq.map_f_to_bv 29 fv2[9]  ->
  some (BVModEq.bool_to_bv 29 bv2[18]) = BVModEq.map_f_to_bv 29 fv2[10]  ->
  some (BVModEq.bool_to_bv 29 bv2[17]) = BVModEq.map_f_to_bv 29 fv2[11]  ->
  some (BVModEq.bool_to_bv 29 bv2[16]) = BVModEq.map_f_to_bv 29 fv2[12]  ->
  some (BVModEq.bool_to_bv 29 bv2[15]) = BVModEq.map_f_to_bv 29 fv2[13]  ->
  some (BVModEq.bool_to_bv 29 bv2[14]) = BVModEq.map_f_to_bv 29 fv2[14]  ->
  some (BVModEq.bool_to_bv 29 bv2[13]) = BVModEq.map_f_to_bv 29 fv2[15]  ->
  some (BVModEq.bool_to_bv 29 bv2[12]) = BVModEq.map_f_to_bv 29 fv2[16]  ->
  some (BVModEq.bool_to_bv 29 bv2[11]) = BVModEq.map_f_to_bv 29 fv2[17]  ->
  some (BVModEq.bool_to_bv 29 bv2[10]) = BVModEq.map_f_to_bv 29 fv2[18]  ->
  some (BVModEq.bool_to_bv 29 bv2[9]) = BVModEq.map_f_to_bv 29 fv2[19]  ->
  some (BVModEq.bool_to_bv 29 bv2[8]) = BVModEq.map_f_to_bv 29 fv2[20]  ->
  some (BVModEq.bool_to_bv 29 bv2[7]) = BVModEq.map_f_to_bv 29 fv2[21]  ->
  some (BVModEq.bool_to_bv 29 bv2[6]) = BVModEq.map_f_to_bv 29 fv2[22]  ->
  some (BVModEq.bool_to_bv 29 bv2[5]) = BVModEq.map_f_to_bv 29 fv2[23]  ->
  some (BVModEq.bool_to_bv 29 bv2[4]) = BVModEq.map_f_to_bv 29 fv2[24]  ->
  some (BVModEq.bool_to_bv 29 bv2[3]) = BVModEq.map_f_to_bv 29 fv2[25]  ->
  some (BVModEq.bool_to_bv 29 bv2[2]) = BVModEq.map_f_to_bv 29 fv2[26]  ->
  some (BVModEq.bool_to_bv 29 bv2[1]) = BVModEq.map_f_to_bv 29 fv2[27]  ->
  some (BVModEq.bool_to_bv 29 bv2[0]) = BVModEq.map_f_to_bv 29 fv2[28]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_29 (Vector.append fv1 fv2))
:= by
  unfold OR_29
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
