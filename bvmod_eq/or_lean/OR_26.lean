-- AUTO-GENERATED — DO NOT EDIT


def OR_26  : Subtable FF0 52 :=
  subtableFromMLE (fun x => 1*(x[51] + x[25] - x[51]*x[25]) + 2*(x[50] + x[24] - x[50]*x[24]) + 4*(x[49] + x[23] - x[49]*x[23]) + 8*(x[48] + x[22] - x[48]*x[22]) + 16*(x[47] + x[21] - x[47]*x[21]) + 32*(x[46] + x[20] - x[46]*x[20]) + 64*(x[45] + x[19] - x[45]*x[19]) + 128*(x[44] + x[18] - x[44]*x[18]) + 256*(x[43] + x[17] - x[43]*x[17]) + 512*(x[42] + x[16] - x[42]*x[16]) + 1024*(x[41] + x[15] - x[41]*x[15]) + 2048*(x[40] + x[14] - x[40]*x[14]) + 4096*(x[39] + x[13] - x[39]*x[13]) + 8192*(x[38] + x[12] - x[38]*x[12]) + 16384*(x[37] + x[11] - x[37]*x[11]) + 32768*(x[36] + x[10] - x[36]*x[10]) + 65536*(x[35] + x[9] - x[35]*x[9]) + 131072*(x[34] + x[8] - x[34]*x[8]) + 262144*(x[33] + x[7] - x[33]*x[7]) + 524288*(x[32] + x[6] - x[32]*x[6]) + 1048576*(x[31] + x[5] - x[31]*x[5]) + 2097152*(x[30] + x[4] - x[30]*x[4]) + 4194304*(x[29] + x[3] - x[29]*x[3]) + 8388608*(x[28] + x[2] - x[28]*x[2]) + 16777216*(x[27] + x[1] - x[27]*x[1]) + 33554432*(x[26] + x[0] - x[26]*x[0]))

lemma or_mle_26_chunk
  (bv1 bv2 : BitVec 26)
  (fv1 fv2 : Vector FF0 26) :
  some bvoutput = BVModEq.map_f_to_bv 26 foutput ->
  some (BVModEq.bool_to_bv 26 bv1[25]) = BVModEq.map_f_to_bv 26 fv1[0]  ->
  some (BVModEq.bool_to_bv 26 bv1[24]) = BVModEq.map_f_to_bv 26 fv1[1]  ->
  some (BVModEq.bool_to_bv 26 bv1[23]) = BVModEq.map_f_to_bv 26 fv1[2]  ->
  some (BVModEq.bool_to_bv 26 bv1[22]) = BVModEq.map_f_to_bv 26 fv1[3]  ->
  some (BVModEq.bool_to_bv 26 bv1[21]) = BVModEq.map_f_to_bv 26 fv1[4]  ->
  some (BVModEq.bool_to_bv 26 bv1[20]) = BVModEq.map_f_to_bv 26 fv1[5]  ->
  some (BVModEq.bool_to_bv 26 bv1[19]) = BVModEq.map_f_to_bv 26 fv1[6]  ->
  some (BVModEq.bool_to_bv 26 bv1[18]) = BVModEq.map_f_to_bv 26 fv1[7]  ->
  some (BVModEq.bool_to_bv 26 bv1[17]) = BVModEq.map_f_to_bv 26 fv1[8]  ->
  some (BVModEq.bool_to_bv 26 bv1[16]) = BVModEq.map_f_to_bv 26 fv1[9]  ->
  some (BVModEq.bool_to_bv 26 bv1[15]) = BVModEq.map_f_to_bv 26 fv1[10]  ->
  some (BVModEq.bool_to_bv 26 bv1[14]) = BVModEq.map_f_to_bv 26 fv1[11]  ->
  some (BVModEq.bool_to_bv 26 bv1[13]) = BVModEq.map_f_to_bv 26 fv1[12]  ->
  some (BVModEq.bool_to_bv 26 bv1[12]) = BVModEq.map_f_to_bv 26 fv1[13]  ->
  some (BVModEq.bool_to_bv 26 bv1[11]) = BVModEq.map_f_to_bv 26 fv1[14]  ->
  some (BVModEq.bool_to_bv 26 bv1[10]) = BVModEq.map_f_to_bv 26 fv1[15]  ->
  some (BVModEq.bool_to_bv 26 bv1[9]) = BVModEq.map_f_to_bv 26 fv1[16]  ->
  some (BVModEq.bool_to_bv 26 bv1[8]) = BVModEq.map_f_to_bv 26 fv1[17]  ->
  some (BVModEq.bool_to_bv 26 bv1[7]) = BVModEq.map_f_to_bv 26 fv1[18]  ->
  some (BVModEq.bool_to_bv 26 bv1[6]) = BVModEq.map_f_to_bv 26 fv1[19]  ->
  some (BVModEq.bool_to_bv 26 bv1[5]) = BVModEq.map_f_to_bv 26 fv1[20]  ->
  some (BVModEq.bool_to_bv 26 bv1[4]) = BVModEq.map_f_to_bv 26 fv1[21]  ->
  some (BVModEq.bool_to_bv 26 bv1[3]) = BVModEq.map_f_to_bv 26 fv1[22]  ->
  some (BVModEq.bool_to_bv 26 bv1[2]) = BVModEq.map_f_to_bv 26 fv1[23]  ->
  some (BVModEq.bool_to_bv 26 bv1[1]) = BVModEq.map_f_to_bv 26 fv1[24]  ->
  some (BVModEq.bool_to_bv 26 bv1[0]) = BVModEq.map_f_to_bv 26 fv1[25]  ->
  some (BVModEq.bool_to_bv 26 bv2[25]) = BVModEq.map_f_to_bv 26 fv2[0]  ->
  some (BVModEq.bool_to_bv 26 bv2[24]) = BVModEq.map_f_to_bv 26 fv2[1]  ->
  some (BVModEq.bool_to_bv 26 bv2[23]) = BVModEq.map_f_to_bv 26 fv2[2]  ->
  some (BVModEq.bool_to_bv 26 bv2[22]) = BVModEq.map_f_to_bv 26 fv2[3]  ->
  some (BVModEq.bool_to_bv 26 bv2[21]) = BVModEq.map_f_to_bv 26 fv2[4]  ->
  some (BVModEq.bool_to_bv 26 bv2[20]) = BVModEq.map_f_to_bv 26 fv2[5]  ->
  some (BVModEq.bool_to_bv 26 bv2[19]) = BVModEq.map_f_to_bv 26 fv2[6]  ->
  some (BVModEq.bool_to_bv 26 bv2[18]) = BVModEq.map_f_to_bv 26 fv2[7]  ->
  some (BVModEq.bool_to_bv 26 bv2[17]) = BVModEq.map_f_to_bv 26 fv2[8]  ->
  some (BVModEq.bool_to_bv 26 bv2[16]) = BVModEq.map_f_to_bv 26 fv2[9]  ->
  some (BVModEq.bool_to_bv 26 bv2[15]) = BVModEq.map_f_to_bv 26 fv2[10]  ->
  some (BVModEq.bool_to_bv 26 bv2[14]) = BVModEq.map_f_to_bv 26 fv2[11]  ->
  some (BVModEq.bool_to_bv 26 bv2[13]) = BVModEq.map_f_to_bv 26 fv2[12]  ->
  some (BVModEq.bool_to_bv 26 bv2[12]) = BVModEq.map_f_to_bv 26 fv2[13]  ->
  some (BVModEq.bool_to_bv 26 bv2[11]) = BVModEq.map_f_to_bv 26 fv2[14]  ->
  some (BVModEq.bool_to_bv 26 bv2[10]) = BVModEq.map_f_to_bv 26 fv2[15]  ->
  some (BVModEq.bool_to_bv 26 bv2[9]) = BVModEq.map_f_to_bv 26 fv2[16]  ->
  some (BVModEq.bool_to_bv 26 bv2[8]) = BVModEq.map_f_to_bv 26 fv2[17]  ->
  some (BVModEq.bool_to_bv 26 bv2[7]) = BVModEq.map_f_to_bv 26 fv2[18]  ->
  some (BVModEq.bool_to_bv 26 bv2[6]) = BVModEq.map_f_to_bv 26 fv2[19]  ->
  some (BVModEq.bool_to_bv 26 bv2[5]) = BVModEq.map_f_to_bv 26 fv2[20]  ->
  some (BVModEq.bool_to_bv 26 bv2[4]) = BVModEq.map_f_to_bv 26 fv2[21]  ->
  some (BVModEq.bool_to_bv 26 bv2[3]) = BVModEq.map_f_to_bv 26 fv2[22]  ->
  some (BVModEq.bool_to_bv 26 bv2[2]) = BVModEq.map_f_to_bv 26 fv2[23]  ->
  some (BVModEq.bool_to_bv 26 bv2[1]) = BVModEq.map_f_to_bv 26 fv2[24]  ->
  some (BVModEq.bool_to_bv 26 bv2[0]) = BVModEq.map_f_to_bv 26 fv2[25]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_26 (Vector.append fv1 fv2))
:= by
  unfold OR_26
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
