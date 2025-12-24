-- AUTO-GENERATED — DO NOT EDIT


def OR_18  : Subtable FF0 36 :=
  subtableFromMLE (fun x => 1*(x[35] + x[17] - x[35]*x[17]) + 2*(x[34] + x[16] - x[34]*x[16]) + 4*(x[33] + x[15] - x[33]*x[15]) + 8*(x[32] + x[14] - x[32]*x[14]) + 16*(x[31] + x[13] - x[31]*x[13]) + 32*(x[30] + x[12] - x[30]*x[12]) + 64*(x[29] + x[11] - x[29]*x[11]) + 128*(x[28] + x[10] - x[28]*x[10]) + 256*(x[27] + x[9] - x[27]*x[9]) + 512*(x[26] + x[8] - x[26]*x[8]) + 1024*(x[25] + x[7] - x[25]*x[7]) + 2048*(x[24] + x[6] - x[24]*x[6]) + 4096*(x[23] + x[5] - x[23]*x[5]) + 8192*(x[22] + x[4] - x[22]*x[4]) + 16384*(x[21] + x[3] - x[21]*x[3]) + 32768*(x[20] + x[2] - x[20]*x[2]) + 65536*(x[19] + x[1] - x[19]*x[1]) + 131072*(x[18] + x[0] - x[18]*x[0]))

lemma or_mle_18_chunk
  (bv1 bv2 : BitVec 18)
  (fv1 fv2 : Vector FF0 18) :
  some bvoutput = BVModEq.map_f_to_bv 18 foutput ->
  some (BVModEq.bool_to_bv 18 bv1[17]) = BVModEq.map_f_to_bv 18 fv1[0]  ->
  some (BVModEq.bool_to_bv 18 bv1[16]) = BVModEq.map_f_to_bv 18 fv1[1]  ->
  some (BVModEq.bool_to_bv 18 bv1[15]) = BVModEq.map_f_to_bv 18 fv1[2]  ->
  some (BVModEq.bool_to_bv 18 bv1[14]) = BVModEq.map_f_to_bv 18 fv1[3]  ->
  some (BVModEq.bool_to_bv 18 bv1[13]) = BVModEq.map_f_to_bv 18 fv1[4]  ->
  some (BVModEq.bool_to_bv 18 bv1[12]) = BVModEq.map_f_to_bv 18 fv1[5]  ->
  some (BVModEq.bool_to_bv 18 bv1[11]) = BVModEq.map_f_to_bv 18 fv1[6]  ->
  some (BVModEq.bool_to_bv 18 bv1[10]) = BVModEq.map_f_to_bv 18 fv1[7]  ->
  some (BVModEq.bool_to_bv 18 bv1[9]) = BVModEq.map_f_to_bv 18 fv1[8]  ->
  some (BVModEq.bool_to_bv 18 bv1[8]) = BVModEq.map_f_to_bv 18 fv1[9]  ->
  some (BVModEq.bool_to_bv 18 bv1[7]) = BVModEq.map_f_to_bv 18 fv1[10]  ->
  some (BVModEq.bool_to_bv 18 bv1[6]) = BVModEq.map_f_to_bv 18 fv1[11]  ->
  some (BVModEq.bool_to_bv 18 bv1[5]) = BVModEq.map_f_to_bv 18 fv1[12]  ->
  some (BVModEq.bool_to_bv 18 bv1[4]) = BVModEq.map_f_to_bv 18 fv1[13]  ->
  some (BVModEq.bool_to_bv 18 bv1[3]) = BVModEq.map_f_to_bv 18 fv1[14]  ->
  some (BVModEq.bool_to_bv 18 bv1[2]) = BVModEq.map_f_to_bv 18 fv1[15]  ->
  some (BVModEq.bool_to_bv 18 bv1[1]) = BVModEq.map_f_to_bv 18 fv1[16]  ->
  some (BVModEq.bool_to_bv 18 bv1[0]) = BVModEq.map_f_to_bv 18 fv1[17]  ->
  some (BVModEq.bool_to_bv 18 bv2[17]) = BVModEq.map_f_to_bv 18 fv2[0]  ->
  some (BVModEq.bool_to_bv 18 bv2[16]) = BVModEq.map_f_to_bv 18 fv2[1]  ->
  some (BVModEq.bool_to_bv 18 bv2[15]) = BVModEq.map_f_to_bv 18 fv2[2]  ->
  some (BVModEq.bool_to_bv 18 bv2[14]) = BVModEq.map_f_to_bv 18 fv2[3]  ->
  some (BVModEq.bool_to_bv 18 bv2[13]) = BVModEq.map_f_to_bv 18 fv2[4]  ->
  some (BVModEq.bool_to_bv 18 bv2[12]) = BVModEq.map_f_to_bv 18 fv2[5]  ->
  some (BVModEq.bool_to_bv 18 bv2[11]) = BVModEq.map_f_to_bv 18 fv2[6]  ->
  some (BVModEq.bool_to_bv 18 bv2[10]) = BVModEq.map_f_to_bv 18 fv2[7]  ->
  some (BVModEq.bool_to_bv 18 bv2[9]) = BVModEq.map_f_to_bv 18 fv2[8]  ->
  some (BVModEq.bool_to_bv 18 bv2[8]) = BVModEq.map_f_to_bv 18 fv2[9]  ->
  some (BVModEq.bool_to_bv 18 bv2[7]) = BVModEq.map_f_to_bv 18 fv2[10]  ->
  some (BVModEq.bool_to_bv 18 bv2[6]) = BVModEq.map_f_to_bv 18 fv2[11]  ->
  some (BVModEq.bool_to_bv 18 bv2[5]) = BVModEq.map_f_to_bv 18 fv2[12]  ->
  some (BVModEq.bool_to_bv 18 bv2[4]) = BVModEq.map_f_to_bv 18 fv2[13]  ->
  some (BVModEq.bool_to_bv 18 bv2[3]) = BVModEq.map_f_to_bv 18 fv2[14]  ->
  some (BVModEq.bool_to_bv 18 bv2[2]) = BVModEq.map_f_to_bv 18 fv2[15]  ->
  some (BVModEq.bool_to_bv 18 bv2[1]) = BVModEq.map_f_to_bv 18 fv2[16]  ->
  some (BVModEq.bool_to_bv 18 bv2[0]) = BVModEq.map_f_to_bv 18 fv2[17]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_18 (Vector.append fv1 fv2))
:= by
  unfold OR_18
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
