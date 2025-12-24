-- AUTO-GENERATED — DO NOT EDIT


def OR_16  : Subtable FF0 32 :=
  subtableFromMLE (fun x => 1*(x[31] + x[15] - x[31]*x[15]) + 2*(x[30] + x[14] - x[30]*x[14]) + 4*(x[29] + x[13] - x[29]*x[13]) + 8*(x[28] + x[12] - x[28]*x[12]) + 16*(x[27] + x[11] - x[27]*x[11]) + 32*(x[26] + x[10] - x[26]*x[10]) + 64*(x[25] + x[9] - x[25]*x[9]) + 128*(x[24] + x[8] - x[24]*x[8]) + 256*(x[23] + x[7] - x[23]*x[7]) + 512*(x[22] + x[6] - x[22]*x[6]) + 1024*(x[21] + x[5] - x[21]*x[5]) + 2048*(x[20] + x[4] - x[20]*x[4]) + 4096*(x[19] + x[3] - x[19]*x[3]) + 8192*(x[18] + x[2] - x[18]*x[2]) + 16384*(x[17] + x[1] - x[17]*x[1]) + 32768*(x[16] + x[0] - x[16]*x[0]))

lemma or_mle_16_chunk
  (bv1 bv2 : BitVec 16)
  (fv1 fv2 : Vector FF0 16) :
  some bvoutput = BVModEq.map_f_to_bv 16 foutput ->
  some (BVModEq.bool_to_bv 16 bv1[15]) = BVModEq.map_f_to_bv 16 fv1[0]  ->
  some (BVModEq.bool_to_bv 16 bv1[14]) = BVModEq.map_f_to_bv 16 fv1[1]  ->
  some (BVModEq.bool_to_bv 16 bv1[13]) = BVModEq.map_f_to_bv 16 fv1[2]  ->
  some (BVModEq.bool_to_bv 16 bv1[12]) = BVModEq.map_f_to_bv 16 fv1[3]  ->
  some (BVModEq.bool_to_bv 16 bv1[11]) = BVModEq.map_f_to_bv 16 fv1[4]  ->
  some (BVModEq.bool_to_bv 16 bv1[10]) = BVModEq.map_f_to_bv 16 fv1[5]  ->
  some (BVModEq.bool_to_bv 16 bv1[9]) = BVModEq.map_f_to_bv 16 fv1[6]  ->
  some (BVModEq.bool_to_bv 16 bv1[8]) = BVModEq.map_f_to_bv 16 fv1[7]  ->
  some (BVModEq.bool_to_bv 16 bv1[7]) = BVModEq.map_f_to_bv 16 fv1[8]  ->
  some (BVModEq.bool_to_bv 16 bv1[6]) = BVModEq.map_f_to_bv 16 fv1[9]  ->
  some (BVModEq.bool_to_bv 16 bv1[5]) = BVModEq.map_f_to_bv 16 fv1[10]  ->
  some (BVModEq.bool_to_bv 16 bv1[4]) = BVModEq.map_f_to_bv 16 fv1[11]  ->
  some (BVModEq.bool_to_bv 16 bv1[3]) = BVModEq.map_f_to_bv 16 fv1[12]  ->
  some (BVModEq.bool_to_bv 16 bv1[2]) = BVModEq.map_f_to_bv 16 fv1[13]  ->
  some (BVModEq.bool_to_bv 16 bv1[1]) = BVModEq.map_f_to_bv 16 fv1[14]  ->
  some (BVModEq.bool_to_bv 16 bv1[0]) = BVModEq.map_f_to_bv 16 fv1[15]  ->
  some (BVModEq.bool_to_bv 16 bv2[15]) = BVModEq.map_f_to_bv 16 fv2[0]  ->
  some (BVModEq.bool_to_bv 16 bv2[14]) = BVModEq.map_f_to_bv 16 fv2[1]  ->
  some (BVModEq.bool_to_bv 16 bv2[13]) = BVModEq.map_f_to_bv 16 fv2[2]  ->
  some (BVModEq.bool_to_bv 16 bv2[12]) = BVModEq.map_f_to_bv 16 fv2[3]  ->
  some (BVModEq.bool_to_bv 16 bv2[11]) = BVModEq.map_f_to_bv 16 fv2[4]  ->
  some (BVModEq.bool_to_bv 16 bv2[10]) = BVModEq.map_f_to_bv 16 fv2[5]  ->
  some (BVModEq.bool_to_bv 16 bv2[9]) = BVModEq.map_f_to_bv 16 fv2[6]  ->
  some (BVModEq.bool_to_bv 16 bv2[8]) = BVModEq.map_f_to_bv 16 fv2[7]  ->
  some (BVModEq.bool_to_bv 16 bv2[7]) = BVModEq.map_f_to_bv 16 fv2[8]  ->
  some (BVModEq.bool_to_bv 16 bv2[6]) = BVModEq.map_f_to_bv 16 fv2[9]  ->
  some (BVModEq.bool_to_bv 16 bv2[5]) = BVModEq.map_f_to_bv 16 fv2[10]  ->
  some (BVModEq.bool_to_bv 16 bv2[4]) = BVModEq.map_f_to_bv 16 fv2[11]  ->
  some (BVModEq.bool_to_bv 16 bv2[3]) = BVModEq.map_f_to_bv 16 fv2[12]  ->
  some (BVModEq.bool_to_bv 16 bv2[2]) = BVModEq.map_f_to_bv 16 fv2[13]  ->
  some (BVModEq.bool_to_bv 16 bv2[1]) = BVModEq.map_f_to_bv 16 fv2[14]  ->
  some (BVModEq.bool_to_bv 16 bv2[0]) = BVModEq.map_f_to_bv 16 fv2[15]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_16 (Vector.append fv1 fv2))
:= by
  unfold OR_16
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
