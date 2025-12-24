-- AUTO-GENERATED — DO NOT EDIT


def OR_14  : Subtable FF0 28 :=
  subtableFromMLE (fun x => 1*(x[27] + x[13] - x[27]*x[13]) + 2*(x[26] + x[12] - x[26]*x[12]) + 4*(x[25] + x[11] - x[25]*x[11]) + 8*(x[24] + x[10] - x[24]*x[10]) + 16*(x[23] + x[9] - x[23]*x[9]) + 32*(x[22] + x[8] - x[22]*x[8]) + 64*(x[21] + x[7] - x[21]*x[7]) + 128*(x[20] + x[6] - x[20]*x[6]) + 256*(x[19] + x[5] - x[19]*x[5]) + 512*(x[18] + x[4] - x[18]*x[4]) + 1024*(x[17] + x[3] - x[17]*x[3]) + 2048*(x[16] + x[2] - x[16]*x[2]) + 4096*(x[15] + x[1] - x[15]*x[1]) + 8192*(x[14] + x[0] - x[14]*x[0]))

lemma or_mle_14_chunk
  (bv1 bv2 : BitVec 14)
  (fv1 fv2 : Vector FF0 14) :
  some bvoutput = BVModEq.map_f_to_bv 14 foutput ->
  some (BVModEq.bool_to_bv 14 bv1[13]) = BVModEq.map_f_to_bv 14 fv1[0]  ->
  some (BVModEq.bool_to_bv 14 bv1[12]) = BVModEq.map_f_to_bv 14 fv1[1]  ->
  some (BVModEq.bool_to_bv 14 bv1[11]) = BVModEq.map_f_to_bv 14 fv1[2]  ->
  some (BVModEq.bool_to_bv 14 bv1[10]) = BVModEq.map_f_to_bv 14 fv1[3]  ->
  some (BVModEq.bool_to_bv 14 bv1[9]) = BVModEq.map_f_to_bv 14 fv1[4]  ->
  some (BVModEq.bool_to_bv 14 bv1[8]) = BVModEq.map_f_to_bv 14 fv1[5]  ->
  some (BVModEq.bool_to_bv 14 bv1[7]) = BVModEq.map_f_to_bv 14 fv1[6]  ->
  some (BVModEq.bool_to_bv 14 bv1[6]) = BVModEq.map_f_to_bv 14 fv1[7]  ->
  some (BVModEq.bool_to_bv 14 bv1[5]) = BVModEq.map_f_to_bv 14 fv1[8]  ->
  some (BVModEq.bool_to_bv 14 bv1[4]) = BVModEq.map_f_to_bv 14 fv1[9]  ->
  some (BVModEq.bool_to_bv 14 bv1[3]) = BVModEq.map_f_to_bv 14 fv1[10]  ->
  some (BVModEq.bool_to_bv 14 bv1[2]) = BVModEq.map_f_to_bv 14 fv1[11]  ->
  some (BVModEq.bool_to_bv 14 bv1[1]) = BVModEq.map_f_to_bv 14 fv1[12]  ->
  some (BVModEq.bool_to_bv 14 bv1[0]) = BVModEq.map_f_to_bv 14 fv1[13]  ->
  some (BVModEq.bool_to_bv 14 bv2[13]) = BVModEq.map_f_to_bv 14 fv2[0]  ->
  some (BVModEq.bool_to_bv 14 bv2[12]) = BVModEq.map_f_to_bv 14 fv2[1]  ->
  some (BVModEq.bool_to_bv 14 bv2[11]) = BVModEq.map_f_to_bv 14 fv2[2]  ->
  some (BVModEq.bool_to_bv 14 bv2[10]) = BVModEq.map_f_to_bv 14 fv2[3]  ->
  some (BVModEq.bool_to_bv 14 bv2[9]) = BVModEq.map_f_to_bv 14 fv2[4]  ->
  some (BVModEq.bool_to_bv 14 bv2[8]) = BVModEq.map_f_to_bv 14 fv2[5]  ->
  some (BVModEq.bool_to_bv 14 bv2[7]) = BVModEq.map_f_to_bv 14 fv2[6]  ->
  some (BVModEq.bool_to_bv 14 bv2[6]) = BVModEq.map_f_to_bv 14 fv2[7]  ->
  some (BVModEq.bool_to_bv 14 bv2[5]) = BVModEq.map_f_to_bv 14 fv2[8]  ->
  some (BVModEq.bool_to_bv 14 bv2[4]) = BVModEq.map_f_to_bv 14 fv2[9]  ->
  some (BVModEq.bool_to_bv 14 bv2[3]) = BVModEq.map_f_to_bv 14 fv2[10]  ->
  some (BVModEq.bool_to_bv 14 bv2[2]) = BVModEq.map_f_to_bv 14 fv2[11]  ->
  some (BVModEq.bool_to_bv 14 bv2[1]) = BVModEq.map_f_to_bv 14 fv2[12]  ->
  some (BVModEq.bool_to_bv 14 bv2[0]) = BVModEq.map_f_to_bv 14 fv2[13]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_14 (Vector.append fv1 fv2))
:= by
  unfold OR_14
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
