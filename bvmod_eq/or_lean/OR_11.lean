-- AUTO-GENERATED — DO NOT EDIT


def OR_11  : Subtable FF0 22 :=
  subtableFromMLE (fun x => 1*(x[21] + x[10] - x[21]*x[10]) + 2*(x[20] + x[9] - x[20]*x[9]) + 4*(x[19] + x[8] - x[19]*x[8]) + 8*(x[18] + x[7] - x[18]*x[7]) + 16*(x[17] + x[6] - x[17]*x[6]) + 32*(x[16] + x[5] - x[16]*x[5]) + 64*(x[15] + x[4] - x[15]*x[4]) + 128*(x[14] + x[3] - x[14]*x[3]) + 256*(x[13] + x[2] - x[13]*x[2]) + 512*(x[12] + x[1] - x[12]*x[1]) + 1024*(x[11] + x[0] - x[11]*x[0]))

lemma or_mle_11_chunk
  (bv1 bv2 : BitVec 11)
  (fv1 fv2 : Vector FF0 11) :
  some bvoutput = BVModEq.map_f_to_bv 11 foutput ->
  some (BVModEq.bool_to_bv 11 bv1[10]) = BVModEq.map_f_to_bv 11 fv1[0]  ->
  some (BVModEq.bool_to_bv 11 bv1[9]) = BVModEq.map_f_to_bv 11 fv1[1]  ->
  some (BVModEq.bool_to_bv 11 bv1[8]) = BVModEq.map_f_to_bv 11 fv1[2]  ->
  some (BVModEq.bool_to_bv 11 bv1[7]) = BVModEq.map_f_to_bv 11 fv1[3]  ->
  some (BVModEq.bool_to_bv 11 bv1[6]) = BVModEq.map_f_to_bv 11 fv1[4]  ->
  some (BVModEq.bool_to_bv 11 bv1[5]) = BVModEq.map_f_to_bv 11 fv1[5]  ->
  some (BVModEq.bool_to_bv 11 bv1[4]) = BVModEq.map_f_to_bv 11 fv1[6]  ->
  some (BVModEq.bool_to_bv 11 bv1[3]) = BVModEq.map_f_to_bv 11 fv1[7]  ->
  some (BVModEq.bool_to_bv 11 bv1[2]) = BVModEq.map_f_to_bv 11 fv1[8]  ->
  some (BVModEq.bool_to_bv 11 bv1[1]) = BVModEq.map_f_to_bv 11 fv1[9]  ->
  some (BVModEq.bool_to_bv 11 bv1[0]) = BVModEq.map_f_to_bv 11 fv1[10]  ->
  some (BVModEq.bool_to_bv 11 bv2[10]) = BVModEq.map_f_to_bv 11 fv2[0]  ->
  some (BVModEq.bool_to_bv 11 bv2[9]) = BVModEq.map_f_to_bv 11 fv2[1]  ->
  some (BVModEq.bool_to_bv 11 bv2[8]) = BVModEq.map_f_to_bv 11 fv2[2]  ->
  some (BVModEq.bool_to_bv 11 bv2[7]) = BVModEq.map_f_to_bv 11 fv2[3]  ->
  some (BVModEq.bool_to_bv 11 bv2[6]) = BVModEq.map_f_to_bv 11 fv2[4]  ->
  some (BVModEq.bool_to_bv 11 bv2[5]) = BVModEq.map_f_to_bv 11 fv2[5]  ->
  some (BVModEq.bool_to_bv 11 bv2[4]) = BVModEq.map_f_to_bv 11 fv2[6]  ->
  some (BVModEq.bool_to_bv 11 bv2[3]) = BVModEq.map_f_to_bv 11 fv2[7]  ->
  some (BVModEq.bool_to_bv 11 bv2[2]) = BVModEq.map_f_to_bv 11 fv2[8]  ->
  some (BVModEq.bool_to_bv 11 bv2[1]) = BVModEq.map_f_to_bv 11 fv2[9]  ->
  some (BVModEq.bool_to_bv 11 bv2[0]) = BVModEq.map_f_to_bv 11 fv2[10]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_11 (Vector.append fv1 fv2))
:= by
  unfold OR_11
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
