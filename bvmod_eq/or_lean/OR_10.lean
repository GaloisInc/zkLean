-- AUTO-GENERATED — DO NOT EDIT


def OR_10  : Subtable FF0 20 :=
  subtableFromMLE (fun x => 1*(x[19] + x[9] - x[19]*x[9]) + 2*(x[18] + x[8] - x[18]*x[8]) + 4*(x[17] + x[7] - x[17]*x[7]) + 8*(x[16] + x[6] - x[16]*x[6]) + 16*(x[15] + x[5] - x[15]*x[5]) + 32*(x[14] + x[4] - x[14]*x[4]) + 64*(x[13] + x[3] - x[13]*x[3]) + 128*(x[12] + x[2] - x[12]*x[2]) + 256*(x[11] + x[1] - x[11]*x[1]) + 512*(x[10] + x[0] - x[10]*x[0]))

lemma or_mle_10_chunk
  (bv1 bv2 : BitVec 10)
  (fv1 fv2 : Vector FF0 10) :
  some bvoutput = BVModEq.map_f_to_bv 10 foutput ->
  some (BVModEq.bool_to_bv 10 bv1[9]) = BVModEq.map_f_to_bv 10 fv1[0]  ->
  some (BVModEq.bool_to_bv 10 bv1[8]) = BVModEq.map_f_to_bv 10 fv1[1]  ->
  some (BVModEq.bool_to_bv 10 bv1[7]) = BVModEq.map_f_to_bv 10 fv1[2]  ->
  some (BVModEq.bool_to_bv 10 bv1[6]) = BVModEq.map_f_to_bv 10 fv1[3]  ->
  some (BVModEq.bool_to_bv 10 bv1[5]) = BVModEq.map_f_to_bv 10 fv1[4]  ->
  some (BVModEq.bool_to_bv 10 bv1[4]) = BVModEq.map_f_to_bv 10 fv1[5]  ->
  some (BVModEq.bool_to_bv 10 bv1[3]) = BVModEq.map_f_to_bv 10 fv1[6]  ->
  some (BVModEq.bool_to_bv 10 bv1[2]) = BVModEq.map_f_to_bv 10 fv1[7]  ->
  some (BVModEq.bool_to_bv 10 bv1[1]) = BVModEq.map_f_to_bv 10 fv1[8]  ->
  some (BVModEq.bool_to_bv 10 bv1[0]) = BVModEq.map_f_to_bv 10 fv1[9]  ->
  some (BVModEq.bool_to_bv 10 bv2[9]) = BVModEq.map_f_to_bv 10 fv2[0]  ->
  some (BVModEq.bool_to_bv 10 bv2[8]) = BVModEq.map_f_to_bv 10 fv2[1]  ->
  some (BVModEq.bool_to_bv 10 bv2[7]) = BVModEq.map_f_to_bv 10 fv2[2]  ->
  some (BVModEq.bool_to_bv 10 bv2[6]) = BVModEq.map_f_to_bv 10 fv2[3]  ->
  some (BVModEq.bool_to_bv 10 bv2[5]) = BVModEq.map_f_to_bv 10 fv2[4]  ->
  some (BVModEq.bool_to_bv 10 bv2[4]) = BVModEq.map_f_to_bv 10 fv2[5]  ->
  some (BVModEq.bool_to_bv 10 bv2[3]) = BVModEq.map_f_to_bv 10 fv2[6]  ->
  some (BVModEq.bool_to_bv 10 bv2[2]) = BVModEq.map_f_to_bv 10 fv2[7]  ->
  some (BVModEq.bool_to_bv 10 bv2[1]) = BVModEq.map_f_to_bv 10 fv2[8]  ->
  some (BVModEq.bool_to_bv 10 bv2[0]) = BVModEq.map_f_to_bv 10 fv2[9]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_10 (Vector.append fv1 fv2))
:= by
  unfold OR_10
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
