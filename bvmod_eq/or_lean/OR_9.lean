-- AUTO-GENERATED — DO NOT EDIT


def OR_9  : Subtable FF0 18 :=
  subtableFromMLE (fun x => 1*(x[17] + x[8] - x[17]*x[8]) + 2*(x[16] + x[7] - x[16]*x[7]) + 4*(x[15] + x[6] - x[15]*x[6]) + 8*(x[14] + x[5] - x[14]*x[5]) + 16*(x[13] + x[4] - x[13]*x[4]) + 32*(x[12] + x[3] - x[12]*x[3]) + 64*(x[11] + x[2] - x[11]*x[2]) + 128*(x[10] + x[1] - x[10]*x[1]) + 256*(x[9] + x[0] - x[9]*x[0]))

lemma or_mle_9_chunk
  (bv1 bv2 : BitVec 9)
  (fv1 fv2 : Vector FF0 9) :
  some bvoutput = BVModEq.map_f_to_bv 9 foutput ->
  some (BVModEq.bool_to_bv 9 bv1[8]) = BVModEq.map_f_to_bv 9 fv1[0]  ->
  some (BVModEq.bool_to_bv 9 bv1[7]) = BVModEq.map_f_to_bv 9 fv1[1]  ->
  some (BVModEq.bool_to_bv 9 bv1[6]) = BVModEq.map_f_to_bv 9 fv1[2]  ->
  some (BVModEq.bool_to_bv 9 bv1[5]) = BVModEq.map_f_to_bv 9 fv1[3]  ->
  some (BVModEq.bool_to_bv 9 bv1[4]) = BVModEq.map_f_to_bv 9 fv1[4]  ->
  some (BVModEq.bool_to_bv 9 bv1[3]) = BVModEq.map_f_to_bv 9 fv1[5]  ->
  some (BVModEq.bool_to_bv 9 bv1[2]) = BVModEq.map_f_to_bv 9 fv1[6]  ->
  some (BVModEq.bool_to_bv 9 bv1[1]) = BVModEq.map_f_to_bv 9 fv1[7]  ->
  some (BVModEq.bool_to_bv 9 bv1[0]) = BVModEq.map_f_to_bv 9 fv1[8]  ->
  some (BVModEq.bool_to_bv 9 bv2[8]) = BVModEq.map_f_to_bv 9 fv2[0]  ->
  some (BVModEq.bool_to_bv 9 bv2[7]) = BVModEq.map_f_to_bv 9 fv2[1]  ->
  some (BVModEq.bool_to_bv 9 bv2[6]) = BVModEq.map_f_to_bv 9 fv2[2]  ->
  some (BVModEq.bool_to_bv 9 bv2[5]) = BVModEq.map_f_to_bv 9 fv2[3]  ->
  some (BVModEq.bool_to_bv 9 bv2[4]) = BVModEq.map_f_to_bv 9 fv2[4]  ->
  some (BVModEq.bool_to_bv 9 bv2[3]) = BVModEq.map_f_to_bv 9 fv2[5]  ->
  some (BVModEq.bool_to_bv 9 bv2[2]) = BVModEq.map_f_to_bv 9 fv2[6]  ->
  some (BVModEq.bool_to_bv 9 bv2[1]) = BVModEq.map_f_to_bv 9 fv2[7]  ->
  some (BVModEq.bool_to_bv 9 bv2[0]) = BVModEq.map_f_to_bv 9 fv2[8]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_9 (Vector.append fv1 fv2))
:= by
  unfold OR_9
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
