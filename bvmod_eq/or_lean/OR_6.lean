-- AUTO-GENERATED — DO NOT EDIT


def OR_6  : Subtable FF0 12 :=
  subtableFromMLE (fun x => 1*(x[11] + x[5] - x[11]*x[5]) + 2*(x[10] + x[4] - x[10]*x[4]) + 4*(x[9] + x[3] - x[9]*x[3]) + 8*(x[8] + x[2] - x[8]*x[2]) + 16*(x[7] + x[1] - x[7]*x[1]) + 32*(x[6] + x[0] - x[6]*x[0]))

lemma or_mle_6_chunk
  (bv1 bv2 : BitVec 6)
  (fv1 fv2 : Vector FF0 6) :
  some bvoutput = BVModEq.map_f_to_bv 6 foutput ->
  some (BVModEq.bool_to_bv 6 bv1[5]) = BVModEq.map_f_to_bv 6 fv1[0]  ->
  some (BVModEq.bool_to_bv 6 bv1[4]) = BVModEq.map_f_to_bv 6 fv1[1]  ->
  some (BVModEq.bool_to_bv 6 bv1[3]) = BVModEq.map_f_to_bv 6 fv1[2]  ->
  some (BVModEq.bool_to_bv 6 bv1[2]) = BVModEq.map_f_to_bv 6 fv1[3]  ->
  some (BVModEq.bool_to_bv 6 bv1[1]) = BVModEq.map_f_to_bv 6 fv1[4]  ->
  some (BVModEq.bool_to_bv 6 bv1[0]) = BVModEq.map_f_to_bv 6 fv1[5]  ->
  some (BVModEq.bool_to_bv 6 bv2[5]) = BVModEq.map_f_to_bv 6 fv2[0]  ->
  some (BVModEq.bool_to_bv 6 bv2[4]) = BVModEq.map_f_to_bv 6 fv2[1]  ->
  some (BVModEq.bool_to_bv 6 bv2[3]) = BVModEq.map_f_to_bv 6 fv2[2]  ->
  some (BVModEq.bool_to_bv 6 bv2[2]) = BVModEq.map_f_to_bv 6 fv2[3]  ->
  some (BVModEq.bool_to_bv 6 bv2[1]) = BVModEq.map_f_to_bv 6 fv2[4]  ->
  some (BVModEq.bool_to_bv 6 bv2[0]) = BVModEq.map_f_to_bv 6 fv2[5]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_6 (Vector.append fv1 fv2))
:= by
  unfold OR_6
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
