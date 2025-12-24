-- AUTO-GENERATED — DO NOT EDIT


def OR_2  : Subtable FF0 4 :=
  subtableFromMLE (fun x => 1*(x[3] + x[1] - x[3]*x[1]) + 2*(x[2] + x[0] - x[2]*x[0]))

lemma or_mle_2_chunk
  (bv1 bv2 : BitVec 2)
  (fv1 fv2 : Vector FF0 2) :
  some bvoutput = BVModEq.map_f_to_bv 2 foutput ->
  some (BVModEq.bool_to_bv 2 bv1[1]) = BVModEq.map_f_to_bv 2 fv1[0]  ->
  some (BVModEq.bool_to_bv 2 bv1[0]) = BVModEq.map_f_to_bv 2 fv1[1]  ->
  some (BVModEq.bool_to_bv 2 bv2[1]) = BVModEq.map_f_to_bv 2 fv2[0]  ->
  some (BVModEq.bool_to_bv 2 bv2[0]) = BVModEq.map_f_to_bv 2 fv2[1]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_2 (Vector.append fv1 fv2))
:= by
  unfold OR_2
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
