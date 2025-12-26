-- AUTO-GENERATED — DO NOT EDIT
import BVModEq.TranslateAll
set_option maxRecDepth 1048576

set_option maxHeartbeats  20000000000000000000
def OR_7  : Subtable FF0 14 :=
  subtableFromMLE (fun x => 1*(x[13] + x[6] - x[13]*x[6]) + 2*(x[12] + x[5] - x[12]*x[5]) + 4*(x[11] + x[4] - x[11]*x[4]) + 8*(x[10] + x[3] - x[10]*x[3]) + 16*(x[9] + x[2] - x[9]*x[2]) + 32*(x[8] + x[1] - x[8]*x[1]) + 64*(x[7] + x[0] - x[7]*x[0]))

lemma or_mle_7_chunk
  (bv1 bv2 : BitVec 7)
  (fv1 fv2 : Vector FF0 7) :
  some bvoutput = BVModEq.map_f_to_bv 7 foutput ->
  some (BVModEq.bool_to_bv 7 bv1[6]) = BVModEq.map_f_to_bv 7 fv1[0]  ->
  some (BVModEq.bool_to_bv 7 bv1[5]) = BVModEq.map_f_to_bv 7 fv1[1]  ->
  some (BVModEq.bool_to_bv 7 bv1[4]) = BVModEq.map_f_to_bv 7 fv1[2]  ->
  some (BVModEq.bool_to_bv 7 bv1[3]) = BVModEq.map_f_to_bv 7 fv1[3]  ->
  some (BVModEq.bool_to_bv 7 bv1[2]) = BVModEq.map_f_to_bv 7 fv1[4]  ->
  some (BVModEq.bool_to_bv 7 bv1[1]) = BVModEq.map_f_to_bv 7 fv1[5]  ->
  some (BVModEq.bool_to_bv 7 bv1[0]) = BVModEq.map_f_to_bv 7 fv1[6]  ->
  some (BVModEq.bool_to_bv 7 bv2[6]) = BVModEq.map_f_to_bv 7 fv2[0]  ->
  some (BVModEq.bool_to_bv 7 bv2[5]) = BVModEq.map_f_to_bv 7 fv2[1]  ->
  some (BVModEq.bool_to_bv 7 bv2[4]) = BVModEq.map_f_to_bv 7 fv2[2]  ->
  some (BVModEq.bool_to_bv 7 bv2[3]) = BVModEq.map_f_to_bv 7 fv2[3]  ->
  some (BVModEq.bool_to_bv 7 bv2[2]) = BVModEq.map_f_to_bv 7 fv2[4]  ->
  some (BVModEq.bool_to_bv 7 bv2[1]) = BVModEq.map_f_to_bv 7 fv2[5]  ->
  some (BVModEq.bool_to_bv 7 bv2[0]) = BVModEq.map_f_to_bv 7 fv2[6]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_7 (Vector.append fv1 fv2))
:= by
  unfold OR_7
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
