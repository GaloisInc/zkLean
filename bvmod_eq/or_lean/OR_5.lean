-- AUTO-GENERATED — DO NOT EDIT
import BVModEq.TranslateAll
set_option maxRecDepth 1048576

set_option maxHeartbeats  20000000000000000000

def OR_5  : Subtable FF0 10 :=
  subtableFromMLE (fun x => 1*(x[9] + x[4] - x[9]*x[4]) + 2*(x[8] + x[3] - x[8]*x[3]) + 4*(x[7] + x[2] - x[7]*x[2]) + 8*(x[6] + x[1] - x[6]*x[1]) + 16*(x[5] + x[0] - x[5]*x[0]))

lemma or_mle_5_chunk
  (bv1 bv2 : BitVec 5)
  (fv1 fv2 : Vector FF0 5) :
  some bvoutput = BVModEq.map_f_to_bv 5 foutput ->
  some (BVModEq.bool_to_bv 5 bv1[4]) = BVModEq.map_f_to_bv 5 fv1[0]  ->
  some (BVModEq.bool_to_bv 5 bv1[3]) = BVModEq.map_f_to_bv 5 fv1[1]  ->
  some (BVModEq.bool_to_bv 5 bv1[2]) = BVModEq.map_f_to_bv 5 fv1[2]  ->
  some (BVModEq.bool_to_bv 5 bv1[1]) = BVModEq.map_f_to_bv 5 fv1[3]  ->
  some (BVModEq.bool_to_bv 5 bv1[0]) = BVModEq.map_f_to_bv 5 fv1[4]  ->
  some (BVModEq.bool_to_bv 5 bv2[4]) = BVModEq.map_f_to_bv 5 fv2[0]  ->
  some (BVModEq.bool_to_bv 5 bv2[3]) = BVModEq.map_f_to_bv 5 fv2[1]  ->
  some (BVModEq.bool_to_bv 5 bv2[2]) = BVModEq.map_f_to_bv 5 fv2[2]  ->
  some (BVModEq.bool_to_bv 5 bv2[1]) = BVModEq.map_f_to_bv 5 fv2[3]  ->
  some (BVModEq.bool_to_bv 5 bv2[0]) = BVModEq.map_f_to_bv 5 fv2[4]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_5 (Vector.append fv1 fv2))
:= by
  unfold OR_5
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
