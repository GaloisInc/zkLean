-- AUTO-GENERATED — DO NOT EDIT
import BVModEq.TranslateAll
set_option maxRecDepth 1048576

set_option maxHeartbeats  20000000000000000000

def OR_19  : Subtable FF0 38 :=
  subtableFromMLE (fun x => 1*(x[37] + x[18] - x[37]*x[18]) + 2*(x[36] + x[17] - x[36]*x[17]) + 4*(x[35] + x[16] - x[35]*x[16]) + 8*(x[34] + x[15] - x[34]*x[15]) + 16*(x[33] + x[14] - x[33]*x[14]) + 32*(x[32] + x[13] - x[32]*x[13]) + 64*(x[31] + x[12] - x[31]*x[12]) + 128*(x[30] + x[11] - x[30]*x[11]) + 256*(x[29] + x[10] - x[29]*x[10]) + 512*(x[28] + x[9] - x[28]*x[9]) + 1024*(x[27] + x[8] - x[27]*x[8]) + 2048*(x[26] + x[7] - x[26]*x[7]) + 4096*(x[25] + x[6] - x[25]*x[6]) + 8192*(x[24] + x[5] - x[24]*x[5]) + 16384*(x[23] + x[4] - x[23]*x[4]) + 32768*(x[22] + x[3] - x[22]*x[3]) + 65536*(x[21] + x[2] - x[21]*x[2]) + 131072*(x[20] + x[1] - x[20]*x[1]) + 262144*(x[19] + x[0] - x[19]*x[0]))

lemma or_mle_19_chunk
  (bv1 bv2 : BitVec 19)
  (fv1 fv2 : Vector FF0 19) :
  some bvoutput = BVModEq.map_f_to_bv 19 foutput ->
  some (BVModEq.bool_to_bv 19 bv1[18]) = BVModEq.map_f_to_bv 19 fv1[0]  ->
  some (BVModEq.bool_to_bv 19 bv1[17]) = BVModEq.map_f_to_bv 19 fv1[1]  ->
  some (BVModEq.bool_to_bv 19 bv1[16]) = BVModEq.map_f_to_bv 19 fv1[2]  ->
  some (BVModEq.bool_to_bv 19 bv1[15]) = BVModEq.map_f_to_bv 19 fv1[3]  ->
  some (BVModEq.bool_to_bv 19 bv1[14]) = BVModEq.map_f_to_bv 19 fv1[4]  ->
  some (BVModEq.bool_to_bv 19 bv1[13]) = BVModEq.map_f_to_bv 19 fv1[5]  ->
  some (BVModEq.bool_to_bv 19 bv1[12]) = BVModEq.map_f_to_bv 19 fv1[6]  ->
  some (BVModEq.bool_to_bv 19 bv1[11]) = BVModEq.map_f_to_bv 19 fv1[7]  ->
  some (BVModEq.bool_to_bv 19 bv1[10]) = BVModEq.map_f_to_bv 19 fv1[8]  ->
  some (BVModEq.bool_to_bv 19 bv1[9]) = BVModEq.map_f_to_bv 19 fv1[9]  ->
  some (BVModEq.bool_to_bv 19 bv1[8]) = BVModEq.map_f_to_bv 19 fv1[10]  ->
  some (BVModEq.bool_to_bv 19 bv1[7]) = BVModEq.map_f_to_bv 19 fv1[11]  ->
  some (BVModEq.bool_to_bv 19 bv1[6]) = BVModEq.map_f_to_bv 19 fv1[12]  ->
  some (BVModEq.bool_to_bv 19 bv1[5]) = BVModEq.map_f_to_bv 19 fv1[13]  ->
  some (BVModEq.bool_to_bv 19 bv1[4]) = BVModEq.map_f_to_bv 19 fv1[14]  ->
  some (BVModEq.bool_to_bv 19 bv1[3]) = BVModEq.map_f_to_bv 19 fv1[15]  ->
  some (BVModEq.bool_to_bv 19 bv1[2]) = BVModEq.map_f_to_bv 19 fv1[16]  ->
  some (BVModEq.bool_to_bv 19 bv1[1]) = BVModEq.map_f_to_bv 19 fv1[17]  ->
  some (BVModEq.bool_to_bv 19 bv1[0]) = BVModEq.map_f_to_bv 19 fv1[18]  ->
  some (BVModEq.bool_to_bv 19 bv2[18]) = BVModEq.map_f_to_bv 19 fv2[0]  ->
  some (BVModEq.bool_to_bv 19 bv2[17]) = BVModEq.map_f_to_bv 19 fv2[1]  ->
  some (BVModEq.bool_to_bv 19 bv2[16]) = BVModEq.map_f_to_bv 19 fv2[2]  ->
  some (BVModEq.bool_to_bv 19 bv2[15]) = BVModEq.map_f_to_bv 19 fv2[3]  ->
  some (BVModEq.bool_to_bv 19 bv2[14]) = BVModEq.map_f_to_bv 19 fv2[4]  ->
  some (BVModEq.bool_to_bv 19 bv2[13]) = BVModEq.map_f_to_bv 19 fv2[5]  ->
  some (BVModEq.bool_to_bv 19 bv2[12]) = BVModEq.map_f_to_bv 19 fv2[6]  ->
  some (BVModEq.bool_to_bv 19 bv2[11]) = BVModEq.map_f_to_bv 19 fv2[7]  ->
  some (BVModEq.bool_to_bv 19 bv2[10]) = BVModEq.map_f_to_bv 19 fv2[8]  ->
  some (BVModEq.bool_to_bv 19 bv2[9]) = BVModEq.map_f_to_bv 19 fv2[9]  ->
  some (BVModEq.bool_to_bv 19 bv2[8]) = BVModEq.map_f_to_bv 19 fv2[10]  ->
  some (BVModEq.bool_to_bv 19 bv2[7]) = BVModEq.map_f_to_bv 19 fv2[11]  ->
  some (BVModEq.bool_to_bv 19 bv2[6]) = BVModEq.map_f_to_bv 19 fv2[12]  ->
  some (BVModEq.bool_to_bv 19 bv2[5]) = BVModEq.map_f_to_bv 19 fv2[13]  ->
  some (BVModEq.bool_to_bv 19 bv2[4]) = BVModEq.map_f_to_bv 19 fv2[14]  ->
  some (BVModEq.bool_to_bv 19 bv2[3]) = BVModEq.map_f_to_bv 19 fv2[15]  ->
  some (BVModEq.bool_to_bv 19 bv2[2]) = BVModEq.map_f_to_bv 19 fv2[16]  ->
  some (BVModEq.bool_to_bv 19 bv2[1]) = BVModEq.map_f_to_bv 19 fv2[17]  ->
  some (BVModEq.bool_to_bv 19 bv2[0]) = BVModEq.map_f_to_bv 19 fv2[18]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_19 (Vector.append fv1 fv2))
:= by
  unfold OR_19
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
