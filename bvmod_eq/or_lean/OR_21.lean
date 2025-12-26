-- AUTO-GENERATED — DO NOT EDIT
import BVModEq.TranslateAll
set_option maxRecDepth 1048576

set_option maxHeartbeats  20000000000000000000

def OR_21  : Subtable FF0 42 :=
  subtableFromMLE (fun x => 1*(x[41] + x[20] - x[41]*x[20]) + 2*(x[40] + x[19] - x[40]*x[19]) + 4*(x[39] + x[18] - x[39]*x[18]) + 8*(x[38] + x[17] - x[38]*x[17]) + 16*(x[37] + x[16] - x[37]*x[16]) + 32*(x[36] + x[15] - x[36]*x[15]) + 64*(x[35] + x[14] - x[35]*x[14]) + 128*(x[34] + x[13] - x[34]*x[13]) + 256*(x[33] + x[12] - x[33]*x[12]) + 512*(x[32] + x[11] - x[32]*x[11]) + 1024*(x[31] + x[10] - x[31]*x[10]) + 2048*(x[30] + x[9] - x[30]*x[9]) + 4096*(x[29] + x[8] - x[29]*x[8]) + 8192*(x[28] + x[7] - x[28]*x[7]) + 16384*(x[27] + x[6] - x[27]*x[6]) + 32768*(x[26] + x[5] - x[26]*x[5]) + 65536*(x[25] + x[4] - x[25]*x[4]) + 131072*(x[24] + x[3] - x[24]*x[3]) + 262144*(x[23] + x[2] - x[23]*x[2]) + 524288*(x[22] + x[1] - x[22]*x[1]) + 1048576*(x[21] + x[0] - x[21]*x[0]))

lemma or_mle_21_chunk
  (bv1 bv2 : BitVec 21)
  (fv1 fv2 : Vector FF0 21) :
  some bvoutput = BVModEq.map_f_to_bv 21 foutput ->
  some (BVModEq.bool_to_bv 21 bv1[20]) = BVModEq.map_f_to_bv 21 fv1[0]  ->
  some (BVModEq.bool_to_bv 21 bv1[19]) = BVModEq.map_f_to_bv 21 fv1[1]  ->
  some (BVModEq.bool_to_bv 21 bv1[18]) = BVModEq.map_f_to_bv 21 fv1[2]  ->
  some (BVModEq.bool_to_bv 21 bv1[17]) = BVModEq.map_f_to_bv 21 fv1[3]  ->
  some (BVModEq.bool_to_bv 21 bv1[16]) = BVModEq.map_f_to_bv 21 fv1[4]  ->
  some (BVModEq.bool_to_bv 21 bv1[15]) = BVModEq.map_f_to_bv 21 fv1[5]  ->
  some (BVModEq.bool_to_bv 21 bv1[14]) = BVModEq.map_f_to_bv 21 fv1[6]  ->
  some (BVModEq.bool_to_bv 21 bv1[13]) = BVModEq.map_f_to_bv 21 fv1[7]  ->
  some (BVModEq.bool_to_bv 21 bv1[12]) = BVModEq.map_f_to_bv 21 fv1[8]  ->
  some (BVModEq.bool_to_bv 21 bv1[11]) = BVModEq.map_f_to_bv 21 fv1[9]  ->
  some (BVModEq.bool_to_bv 21 bv1[10]) = BVModEq.map_f_to_bv 21 fv1[10]  ->
  some (BVModEq.bool_to_bv 21 bv1[9]) = BVModEq.map_f_to_bv 21 fv1[11]  ->
  some (BVModEq.bool_to_bv 21 bv1[8]) = BVModEq.map_f_to_bv 21 fv1[12]  ->
  some (BVModEq.bool_to_bv 21 bv1[7]) = BVModEq.map_f_to_bv 21 fv1[13]  ->
  some (BVModEq.bool_to_bv 21 bv1[6]) = BVModEq.map_f_to_bv 21 fv1[14]  ->
  some (BVModEq.bool_to_bv 21 bv1[5]) = BVModEq.map_f_to_bv 21 fv1[15]  ->
  some (BVModEq.bool_to_bv 21 bv1[4]) = BVModEq.map_f_to_bv 21 fv1[16]  ->
  some (BVModEq.bool_to_bv 21 bv1[3]) = BVModEq.map_f_to_bv 21 fv1[17]  ->
  some (BVModEq.bool_to_bv 21 bv1[2]) = BVModEq.map_f_to_bv 21 fv1[18]  ->
  some (BVModEq.bool_to_bv 21 bv1[1]) = BVModEq.map_f_to_bv 21 fv1[19]  ->
  some (BVModEq.bool_to_bv 21 bv1[0]) = BVModEq.map_f_to_bv 21 fv1[20]  ->
  some (BVModEq.bool_to_bv 21 bv2[20]) = BVModEq.map_f_to_bv 21 fv2[0]  ->
  some (BVModEq.bool_to_bv 21 bv2[19]) = BVModEq.map_f_to_bv 21 fv2[1]  ->
  some (BVModEq.bool_to_bv 21 bv2[18]) = BVModEq.map_f_to_bv 21 fv2[2]  ->
  some (BVModEq.bool_to_bv 21 bv2[17]) = BVModEq.map_f_to_bv 21 fv2[3]  ->
  some (BVModEq.bool_to_bv 21 bv2[16]) = BVModEq.map_f_to_bv 21 fv2[4]  ->
  some (BVModEq.bool_to_bv 21 bv2[15]) = BVModEq.map_f_to_bv 21 fv2[5]  ->
  some (BVModEq.bool_to_bv 21 bv2[14]) = BVModEq.map_f_to_bv 21 fv2[6]  ->
  some (BVModEq.bool_to_bv 21 bv2[13]) = BVModEq.map_f_to_bv 21 fv2[7]  ->
  some (BVModEq.bool_to_bv 21 bv2[12]) = BVModEq.map_f_to_bv 21 fv2[8]  ->
  some (BVModEq.bool_to_bv 21 bv2[11]) = BVModEq.map_f_to_bv 21 fv2[9]  ->
  some (BVModEq.bool_to_bv 21 bv2[10]) = BVModEq.map_f_to_bv 21 fv2[10]  ->
  some (BVModEq.bool_to_bv 21 bv2[9]) = BVModEq.map_f_to_bv 21 fv2[11]  ->
  some (BVModEq.bool_to_bv 21 bv2[8]) = BVModEq.map_f_to_bv 21 fv2[12]  ->
  some (BVModEq.bool_to_bv 21 bv2[7]) = BVModEq.map_f_to_bv 21 fv2[13]  ->
  some (BVModEq.bool_to_bv 21 bv2[6]) = BVModEq.map_f_to_bv 21 fv2[14]  ->
  some (BVModEq.bool_to_bv 21 bv2[5]) = BVModEq.map_f_to_bv 21 fv2[15]  ->
  some (BVModEq.bool_to_bv 21 bv2[4]) = BVModEq.map_f_to_bv 21 fv2[16]  ->
  some (BVModEq.bool_to_bv 21 bv2[3]) = BVModEq.map_f_to_bv 21 fv2[17]  ->
  some (BVModEq.bool_to_bv 21 bv2[2]) = BVModEq.map_f_to_bv 21 fv2[18]  ->
  some (BVModEq.bool_to_bv 21 bv2[1]) = BVModEq.map_f_to_bv 21 fv2[19]  ->
  some (BVModEq.bool_to_bv 21 bv2[0]) = BVModEq.map_f_to_bv 21 fv2[20]  ->
  (bvoutput = (BitVec.or bv1 bv2))
  =
  (foutput = evalSubtable OR_21 (Vector.append fv1 fv2))
:= by
  unfold OR_21
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
