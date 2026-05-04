import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def SIGN_EXTEND_16_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => x[0]*65535)

open BitVec

lemma sign_extend_mle_one_chunk {bvoutput foutput} [ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv_16 foutput ->
   some (bool_to_bv_16 bv1[7])  = map_f_to_bv_16 fv1[0]  ->
   some (bool_to_bv_16 bv1[6]) = map_f_to_bv_16 fv1[1]  ->
   some (bool_to_bv_16 bv1[5]) = map_f_to_bv_16 fv1[2]  ->
   some (bool_to_bv_16 bv1[4]) = map_f_to_bv_16 fv1[3]  ->
   some (bool_to_bv_16 bv1[3]) = map_f_to_bv_16 fv1[4]  ->
  some (bool_to_bv_16 bv1[2]) = map_f_to_bv_16 fv1[5]  ->
   some (bool_to_bv_16 bv1[1]) = map_f_to_bv_16 fv1[6]  ->
   some (bool_to_bv_16 bv1[0]) = map_f_to_bv_16 fv1[7]  ->
  some (bool_to_bv_16 bv2[7]) = map_f_to_bv_16 fv2[0]  ->
  some (bool_to_bv_16 bv2[6]) = map_f_to_bv_16 fv2[1]  ->
  some (bool_to_bv_16 bv2[5]) = map_f_to_bv_16 fv2[2]  ->
  some (bool_to_bv_16 bv2[4]) = map_f_to_bv_16 fv2[3]  ->
  some (bool_to_bv_16 bv2[3]) = map_f_to_bv_16 fv2[4]  ->
  some (bool_to_bv_16 bv2[2]) = map_f_to_bv_16 fv2[5]  ->
  some (bool_to_bv_16 bv2[1]) = map_f_to_bv_16 fv2[6]  ->
  some (bool_to_bv_16 bv2[0]) = map_f_to_bv_16 fv2[7]  ->
  (bvoutput = BitVec.fill 16 bv1[7])
  =
  (foutput = evalSubtable SIGN_EXTEND_16_16 (Vector.append fv1 fv2))
 := by
  -- I think this is okay to expect use to do
   unfold fill
   solveMLE SIGN_EXTEND_16_16 16
