import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def IDENTITY_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*x[15] + 2*x[14] + 4*x[13] + 8*x[12] + 16*x[11] + 32*x[10] + 64*x[9] + 128*x[8] + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0])


lemma identity_mle_one_chunk {bvoutput foutput} [ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
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
  (bvoutput = BitVec.append bv1 bv2 )
  =
  (foutput = evalSubtable IDENTITY_16 (Vector.append fv1 fv2))
 := by solveMLE IDENTITY_16 16
