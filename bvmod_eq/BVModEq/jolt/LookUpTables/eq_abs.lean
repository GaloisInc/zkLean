import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def EQ_ABS_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))


lemma eq_abs_mle_one_chunk [ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv_8 foutput ->
   some (bool_to_bv bv1[7])  = map_f_to_bv_8 fv1[0]  ->
   some (bool_to_bv bv1[6]) = map_f_to_bv_8 fv1[1]  ->
   some (bool_to_bv bv1[5]) = map_f_to_bv_8 fv1[2]  ->
   some (bool_to_bv bv1[4]) = map_f_to_bv_8 fv1[3]  ->
   some (bool_to_bv bv1[3]) = map_f_to_bv_8 fv1[4]  ->
  some (bool_to_bv bv1[2]) = map_f_to_bv_8 fv1[5]  ->
   some (bool_to_bv bv1[1]) = map_f_to_bv_8 fv1[6]  ->
   some (bool_to_bv bv1[0]) = map_f_to_bv_8 fv1[7]  ->
  some (bool_to_bv bv2[7]) = map_f_to_bv_8 fv2[0]  ->
  some (bool_to_bv bv2[6]) = map_f_to_bv_8 fv2[1]  ->
  some (bool_to_bv bv2[5]) = map_f_to_bv_8 fv2[2]  ->
  some (bool_to_bv bv2[4]) = map_f_to_bv_8 fv2[3]  ->
  some (bool_to_bv bv2[3]) = map_f_to_bv_8 fv2[4]  ->
  some (bool_to_bv bv2[2]) = map_f_to_bv_8 fv2[5]  ->
  some (bool_to_bv bv2[1]) = map_f_to_bv_8 fv2[6]  ->
  some (bool_to_bv bv2[0]) = map_f_to_bv_8 fv2[7]  ->
  (bvoutput = bool_to_bv (BitVec.and bv1 127 = BitVec.and bv2 127 ))
  =
  (foutput = evalSubtable EQ_ABS_16  (Vector.append fv1 fv2))
 := by solveMLE EQ_ABS_16 8
