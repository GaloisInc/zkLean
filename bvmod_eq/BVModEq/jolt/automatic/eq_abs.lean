import BVModEq.TranslateAll
set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900
abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
abbrev f := FF0



set_option maxHeartbeats  20000000000000000000

def EQ_ABS_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))


lemma eq_abs_mle_one_chunk [ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = BVModEq.map_f_to_bv 8 foutput ->
   some (BVModEq.bool_to_bv 8 bv1[7])  = BVModEq.map_f_to_bv 8 fv1[0]  ->
   some (BVModEq.bool_to_bv 8 bv1[6]) = BVModEq.map_f_to_bv 8 fv1[1]  ->
   some (BVModEq.bool_to_bv 8 bv1[5]) = BVModEq.map_f_to_bv 8 fv1[2]  ->
   some (BVModEq.bool_to_bv 8 bv1[4]) = BVModEq.map_f_to_bv 8 fv1[3]  ->
   some (BVModEq.bool_to_bv 8 bv1[3]) = BVModEq.map_f_to_bv 8 fv1[4]  ->
  some (BVModEq.bool_to_bv 8 bv1[2]) = BVModEq.map_f_to_bv 8 fv1[5]  ->
   some (BVModEq.bool_to_bv 8 bv1[1]) = BVModEq.map_f_to_bv 8 fv1[6]  ->
   some (BVModEq.bool_to_bv 8 bv1[0]) = BVModEq.map_f_to_bv 8 fv1[7]  ->
  some (BVModEq.bool_to_bv 8 bv2[7]) = BVModEq.map_f_to_bv 8 fv2[0]  ->
  some (BVModEq.bool_to_bv 8 bv2[6]) = BVModEq.map_f_to_bv 8 fv2[1]  ->
  some (BVModEq.bool_to_bv 8 bv2[5]) = BVModEq.map_f_to_bv 8 fv2[2]  ->
  some (BVModEq.bool_to_bv 8 bv2[4]) = BVModEq.map_f_to_bv 8 fv2[3]  ->
  some (BVModEq.bool_to_bv 8 bv2[3]) = BVModEq.map_f_to_bv 8 fv2[4]  ->
  some (BVModEq.bool_to_bv 8 bv2[2]) = BVModEq.map_f_to_bv 8 fv2[5]  ->
  some (BVModEq.bool_to_bv 8 bv2[1]) = BVModEq.map_f_to_bv 8 fv2[6]  ->
  some (BVModEq.bool_to_bv 8 bv2[0]) = BVModEq.map_f_to_bv 8 fv2[7]  ->
  (bvoutput = BVModEq.bool_to_bv 8 (BitVec.and bv1 127 = BitVec.and bv2 127 ))
  =
  (foutput = evalSubtable EQ_ABS_16  (Vector.append fv1 fv2)) := by
  unfold EQ_ABS_16
  unfold evalSubtable
  unfold subtableFromMLE
  unfold Vector.append
  translate_all false
