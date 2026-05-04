import ZkLean.Formalism
import ZkLean.solve_mle



set_option maxHeartbeats  20000000000000000000

def LTU_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + (1 - x[0])*x[8]*1 + (1 - x[1])*x[9]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8]) + (1 - x[2])*x[10]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9]) + (1 - x[3])*x[11]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10]) + (1 - x[4])*x[12]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11]) + (1 - x[5])*x[13]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12]) + (1 - x[6])*x[14]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13]) + (1 - x[7])*x[15]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13])*(1 - x[6] - x[14] + x[6]*x[14] + x[6]*x[14]))

open Mathlib.Tactic.Valify

lemma ltu_mle_one_chunk [ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
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
  (bvoutput = bool_to_bv (bv1 < bv2 ))
  =
  (foutput = evalSubtable LTU_16  (Vector.append fv1 fv2))
 := by
    intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [extract_bv_rel_8] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rcases h2 with ⟨h2_1, h2_2⟩
    rcases h3 with ⟨h3_1, h3_2⟩
    rcases h4 with ⟨h4_1, h4_2⟩
    rcases h5 with ⟨h5_1, h5_2⟩
    rcases h6 with ⟨h6_1, h6_2⟩
    rcases h7 with ⟨h7_1, h7_2⟩
    rcases h8 with ⟨h8_1, h8_2⟩
    rcases h9 with ⟨h9_1, h9_2⟩
    rcases h10 with ⟨h10_1, h10_2⟩
    rcases h11 with ⟨h11_1, h11_2⟩
    rcases h12 with ⟨h12_1, h12_2⟩
    rcases h13 with ⟨h13_1, h13_2⟩
    rcases h14 with ⟨h14_1, h14_2⟩
    rcases h15 with ⟨h15_1, h15_2⟩
    rcases h16 with ⟨h16_1, h16_2⟩
    rcases h17 with ⟨h17_1, h17_2⟩
    unfold map_f_to_bv_8 at h1
    simp at h1
    rcases h1 with ⟨h1_1, h1_2⟩
    -- apply val and unfold subtables
    rw [ZMod.eq_if_val]
    unfold LTU_16
    unfold evalSubtable
    simp
    unfold subtableFromMLE
    simp
    unfold Vector.append
    simp
   -- simp  [ult_val h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, or_val, ZMod.val_sub, ZMod.val_add, ZMod.val_mul, ZMod.val_one, ZMod.val_ofNat, push_cast]
    --valify [h2_1, h11_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1]
    simp [ZMod.val_add]
    simp [ZMod.val_mul]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mul_left_mod, Nat.mod_mul_right_mod]
    simp
    --rw [Nat.mod_eq_of_lt]
   -- simp [ult_val  h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1]
    simp [ult_val h2_1 h10_1]

    simp [ult_val h3_1 h11_1]

    simp [ult_val h4_1 h12_1]
    simp [ult_val h5_1 h13_1]
    simp [ult_val h6_1 h14_1]
    simp [ult_val h7_1 h15_1]
    simp [ult_val h8_1 h16_1]
    --simp [ZMod.val_add]
   -- simp [ZMod.val_mul]
    --simp [ZMod.val_mul]
    simp [*]
    rw [ZMod.val_sub h2_1]
    rw [ZMod.val_sub h3_1]
    rw [ZMod.val_sub h4_1]
    rw [ZMod.val_sub h5_1]
    rw [ZMod.val_sub h6_1]
    rw [ZMod.val_sub h7_1]
    rw [ZMod.val_sub h8_1]
    rw [ZMod.val_sub h9_1]
    simp [ZMod.val_one]
    --simp [<- Nat.mul_mod]
    --simp
    rw [Nat.mod_eq_of_lt]


    rw [BitVec_ofNat_eq_iff_8]
    unfold bool_to_bv
    -- apply bv and nat to zmod
    bvify [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1]
    -- necessary because of Lean version this can do away
    set a := foutput.val
    set b10:= ZMod.val fv1[0]
    set b11 := ZMod.val fv1[1]
    set b12 := ZMod.val fv1[2]
    set b13 := ZMod.val fv1[3]
    set b14 := ZMod.val fv1[4]
    set b15 := ZMod.val fv1[5]
    set b16 := ZMod.val fv1[6]
    set b17 := ZMod.val fv1[7]
    set b20:= ZMod.val fv2[0]
    set b21 := ZMod.val fv2[1]
    set b22 := ZMod.val fv2[2]
    set b23 := ZMod.val fv2[3]
    set b24 := ZMod.val fv2[4]
    set b25 := ZMod.val fv2[5]
    set b26 := ZMod.val fv2[6]
    set b27 := ZMod.val fv2[7]
    bv_normalize
    bv_decide
    --bv_decide
    exact h1_1

    --- range analysis tactic
    try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1]
