import BvModEq.SolveMle

abbrev ff := 2435875175126190479447740508185965837690552500527637822603658699938581184513
abbrev f := ZMod ff

variable (fresh_pf0_sum_bit0 : f)
variable (fresh_pf0_sum_bit1 : f)
variable (fresh_pf0_sum_bit2 : f)
variable (fresh_pf0_sum_bit3 : f)
variable (a : BitVec 2)
variable (b : BitVec 2)



instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry

instance NotTwo: BVModEq.GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry


lemma square_eq_one_zero (x : f) : x * x = x <-> ( x.val <= 1)  /\ (((  x.val : BitVec 256)= 0#256 ) \/ ((x.val : BitVec 256) =1) ):= by
sorry



lemma bvmul_2:

 (     ( fresh_pf0_sum_bit0  *fresh_pf0_sum_bit0) = fresh_pf0_sum_bit0) ->
      ( fresh_pf1_sum_bit1 * fresh_pf1_sum_bit1) = fresh_pf1_sum_bit1 ->
     ( ( fresh_pf2_sum_bit2 * fresh_pf2_sum_bit2)  = fresh_pf2_sum_bit2) ->
     ( ( fresh_pf3_sum_bit3 * fresh_pf3_sum_bit3) = fresh_pf3_sum_bit3) ->

     (
       ( 1 * fresh_pf0_sum_bit0) +
       ( 2 * fresh_pf1_sum_bit1) +
       ( 4  *fresh_pf2_sum_bit2) +
       ( 8 * fresh_pf3_sum_bit3) =

        (BVModEq.map_bv_to_f ff a) * BVModEq.map_bv_to_f ff b )
    ->
      (if (a * b)[0] then (1: f) else (0:f)) = fresh_pf0_sum_bit0  := by


    --- intro necessary bounds
      intro h1 h2 h3 h4 h5
      rw [square_eq_one_zero] at h1 h2 h3 h4
      rcases h1 with ⟨h1_1, h1_2⟩
      rcases h2 with ⟨h2_1, h2_2⟩
      rcases h3 with ⟨h3_1, h3_2⟩
      rcases h4 with ⟨h4_1, h4_2⟩


      -- unfold BitVec defs
      unfold BVModEq.map_bv_to_f at h5


      -- valify
      rw [BVModEq.ZMod.eq_if_val] at h5
      valify [h1_1, h2_1, h3_1, h4_1] at h5
      rw [BVModEq.ZMod.eq_if_val]
      --rw [BVModEq.ZMod.if_then_else_val]
      --have h: ZMod.val (if (a * b)[0] = true then (1:f) else 0) = if (a * b)[0] = true then (1:f).val else (0:f).val := by sorry
      --rw [h]

      valify [h1_1, h2_1, h3_1,h4_1]
      simp at h5


      -- eliminate mods (this could be a tactic)
      rw [Nat.mod_eq_of_lt] at h5
      rw [Nat.mod_eq_of_lt] at h5


      -- bvify
      rw [ BVModEq.BitVec_ofNat_eq_iff 256] at h5
      bvify [h1_1, h2_1, h3_1, h4_1] at h5
      rw [ BVModEq.BitVec_ofNat_eq_iff 256]
      bvify [h1_1, h2_1, h3_1, h4_1]

      -- clean up
     --have h2: ZMod.val (if (a * b)[0] = true then (1:f) else 0) = if (a * b)[0] = true then (1:f).val else (0:f).val := by sorry
      --
      --unfold bool_to_bv

      --- 3 Solutions
      -- 1. We do range analysis in rust and cast everything into the biggest bit vector we know will happen due to overflow
      -- 2. We do range analysis in Lean?? Somehow figure out overflow & then have a function to cast everything smaller bit vector into bigger
      -- 3. This is manual left to user.

-- This should go to bit vector land (if (a * b)[0] = true then 1 else 0) = fresh_pf0_sum_bit0
--


      bv_normalize
      bv_decide
      -- To Do make range analysis work with if then and also not break of gets BitVector.Nat and stil apply hypothesis
      --- any time we see a .toNat get lemma that talks about bitdwith sizes
      try_apply_lemma_hyps [h1_1, h2_1, h3_1, h4_1, h6, h7]



def x := 3#2
def y := 1#2

#eval (x*y)[0]
#eval (x*y)[1]
