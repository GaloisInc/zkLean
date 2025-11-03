import BVModEq.SolveMLE


abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513

instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry

instance NotTwo: BVModEq.GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry


lemma ZMod.if_then_else_prop_val {x y : ZMod n} {b: Prop} [Decidable b] :
  (if b then x else y).val = if b then x.val else y.val := by
  split_ifs
  simp
  simp


lemma BitVec.ofNat_if_then_prop_else {bw x y: ℕ}  {b: Prop} [Decidable b] :
  BitVec.ofNat bw (if b then x else y) = if b then BitVec.ofNat bw x else BitVec.ofNat bw y := by
  split_ifs
  simp
  simp


set_option maxHeartbeats 20000000000000000





lemma ZMod.val_sub_mod {ff: ℕ} [h: NeZero ff] {y x : ZMod ff}  (h : x.val ≤ y.val)
  : ZMod.val (y - x) = (ZMod.val (y) - ZMod.val (x) )  := by
  have hx:= ZMod.val_lt x
  have hy := ZMod.val_lt y
  rw [ZMod.val_sub]
  --rw [Nat.mod_eq_of_lt]
  have h1 : y.val - x.val ≤ y.val := Nat.sub_le y.val x.val
 -- apply lt_of_le_of_lt h1 hy
  apply h





lemma neg_add_to_sub {α : Type*} [AddCommGroup α] (a b : α) :
  -a + b = b - a := by
  rw [sub_eq_add_neg]
  rw [add_comm (-a) b]

lemma sub_add_right_recursive {α : Type*} [AddCommGroup α]
    (a b c : α) : a - b + c = (a + c) - b := by
  rw [sub_eq_add_neg, add_assoc]
  rw [sub_eq_add_neg]
  rw [add_comm (-b) (c)]
  rw [add_assoc]


def map_f_to_bv_circ {ff : ℕ} n (rs1_val : ZMod ff) : BitVec n :=
  let m : ℕ := ZMod.val rs1_val
  if m <= 2^n then
    (BitVec.ofNat n m)
  else
    BitVec.ofNat n 0

lemma map_f_to_bv_circ_spec {ff n : ℕ} (rs1_val : ZMod ff)
  (h : ZMod.val rs1_val <= 2^n) :
  map_f_to_bv_circ n rs1_val = BitVec.ofNat n (ZMod.val rs1_val) := by
  simp [map_f_to_bv_circ]
  simp [h]

variable (b : BitVec 2)
variable (a : BitVec 2)



lemma correct :
((((((((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ ((((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (if (((BVModEq.bool_to_bv 1 (map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (BitVec.ult a b)))))))
 := by
  simp
  unfold  BVModEq.map_bv_to_f
  constructor
  focus
    unfold BVModEq.bool_to_bv
    simp
    have h' :a <= 2^2 -1 := by
      apply BitVec.toNatLT
    -- move minus to the end
    rw [<- sub_eq_add_neg]
    rw [sub_add_right_recursive]
    rw [map_f_to_bv_circ_spec]
    rw [BVModEq.ZMod.eq_if_val]
    -- remove minus for the ZVal
    all_goals rw [ZMod.val_sub_mod]
    -- get rid of mod that comes from removal
    --rw [Nat.mod_eq_of_lt]
   -- split_ifs with h1 h2 h3 h4 h5 h6 h7 (2^3)
   --
    valify [h']


-- Algorithm
-- Implementing updated algorithm
-- have loop as a seperate tactic
--
-- for goal & all non range constraint hypothesis:
--   0) unfold all bitvector/ custom definitions
--   -- if you see x * x = x then its a constraint (CirC)
--   -- Jolt if you see if var then = to bit vect (Jolt) TODO: double check this
--   --
--   1) are there minuses then move them to the end
--   2) inject val & run valify
--     2.1 if stuck on minus then handle it
--     2. 2) are there mods then remove ()
--   3) inject bitvectors & run (bvify)
--     4.1) are there mods then remove( )
-- 4) bv_decide
-- 5) prove all ranges with try_apply_lemma_hyps
--     -- very very far future optimize to proves less lemmas!

--   -- if Exp > C replace with Exp >= ?m
--   -- if Exp has 2 vars & sub do case by case (not great if fields or bit vectors with big bounds)
--   -- TODO: Liza write up inference rules inside paper
--   -- prove termination & completness
--      -- decreasing measures # of variables + #of operators (most likely)


-- -- Experiments we want to do
--   -- Jolt (translation to SMT) TODO: automatic translation
--   -- CirC  ( )
--   -- Test of time different versions of lean ( maybe? )very very far future Wishful thinking



    --split_ifs with h1 h2 h3
    simp

    have hx: (b.toNat + 3) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 = (b.toNat + 3) :=
      by
      rw [Nat.mod_eq_of_lt]
      try_apply_lemma_hyps []
-- now Lean creates ⊢ b.toNat + 3 < ff as a normal subgoal
    simp [hx]
    have hy: (a.toNat) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 = a.toNat :=
        by
        rw [Nat.mod_eq_of_lt]
        try_apply_lemma_hyps []
-- now Lean creates ⊢ b.toNat + 3 < ff as a normal subgoal
    simp [hy]
    set c := (BitVec.ofNat 3 (b.toNat + 3 - a.toNat))[0] with hc
    --rw [hc]

    rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
    bvify [] at hc
    rw [hc]
    set c := (BitVec.ofNat 3 (b.toNat + 3 - a.toNat))[1] with hc
    --rw [hc]

    rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
    bvify [] at hc
    rw [hc]
    set c := (BitVec.ofNat 3 (b.toNat + 3 - a.toNat))[2] with hc
    --rw [hc]

    rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
    bvify [] at hc
    valify [hc]
    --rw [ZMod.val_sub_mod]
    --valify  [hc]
   --simp
    --nth_rewrite 3 [Nat.mod_eq_of_lt]
    --nth_rewrite 3 [Nat.mod_eq_of_lt]
    rw [Nat.mod_eq_of_lt]
    --rw [Nat.mod_eq_of_lt]
    rw [BVModEq.BitVec_ofNat_eq_iff 256]
    rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
    bvify
    bv_normalize
    focus bv_decide
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    focus try_apply_lemma_hyps []
    valify
    focus try_apply_lemma_hyps []
    valify
    focus try_apply_lemma_hyps []
    valify
    focus try_apply_lemma_hyps []
  unfold BVModEq.bool_to_bv
  simp
  -- have h' :a <= 2^2 -1 := by
  --   apply BitVec.toNatLT
  rw [<- sub_eq_add_neg]
  rw [sub_add_right_recursive]
  rw [map_f_to_bv_circ_spec]
  all_goals rw [ZMod.val_sub_mod]
  --rw [Nat.mod_eq_of_lt]
  all_goals valify
  simp
  nth_rewrite 1 [Nat.mod_eq_of_lt]
  nth_rewrite 1 [Nat.mod_eq_of_lt]
  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
  bvify

  bv_decide
  try_apply_lemma_hyps []
  -- nth_rewrite 1 [Nat.mod_eq_of_lt]
  -- simp
  -- nth_rewrite 2 [Nat.mod_eq_of_lt]
  -- nth_rewrite 1 [Nat.mod_eq_of_lt]
  -- rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
  -- bvify []
  -- bv_decide
  -- try_apply_lemma_hyps []







  --   try_apply_lemma_hyps []
  --   valify [hc]
  --   try_apply_lemma_hyps []
  --   valify [h']
  --   try_apply_lemma_hyps []
  --   valify [h']
  --   try_apply_lemma_hyps []
  --   valify [h']
  --   try_apply_lemma_hyps []
  --   valify  [h']
  --   try_apply_lemma_hyps []
  --   valify [h']
  --   try_apply_lemma_hyps []
  -- --- for 2nd goal
  -- unfold BVModEq.bool_to_bv
  -- simp
  -- have h' :a <= 2^2 -1 := by
  --   apply BitVec.toNatLT
  -- rw [<- sub_eq_add_neg]
  -- rw [sub_add_right_recursive]
  -- rw [map_f_to_bv_circ_spec]
  -- all_goals rw [ZMod.val_sub_mod]
  -- rw [Nat.mod_eq_of_lt]
  -- all_goals valify [h']
  -- nth_rewrite 2 [Nat.mod_eq_of_lt]
  -- nth_rewrite 1 [Nat.mod_eq_of_lt]
  -- simp
  -- nth_rewrite 2 [Nat.mod_eq_of_lt]
  -- nth_rewrite 1 [Nat.mod_eq_of_lt]
  -- rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
  -- bvify []
  -- bv_decide
  -- try_apply_lemma_hyps []
