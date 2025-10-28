import BVModEq.SolveMLE
open Lean Meta Elab Tactic
open Lean.Parser.Tactic

abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry

instance NotTwo: BVModEq.GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry

set_option maxHeartbeats  20000000000000000000


syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")? : tactic


@[tactic translateHypothesis]
elab_rules : tactic
| `(tactic| translate_hypothesis $h:ident $[ [ $ids,* ] ]? ) => withMainContext do
  /- Build simpArg array (empty if none provided) -/
  let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
  if let some idList := ids then
    for i in idList.getElems do
      let sa ← `(simpArg| $i:term)
      let ua : TSyntax [`Lean.Parser.Tactic.simpStar,
                        `Lean.Parser.Tactic.simpErase,
                        `Lean.Parser.Tactic.simpLemma] := ⟨sa.raw⟩
      sargs := sargs.push ua
  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| simp [BVModEq.ZMod.eq_if_val] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| rw [BVModEq.BitVec_ofNat_eq_iff 256] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| bvify [$[$sargs],*] at $(mkIdent h.getId):ident))


partial def countAnds (e : Expr) : Nat :=
   match e with
  | .const ``And _ =>
      let args := e.getAppArgs
      if h : args.size ≥ 2 then
        let a := args[0]!
        let b := args[1]!
        1 + countAnds a + countAnds b
      else
        1
  | _ =>
      match e with
      | .app f x => countAnds f + countAnds x
      | _ => 0


syntax (name := translateGoal)
  "translate_goal" ppSpace ("[" ident,* "]")? : tactic


@[tactic translateGoal]
elab_rules : tactic
| `(tactic| translate_goal $[[ $ids,* ]]?) => withMainContext do
  /- Build simpArg array (empty if none provided) -/
  let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
  if let some idList := ids then
    for i in idList.getElems do
      let sa ← `(simpArg| $i:term)
      let ua : TSyntax [`Lean.Parser.Tactic.simpStar,
                        `Lean.Parser.Tactic.simpErase,
                        `Lean.Parser.Tactic.simpLemma] := ⟨sa.raw⟩
      sargs := sargs.push ua
  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv ))
  evalTactic (← `(tactic| simp [BVModEq.ZMod.eq_if_val]))
  evalTactic (← `(tactic| valify [$[$sargs],*] ) )
  evalTactic (← `(tactic| try simp ) )
  --evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
  --evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] ))
  evalTactic (← `(tactic| rw [BVModEq.BitVec_ofNat_eq_iff 256]))
  evalTactic (← `(tactic| bvify [$[$sargs],*]))
  let g ← getMainGoal
  let t ← g.getType
  let n := countAnds t
  for _ in [:n] do
      evalTactic (← `(tactic| rw [BVModEq.BitVec_ofNat_eq_iff 256]))
  evalTactic (← `(tactic| bvify [$[$sargs],*]))

def isZModIdemEq (e : Expr) : Option Expr :=
  match e with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
    let f := lhs.getAppFn
    if f.isConstOf ``HMul.hMul || f.isConstOf ``Mul.mul then
      let args := lhs.getAppArgs
      if args.size ≥ 2 then
        let a := args[args.size - 2]!
        let b := args[args.size - 1]!
        if a == rhs && b == rhs then some rhs else none
      else none
    else none
  | _ => none

-- def smartTranslateOne (h : TSyntax `ident)
--     (extraArgs :
--       Array (TSyntax [`Lean.Parser.Tactic.simpStar,
--                       `Lean.Parser.Tactic.simpErase,
--                       `Lean.Parser.Tactic.simpLemma])) : TacticM Unit := do
--   let decl ← getLocalDeclFromUserName h.getId
--   let ty   := decl.type
--   match isZModIdemEq ty with
--   | some _ =>
--       /- Case 1: x * x = x  → rewrite + rcases -/
--       evalTactic (← `(tactic| rw [BVModEq.square_eq_one_zero 256] at $(mkIdent h.getId):ident))
--       -- Automatically generate `rcases h with ⟨h_1, h_2⟩`
--       let base := h.getId.toString
--       let h1 := mkIdent (Name.mkSimple s!"{base}_1")
--       let h2 := mkIdent (Name.mkSimple s!"{base}_2")
--       evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident with ⟨$h1, $h2⟩))
--   | none =>
--       /- Case 2: Anything else → normal translate_hypothesis -/
--       if extraArgs.isEmpty then
--         evalTactic (← `(tactic| translate_hypothesis $h))
--       else
--         evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))


-- syntax (name := smartTranslate) "smart_translate" ppSpace
--   ("[" ident,* "]")? : tactic

-- @[tactic smartTranslate]
-- elab_rules : tactic
-- | `(tactic| smart_translate $[[ $ids,* ]]?) => withMainContext do
--   let extraArgs :
--     Array (TSyntax [`Lean.Parser.Tactic.simpStar,
--                     `Lean.Parser.Tactic.simpErase,
--                     `Lean.Parser.Tactic.simpLemma]) := #[]

--   match ids with
--   | some idList =>
--       for h in idList.getElems do
--         smartTranslateOne h extraArgs
--   | none =>
--       for ldecl in (← getLCtx) do
--         if !ldecl.isImplementationDetail then
--           smartTranslateOne (mkIdent ldecl.userName) extraArgs


def flattenAnds (h : TSyntax `ident) : TacticM (Array (TSyntax `ident)) :=
  withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hyp `{h.getId}` in context"

    let ty ← whnf decl.type
    let num := countAnds ty + 1
    if num == 0 then
      return #[h]

    -- perform `rcases h with ⟨h1, h2, ..., hn⟩`
    let names : Array (TSyntax `ident) :=
      (List.range num).map (fun i => mkIdent (Name.mkSimple s!"{h.getId}_{i+1}")) |>.toArray
    evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident with ⟨$[$names],*⟩))
    return names

def smartTranslateOne
    (h : TSyntax `ident)
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma])) : TacticM (Option (TSyntax `ident)) := do
    withMainContext do
    -- Retrieve hypothesis declaration safely
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hypothesis `{h.getId}` in local context"

    let hIdent : TSyntax `ident := mkIdent decl.userName
    let hType ← whnf decl.type
    match isZModIdemEq hType with
    | some _ => do
        evalTactic (← `(tactic| rw [BVModEq.square_eq_one_zero 256] at $(mkIdent h.getId):ident))
        -- name parts as h_1 / h_2
        let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
        let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
        evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $h2⟩))
        return some h1
    | none =>
      logInfo m! "{h}"
        if extraArgs.isEmpty then
          evalTactic (← `(tactic| translate_hypothesis $h))
        else
          evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))
      logInfo m! "Done"
        return none

/-- Batch helper over a list of hypothesis idents.
    Returns the collected `*_1` names from `x*x=x` cases. -/
def smartTranslateMany
    (hs : Array (TSyntax `ident))
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma])) : TacticM (Array (TSyntax `ident)) := do
  let mut picked : Array (TSyntax `ident) := #[]
  for h in hs do
    if let some k ← smartTranslateOne h extraArgs then
      picked := picked.push k
  return picked

/-- One-shot orchestrator:
    intro h; split; smart-translate; translate_goal; bv_decide; try_apply_lemma_hyps [*_1 ...] -/
syntax (name := translateAll) "translate_all" ppSpace
  ("[" ident,* "]")? : tactic

@[tactic translateAll]
elab_rules : tactic
| `(tactic| translate_all $[[ $extraSimp,* ]]?) => withMainContext do
  -- collect optional extra simp args (reuse your pipeline args if you like)
  let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
  if let some idList := extraSimp then
    for i in idList.getElems do
      let sa ← `(simpArg| $i:term)
      let ua : TSyntax [`Lean.Parser.Tactic.simpStar,
                        `Lean.Parser.Tactic.simpErase,
                        `Lean.Parser.Tactic.simpLemma] := ⟨sa.raw⟩
      sargs := sargs.push ua

  -- 1) intro and flatten the big conjunction
  --let h := mkIdent `h
  let name := Name.mkSimple s!"h"
  -- let g ← getMainGoal
  -- try
  --   let (_, g') ← g.intro name
  --   replaceMainGoal [g']
  -- catch _ =>
  --   throwError m!"can't intro"
  --   pure ()
  -- let g' ← getMainGoal
  -- let id : TSyntax `ident ← withMainContext do
  --     let lctx ← getLCtx
  --     let some decl := lctx.findFromUserName? name
  --          | throwError m!"no hyp `{name}`"
  --     pure (mkIdent decl.userName)
  let g ← getMainGoal
  let (fvarId, newGoal) ← g.intro `h        -- introduces h at the Meta level
  setGoals [newGoal]
  let hIdent : TSyntax `ident := mkIdent `h
  let leaves ← flattenAnds hIdent

  --let h : TSyntax `ident := mkIdent decl.userName

  -- -- 2) smart translate each leaf, collect only *_1 from idempotence rewrites
  let collected ← smartTranslateMany leaves sargs

  -- -- 3) goal pipeline
  evalTactic (← `(tactic| translate_goal))
  evalTactic (← `(tactic| bv_decide))

  -- 4) try_apply_lemma_hyps with only the collected *_1; avoid empty []
  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))


abbrev FF0 : Type := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
variable (fresh_pf21_xor_bit0 : FF0)
variable (f : BitVec 8)
variable (e : BitVec 8)
variable (d : BitVec 8)
variable (c : BitVec 8)
variable (b : BitVec 8)
variable (a : BitVec 8)
variable (fresh_pf18_xor_bit0 : FF0)
variable (fresh_pf15_xor_bit0 : FF0)
variable (fresh_pf12_xor_bit0 : FF0)
variable (fresh_pf9_xor_bit0 : FF0)
variable (fresh_pf6_xor_bit0 : FF0)
variable (fresh_pf3_xor_bit0 : FF0)
variable (fresh_pf0_xor_bit0 : FF0)
variable (fresh_pf23_xor_bit2 : FF0)
variable (fresh_pf22_xor_bit1 : FF0)
variable (fresh_pf20_xor_bit2 : FF0)
variable (fresh_pf19_xor_bit1 : FF0)
variable (fresh_pf17_xor_bit2 : FF0)
variable (fresh_pf16_xor_bit1 : FF0)
variable (fresh_pf14_xor_bit2 : FF0)
variable (fresh_pf13_xor_bit1 : FF0)
variable (fresh_pf11_xor_bit2 : FF0)
variable (fresh_pf10_xor_bit1 : FF0)
variable (fresh_pf8_xor_bit2 : FF0)
variable (fresh_pf7_xor_bit1 : FF0)
variable (fresh_pf5_xor_bit2 : FF0)
variable (fresh_pf4_xor_bit1 : FF0)
variable (fresh_pf2_xor_bit2 : FF0)
variable (fresh_pf1_xor_bit1 : FF0)
lemma correct :
((((((((fresh_pf0_xor_bit0) * (fresh_pf0_xor_bit0))) = (fresh_pf0_xor_bit0))) ∧ (((((fresh_pf1_xor_bit1) * (fresh_pf1_xor_bit1))) = (fresh_pf1_xor_bit1))) ∧ (((((fresh_pf2_xor_bit2) * (fresh_pf2_xor_bit2))) = (fresh_pf2_xor_bit2))) ∧ ((((fresh_pf0_xor_bit0) + (((fresh_pf1_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf3_xor_bit0) * (fresh_pf3_xor_bit0))) = (fresh_pf3_xor_bit0))) ∧ (((((fresh_pf4_xor_bit1) * (fresh_pf4_xor_bit1))) = (fresh_pf4_xor_bit1))) ∧ (((((fresh_pf5_xor_bit2) * (fresh_pf5_xor_bit2))) = (fresh_pf5_xor_bit2))) ∧ ((((fresh_pf3_xor_bit0) + (((fresh_pf4_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf5_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf6_xor_bit0) * (fresh_pf6_xor_bit0))) = (fresh_pf6_xor_bit0))) ∧ (((((fresh_pf7_xor_bit1) * (fresh_pf7_xor_bit1))) = (fresh_pf7_xor_bit1))) ∧ (((((fresh_pf8_xor_bit2) * (fresh_pf8_xor_bit2))) = (fresh_pf8_xor_bit2))) ∧ ((((fresh_pf6_xor_bit0) + (((fresh_pf7_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf8_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf9_xor_bit0) * (fresh_pf9_xor_bit0))) = (fresh_pf9_xor_bit0))) ∧ (((((fresh_pf10_xor_bit1) * (fresh_pf10_xor_bit1))) = (fresh_pf10_xor_bit1))) ∧ (((((fresh_pf11_xor_bit2) * (fresh_pf11_xor_bit2))) = (fresh_pf11_xor_bit2))) ∧ ((((fresh_pf9_xor_bit0) + (((fresh_pf10_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf11_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf12_xor_bit0) * (fresh_pf12_xor_bit0))) = (fresh_pf12_xor_bit0))) ∧ (((((fresh_pf13_xor_bit1) * (fresh_pf13_xor_bit1))) = (fresh_pf13_xor_bit1))) ∧ (((((fresh_pf14_xor_bit2) * (fresh_pf14_xor_bit2))) = (fresh_pf14_xor_bit2))) ∧ ((((fresh_pf12_xor_bit0) + (((fresh_pf13_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf14_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf15_xor_bit0) * (fresh_pf15_xor_bit0))) = (fresh_pf15_xor_bit0))) ∧ (((((fresh_pf16_xor_bit1) * (fresh_pf16_xor_bit1))) = (fresh_pf16_xor_bit1))) ∧ (((((fresh_pf17_xor_bit2) * (fresh_pf17_xor_bit2))) = (fresh_pf17_xor_bit2))) ∧ ((((fresh_pf15_xor_bit0) + (((fresh_pf16_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf17_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf18_xor_bit0) * (fresh_pf18_xor_bit0))) = (fresh_pf18_xor_bit0))) ∧ (((((fresh_pf19_xor_bit1) * (fresh_pf19_xor_bit1))) = (fresh_pf19_xor_bit1))) ∧ (((((fresh_pf20_xor_bit2) * (fresh_pf20_xor_bit2))) = (fresh_pf20_xor_bit2))) ∧ ((((fresh_pf18_xor_bit0) + (((fresh_pf19_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf20_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf21_xor_bit0) * (fresh_pf21_xor_bit0))) = (fresh_pf21_xor_bit0))) ∧ (((((fresh_pf22_xor_bit1) * (fresh_pf22_xor_bit1))) = (fresh_pf22_xor_bit1))) ∧ (((((fresh_pf23_xor_bit2) * (fresh_pf23_xor_bit2))) = (fresh_pf23_xor_bit2))) ∧ ((((fresh_pf21_xor_bit0) + (((fresh_pf22_xor_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf23_xor_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((if (((BVModEq.bool_to_bv 1 a[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 b[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 c[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 d[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 e[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if (((BVModEq.bool_to_bv 1 f[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) → ((((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf0_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf3_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf6_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[3]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf9_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[4]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf12_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[5]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf15_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[6]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf18_xor_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor (BitVec.xor a b) c) d) e) f)[7]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf21_xor_bit0))))))
 := by
  -- intro h
  -- rcases h with ⟨
  -- h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
  -- h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
  -- h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
  -- h31, h32⟩
  -- smart_translate [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
  -- h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
  -- h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
  -- h31, h32]
  -- translate_goal
  -- bv_decide
  -- try_apply_lemma_hyps [h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1,
  --   h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1, h20_1,
  --   h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1, h30_1,
  --   h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1, h40_1,
  --   h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1]
  translate_all
