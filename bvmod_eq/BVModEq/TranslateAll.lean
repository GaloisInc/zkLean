import Lean.Elab.Term
import Lean.Meta.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Kleene
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Std.Data.HashMap.Basic

import BVModEq.RangeAnalysis
--import BVModEq.BVify
import BVModEq.Mappings

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace BVModEq

set_option maxHeartbeats 20000000000

syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")? : tactic

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


def compositeInsideIfHere? (e : Expr) : MetaM (Option Expr) := do
  --let e ← whnf e
  if e.isAppOf ``ite then
    let args := e.getAppArgs

    if h : args.size > 1 then
      let cond := args[1]

      -- Normalize (optional but safer)

      -- Check if it's an equality
      if cond.isAppOf ``Eq then
        let eqArgs := cond.getAppArgs
        -- eqArgs = #[α, lhs, rhs] because Eq α lhs rhs has implicit type param α
        if h2 : eqArgs.size > 1 then
          let lhs := eqArgs[1]
            if lhs.isAppOf ``getElem then
                let lhsArgs := lhs.getAppArgs
                if lhsArgs.size > 5 then
                  if lhsArgs[5]!.isAppOf ``BitVec.ofNat then
                        return some lhs
  pure none

/-- DFS for first subterm of the form `ZMod.val t` where `t` is composite
(arithmetic-headed). -/
 def firstCompositeInsideIf? (e : Expr) : MetaM (Option Expr) := do
  if let some t ← compositeInsideIfHere? e then
    return some t
  match e with
  | .app f a =>
      if let some r ← firstCompositeInsideIf? f then return some r
      firstCompositeInsideIf? a
  | .mdata _ b => firstCompositeInsideIf? b
  | .proj _ _ b => firstCompositeInsideIf? b
  | _ =>
    pure none



partial def introAll (i : Nat := 0) (revNames : List Name := []) : TacticM (List Name) := do
  let name := Name.mkSimple s!"h{i}"
  let g ← getMainGoal
  try
    let (_, g') ← g.intro name
    replaceMainGoal [g']
  catch _ => return revNames.reverse
  introAll (i + 1) (name :: revNames)

open Lean

partial def countMinusOps2 (e : Expr) : MetaM Nat := do
  -- print the head for debugging
  let e ← instantiateMVars e


  -- detect subtraction at this node
  let here :=
    match e.getAppFn with
    | .const n _ =>
        if n == ``HSub.hSub || n == ``Sub.sub || n == ``Nat.sub then 1 else 0
    | _ => 0

  -- recurse structurally over ALL Expr forms
  match e with
  | .app _ _ =>
      let args := e.getAppArgs
      let mut acc := here
      for a in args do
        acc := acc + (← countMinusOps2 a)
      return acc

  | .lam _ _ b _ =>
      return here + (← countMinusOps2 b)

  | .forallE _ ty b _ =>
      return here + (← countMinusOps2 ty) + (← countMinusOps2 b)

  | .letE _ t v b _ =>
      return here + (← countMinusOps2 t)
                  + (← countMinusOps2 v)
                  + (← countMinusOps2 b)

  | .proj _ _ b =>
      return here + (← countMinusOps2 b)

  | .mdata _ b =>
      return here + (← countMinusOps2 b)

  | .const _ _ | .sort _ | .lit _ | .bvar _ | .fvar _ | .mvar _ =>
      return here



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
  let hName := h.getId   -- the Name of the identifier
  let i ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    countMinusOps2 decl.type
  logInfo m! "MINUSES HIP {i}"

  -- TO DO THIS SHOULD BE A TRY CATCH LOOP!


  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  at $(mkIdent h.getId):ident))
  if i > 0 then
     evalTactic (← `(tactic|  try rw [sub_add_right_recursive] at $(mkIdent h.getId):ident))

  evalTactic (← `(tactic| try simp [BVModEq.ZMod.eq_if_val] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  for _ in [:i] do
       evalTactic (← `(tactic| try rw [ZMod.val_sub_mod] at $(mkIdent h.getId):ident))
       evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident ) )
       evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
       evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
  evalTactic (← `(tactic| try rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256] at $(mkIdent h.getId):ident))
  for _ in [:i] do
      evalTactic (← `(tactic| try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))




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


partial def loopUntilDone : TacticM Unit := do
  let g ← getMainGoal
  let t ← g.getType
  let t2 <- instantiateMVars t

  let res ← firstCompositeInsideIf? t2
  match res with
  | none =>
      logInfo "✅ Done — no composite expressions left inside any `if`."
      pure ()

  | some if_comp =>
      -- Show we found something
      logInfo m!"🔍 Found composite: {if_comp}"

      -- Turn Expr into Syntax so we can splice it
      let ifSyn ← PrettyPrinter.delab if_comp

      -- Generate a fresh name: c₁, c₂, something unique

      -- set c := ...
      evalTactic (← `(tactic| set c := $(ifSyn) with hc))

      -- Call your custom tactic on it
      evalTactic (← `(tactic| translate_hypothesis hc))

      -- Simplify the goal using this new equality
      evalTactic (← `(tactic| all_goals try simp [hc]))

      -- Recurse on updated goal
      loopUntilDone

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
  --logInfo m! "Minuses {i}"
  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv ))
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  ))
  evalTactic (← `(tactic| try rw [map_f_to_bv_circ_spec] ))
  evalTactic (← `(tactic| all_goals try rw [<- sub_eq_add_neg]))
  let mut g ← getMainGoal
  let mut t ← g.getType
  let i := countMinusOps t

  --TO DO THIS SHOULD BE A TRY CATCH LOOP!
  if i > 0 then
     evalTactic (← `(tactic| all_goals try rw  [sub_add_right_recursive]))
  evalTactic (← `(tactic| try simp [BVModEq.ZMod.eq_if_val]))
  evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
  evalTactic (← `(tactic| try simp ) )

  if i > 0 then
    --  evalTactic (← `(tactic|  try rw [<- sub_eq_add_neg]))
    --  evalTactic (← `(tactic|  try rw [sub_add_right_recursive]))
    for _ in [:i] do
       evalTactic (← `(tactic| try rw [ZMod.val_sub_mod]))
       evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
       evalTactic (← `(tactic| try simp ) )
       evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
  loopUntilDone
  evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
  evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
--   unfold BVModEq.bool_to_bv
--  unfold BVModEq.map_bv_to_f
--  rw [map_f_to_bv_circ_spec]
--  --rw [map_f_to_bv_circ_spec]
--  all_goals rw [<- sub_eq_add_neg]
--  all_goals rw [sub_add_right_recursive]
--  --rw [sub_add_right_recursive]
--  simp [BVModEq.ZMod.eq_if_val]
--  rw [ZMod.val_sub_mod]
--  --rw [ZMod.val_sub_mod]
--  valify
--  simp
--  set c :=(BitVec.ofNat 2
--                   ((b.toNat + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                     a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] with hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
--  bvify at hc
--  simp [hc]
  -- TO DO THIS SHOULD BE A TRY CATCH LOOP!
--   if i > 0 then
--      evalTactic (← `(tactic|  try simp [sub_add_right_recursive]))

--   evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv ))
--   evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  ))
--   evalTactic (← `(tactic| rw  [BVModEq.map_f_to_bv_circ_spec]))
--   evalTactic (← `(tactic| try simp [BVModEq.ZMod.eq_if_val]))
--  -- rw  [BVModEq.map_f_to_bv_circ_spec]
--   evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
--   evalTactic (← `(tactic| try simp ) )

--   -- this currently counts 1-x which it should not
--   if i > 0 then
--     --  evalTactic (← `(tactic|  try rw [<- sub_eq_add_neg]))
--     --  evalTactic (← `(tactic|  try rw [sub_add_right_recursive]))
--     for _ in [:i] do
--        evalTactic (← `(tactic| rw [ZMod.val_sub_mod]))
--        evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
--        evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
-- --        evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  if i > 0 then
    for _ in [:i] do
      evalTactic (← `(tactic|  try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] ) )
  let n := countAnds t
  for _ in [:n] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))

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
    --logInfo m! "We are here?"
    let hType ← whnf decl.type
    --logInfo m! "{hType}"
    match isZModIdemEq hType with
    | some _ => do
        --logInfo m! "we are we not here..."
        evalTactic (← `(tactic| rw [BVModEq.square_eq_one_zero 256] at $(mkIdent h.getId):ident))
        -- name parts as h_1 / h_2
        let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
        let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
        evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $h2⟩))
        return some h1
    | none =>
      --logInfo m! "{h}"
        if extraArgs.isEmpty then
          evalTactic (← `(tactic| translate_hypothesis $h))
        else
          evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))
      --logInfo m! "Done"
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
  --logInfo m! "ARRAY {hs}"
  for h in hs do
    --logInfo m! "{h}"
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

  evalTactic (← `(tactic| try simp))
  let gs ← getGoals
  if gs.isEmpty then
    logInfo "✅ No goals left!"
    return

  let name := Name.mkSimple s!"h"
  let g ← getMainGoal
  --let collected ←
 -- try
  let hyps : List Name ← introAll
  let mut ids : Array (TSyntax `ident) := #[]
    ---et (fvarId, newGoal) ← g.intro `h
  let g ← getMainGoal

  for x in hyps do
      let id : TSyntax `ident ← g.withContext do
        let lctx ← getLCtx
        let some decl := lctx.findFromUserName? x
          | throwError m!"no hyp `{x}`"
        pure (mkIdent decl.userName)

      ids := ids.push id
  if ids.size == 1 then
    try
      ids <- flattenAnds ids[0]!
    catch _ => pure ()

  let collected := (← smartTranslateMany ids sargs)
  -- catch _ =>
  --logInfo m! "No hyps?"
  --   pure #[]


  evalTactic (← `(tactic| translate_goal))
  evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))

  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
  let mut goals ← getGoals
  while (!goals.isEmpty) do
    evalTactic (← `(tactic| translate_goal))
    evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
    goals ← getGoals






abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance Notwo: BVModEq.GtTwo (ffff0) := by sorry

abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
variable (b : BitVec 1)
variable (a : BitVec 1)
lemma correct :
((((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 2  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (BitVec.ult a b)))))))
 := by
 translate_all


--  sorry
--  try_apply_lemma_hyps []
--  try_apply_lemma_hyps []



--                    ((b.toNat + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                      a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] with hc
--  translate_hypothesis hc
--  simp [hc]
--  set c :=(BitVec.ofNat 2
--                    ((b.toNat + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                      a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513))[1] with hc
--  translate_hypothesis hc
--  simp [hc]







-- REAL SOLUTION
--  unfold BVModEq.bool_to_bv
--  unfold BVModEq.map_bv_to_f
--  rw [map_f_to_bv_circ_spec]
--  --rw [map_f_to_bv_circ_spec]
--  all_goals rw [<- sub_eq_add_neg]
--  all_goals rw [sub_add_right_recursive]
--  --rw [sub_add_right_recursive]
--  simp [BVModEq.ZMod.eq_if_val]
--  rw [ZMod.val_sub_mod]
--  --rw [ZMod.val_sub_mod]
--  valify
--  simp
--  set c :=(BitVec.ofNat 2
--                   ((b.toNat + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                     a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] with hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
--  bvify at hc
--  simp [hc]
--  set c :=(BitVec.ofNat 2
--                   ((b.toNat + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                     a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513))[1] with hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Nat.mod_eq_of_lt] at hc
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at hc
--  bvify at hc
--  simp [hc]
--  rw [Nat.mod_eq_of_lt]
--  rw [Nat.mod_eq_of_lt]
--  rw [Nat.mod_eq_of_lt]
--  rw [BVModEq.BitVec_ofNat_eq_iff 256]
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
--  bvify
--  bv_normalize
--  bv_decide
--  all_goals try simp
--  try_apply_lemma_hyps []
--  sorry
--  sorry
--  sorry
--  try_apply_lemma_hyps []













    -- remove minus for the ZVal

--  rw [BVModEq.map_f_to_bv_circ_spec]
--  all_goals simp [<- sub_eq_add_neg]
--  --all_goals simp [sub_add_right_recursive]
--  rw [BVModEq.ZMod.eq_if_val]
--  -- rw  [BVModEq.map_f_to_bv_circ_spec]
--  --valify
--  rw [ZMod.val_sub_mod]
--        evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
--        evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
--        evalTactic (← `(tactic| try simp))
