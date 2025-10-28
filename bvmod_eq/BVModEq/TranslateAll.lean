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

import BVModEq.ValifyHelper
import BVModEq.BVify
import BVModEq.Mappings

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace BVModEq


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
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  at $(mkIdent h.getId):ident))
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
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  ))
  evalTactic (← `(tactic| simp [BVModEq.ZMod.eq_if_val]))
  evalTactic (← `(tactic| valify [$[$sargs],*] ) )
  evalTactic (← `(tactic| try simp ) )

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


  let name := Name.mkSimple s!"h"

  let g ← getMainGoal
  let (fvarId, newGoal) ← g.intro `h
  setGoals [newGoal]
  let hIdent : TSyntax `ident := mkIdent `h
  let leaves ← flattenAnds hIdent

  let collected ← smartTranslateMany leaves sargs


  evalTactic (← `(tactic| translate_goal))
  evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))

  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
