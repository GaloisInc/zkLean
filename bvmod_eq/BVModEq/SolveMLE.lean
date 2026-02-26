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

namespace BVModEq


syntax (name := SolveMLE) "solveMLE " num  (" [" ident,* "]")?: tactic

partial def introAll (i : Nat := 0) (revNames : List Name := []) : TacticM (List Name) := do
  let name := Name.mkSimple s!"h{i}"
  let g ← getMainGoal
  try
    let (_, g') ← g.intro name
    replaceMainGoal [g']
  catch _ => return revNames.reverse
  introAll (i + 1) (name :: revNames)

private def termFor (nm : Name) : TacticM (TSyntax `term) := withMainContext do
  match (← getLCtx).findFromUserName? nm with
  | some d => pure ⟨(mkIdent d.userName).raw⟩
  | none   => pure ⟨(mkIdent nm).raw⟩

syntax (name := findModLT) "findModLT " num : tactic

@[tactic findModLT] def evalfindModLT : Tactic := fun stx => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let (fn, args) := ty.getAppFnArgs
   let some n := stx[1].isNatLit?
    | throwError "usage: findModLT <n> (natural number)"
  match fn with
    | ``Iff =>
        let (fn2, args2) := args[args.size -1]!.getAppFnArgs
        match fn2 with
        | ``Eq =>
           let (fn3, args3) := args2[args2.size -1]!.getAppFnArgs
           match fn3 with
           | ``HMod.hMod =>
                let lhs := args3[args3.size - 2]!    -- adjust if your indexing changes
        -- build 2 ^ n as a Nat expression
                let twoPowN : Expr := mkApp2 (mkConst ``Nat.pow) (mkNatLit 2) (mkNatLit n)
                let prop ← mkAppM ``LT.lt #[lhs, twoPowN]
                let pr ← g.withContext do mkFreshExprMVar prop
                let gWithHyp  ← g.assert `Leq prop pr
                --let hyp ← g.withContext do pr.mvarId!.assert `Leq prop pr
                -- let gWithHyp ←  g.assert `Leq prop pr
                setGoals [pr.mvarId!, gWithHyp]
           | _ =>
                let lhs := args2[args2.size - 1]!    -- adjust if your indexing changes
        -- build 2 ^ n as a Nat expression
                let twoPowN : Expr := mkApp2 (mkConst ``Nat.pow) (mkNatLit 2) (mkNatLit n)
                let prop ← mkAppM ``LT.lt #[lhs, twoPowN]
                let pr ← g.withContext do mkFreshExprMVar prop
                let gWithHyp  ← g.assert `Leq prop pr
                setGoals [pr.mvarId!, gWithHyp]
        | _ => pure ()
    | _ => pure ()


set_option maxHeartbeats  20000000000000000000
elab_rules : tactic
| `(tactic| solveMLE  $N:num $[[$extras:ident,*]]? ) => do
  let n := N.getNat
  let extraList : List Syntax := (extras.map (·.getElems.toList)).getD []
  let hyps ← introAll
  let mut ids : List (TSyntax `ident) := []
  let first :: rest := hyps | return ()
  let _firstId : TSyntax `ident := mkIdent first
  let g ← getMainGoal
  for x in rest do
    let id : TSyntax `ident ← g.withContext do
      let lctx ← getLCtx
      let some decl := lctx.findFromUserName? x
           | throwError m!"no hyp `{x}`"
      pure (mkIdent decl.userName)
    try
    -- we might have extra hypothesis that don't need to be rewritten
      let extractLemma:= `BVModEq ++ Name.mkSimple s!"extract_bv_rel"
      evalTactic (← `(tactic| rw [$(mkIdent extractLemma):ident] at $id:ident))
      let n1 := Name.mkSimple s!"{x}_1"
      let n2 := Name.mkSimple s!"{x}_2"
      let id1 : TSyntax `ident := mkIdent n1
      let id2 : TSyntax `ident := mkIdent n2
      ids := ids ++ [id1]
      evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩))
    catch _ => pure ()
  let id : TSyntax `ident ← g.withContext do
      let lctx ← getLCtx
      let some decl := lctx.findFromUserName? hyps[0]!
           | throwError m!"no hyp"
      pure (mkIdent decl.userName)
  let map_f := `BVModEq ++ Name.mkSimple s!"map_f_to_bv"
  evalTactic (← `(tactic| unfold $(mkIdent map_f):ident at $id:ident; simp at $id:ident))
  let n1 := Name.mkSimple s!"h_1"
  let n2 := Name.mkSimple s!"h_2"
  let id1 : TSyntax `ident := mkIdent n1
  let id2 : TSyntax `ident := mkIdent n2
  evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩; rw [ZMod.eq_if_val]))
  let idsArr : Array (TSyntax `ident) := ids.toArray
  let i <- getMainGoal
  --logInfo m!"{ids}"

  evalTactic (← `(tactic| try valify [$[$idsArr:ident],*]))
  let g ← getMainGoal
  let gt <- g.getType
  let ty ← instantiateMVars (← g.getType)
  let t' ← firstCompositeInsideVal? ty
  let mut valhelp := false
  match t' with
  | some t =>
    valhelp := true
    evalTactic (← `(tactic| valify_helper [$[$idsArr:ident],*]))
    -- val(1 - exp ) --> 1 - val(exp) show that exp <= 1 which range analysis can do
    -- val(y - x*y) --> x*y <= y which range analysis cannot do b/c variable on RHS
        --                x*y - y <= 0 and then rewrite back?
    evalTactic (← `(tactic| intro NatLeq; intro ZLeq; intro Eq; simp at Eq ; rw [Eq] ; valify [$[$idsArr:ident],*]))
  | none  => pure ()
  evalTactic (← `(tactic| try simp )) -- rw [Nat.mod_eq_of_lt]))
  let nSyntax : TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString n)⟩
  evalTactic (← `(tactic| findModLT $nSyntax) )
  -- -- let g <- getMainGoal
  -- logInfo m!"Hello?{g}"
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$idsArr:ident],*]))
  logInfo m!"Passed range analysis"
  if valhelp then
       evalTactic (← `(tactic|
       simp [<- Nat.lt_add_one_iff];
       simp [Nat.mul_assoc] at NatLeq;
       apply NatLeq;
       ))
  evalTactic (← `(tactic| try simp))

  evalTactic (← `(tactic| intro Leq))
  evalTactic (← `(tactic| try rw [Nat.mod_eq_of_lt]))
  let lemmaName := `BVModEq ++ Name.mkSimple s!"BitVec_ofNat_eq_iff"
  evalTactic (← `(tactic| rw [$(mkIdent lemmaName):ident $(Quote.quote n)]))



-- --   -- TODO : Should fv1 should be passed in as parameters?
  let fv1T : TSyntax `term := (← termFor `fv1)
  let fv2T : TSyntax `term := (← termFor `fv2)
  let foT  : TSyntax `term := (← termFor `foutput)
  if valhelp then
   evalTactic (← `(tactic| simp [Nat.lt_succ_iff] at NatLeq))
   evalTactic (← `(tactic| simp [Nat.mul_assoc] at NatLeq))
   evalTactic (← `(tactic| try bvify [NatLeq]))
   evalTactic (← `(tactic| try bvify [$[$idsArr:ident],*]))
   evalTactic (← `(tactic| clear NatLeq; clear ZLeq; clear Eq))
  else
     evalTactic (← `(tactic| try bvify [$[$idsArr:ident],*]))
  evalTactic (← `(tactic|  try unfold BVModEq.bool_to_bv))
  evalTactic (← `(tactic| clear Leq))
  -- -- TODO: I don't the number bits should be hardcoded like this
  evalTactic (← `(tactic|set a   := ($foT).val))
  let mut index := 0
  while index < ids.length/2 do
    -- names for the bound and its equality
    let idName  := Name.mkSimple s!"b0_{index}"

    -- identifiers/syntax nodes
    let idSyn   : TSyntax `Lean.binderIdent := ⟨(mkIdent idName).raw⟩
    let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    -- safest access: .get! (parses reliably inside quotations)
    evalTactic (← `(tactic|
      set $idSyn := $fv1T[$idxSyn]
    ))
    index := index + 1
  index := 0
  while index < ids.length/2 do
    -- names for the bound and its equality
    let idName  := Name.mkSimple s!"b1_{index}"

    -- identifiers/syntax nodes
    let idSyn   : TSyntax `Lean.binderIdent := ⟨(mkIdent idName).raw⟩
    let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    -- safest access: .get! (parses reliably inside quotations)
    evalTactic (← `(tactic|
      set $idSyn := $fv2T[$idxSyn]
    ))
    index := index + 1
  match extraList  with
  | [id1, id2] =>
      evalTactic (← `(tactic|
        unfold $(mkIdent id1.getId);
        repeat unfold  $(mkIdent id2.getId)
      ))
  | [id1] =>
     evalTactic (← `(tactic|
        unfold $(mkIdent id1.getId);
      ))
  | _ =>
      pure ()
  logInfo m!"Started bv decide"
  evalTactic (← `(tactic| bv_decide (config := {timeout := 300}) ;
    apply $id1:ident ;
    ))
  evalTactic (← `(tactic|  apply Nat.lt_of_lt_of_le;
  apply Leq;
  decide))
  try
    evalTactic (← `(tactic|  apply Nat.lt_of_lt_of_le;
    apply Leq;
    decide))
  catch _ => pure ()

end BVModEq
