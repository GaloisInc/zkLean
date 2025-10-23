import BVModEq.RangeAnalysis
import BVModEq.Valify

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace BVModEq

private def isArithmeticHead (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n =>
      n == ``HAdd.hAdd || n == ``Add.add ||
      n == ``HSub.hSub || n == ``Sub.sub ||
      n == ``HMul.hMul || n == ``Mul.mul ||
      n == ``Neg.neg   || n == ``HMod.hMod ||
      n == ``HPow.hPow || n == ``Pow.pow
  | none => false

private def compositeInsideValHere? (e : Expr) : MetaM (Option Expr) := do
  --let e ← whnf e
  if e.isAppOf ``ZMod.val then
    let args := e.getAppArgs

    if let some t := args.back? then
      if isArithmeticHead t then
        --logInfo m!"{args}"
        return some e
  pure none

/-- DFS for first subterm of the form `ZMod.val t` where `t` is composite
(arithmetic-headed). -/
partial def firstCompositeInsideVal? (e : Expr) : MetaM (Option Expr) := do
  if let some t ← compositeInsideValHere? e then
    return some t
  match e with
  | .app f a =>
      if let some r ← firstCompositeInsideVal? f then return some r
      firstCompositeInsideVal? a
  | _ =>
    pure none


partial def pushValToNat (n : Expr) (t : Expr) : MetaM Expr := do
  let head := t.getAppFn
  let args := t.getAppArgs
  match head.constName? with
  | some name =>
    --logInfo m!"{name}"
    if name == ``HAdd.hAdd || name == ``Add.add then
      -- binary add: ... a b
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.add) a' b'
    else if name == ``HSub.hSub || name == ``Sub.sub then
      -- binary sub: ... a b (literal Nat subtraction)
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.sub) a' b'
    else if name == ``HMul.hMul || name == ``Mul.mul then
      -- binary mul: ... a b
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.mul) a' b'
    else
      -- atomic fallback: ZMod.val n t
      return mkApp2 (mkConst ``ZMod.val) n t
  | none =>
      -- not constant-headed; treat as atomic
      return mkApp2 (mkConst ``ZMod.val) n t


def pushValToNatMod (n : Expr) (t : Expr) : MetaM Expr := do
  let e ← pushValToNat n t
  let modExpr ← mkAppM ``HMod.hMod #[e, n]
  return modExpr

/-- `findInsideVal` optionally binds the found composite term:
`findInsideVal` or `findInsideVal => name`. -/
syntax (name := findInsideVal) "findInsideVal" (ppSpace "=>" ident)? : tactic


@[tactic findInsideVal] def evalFindInsideVal : Tactic := fun stx => do
  let g ← getMainGoal
  let gt ← g.getType
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    logInfo m!"{gt.getAppApps}"
    let some t ← firstCompositeInsideVal? ty
      | return ()
    let args := t.getAppArgs
    logInfo m!"NEW EQ: {t}"
    --logInfo m!"found: {← ppExpr t}"
    let exp ← pushValToNat args[0]! args[1]!
    let e ← mkAppM ``HMod.hMod #[exp, args[0]!]
    let args2 := args[1]!.getAppApps
    let e2 := args2[args2.size-1]!
    let args3:= e2.getAppArgs
    let prop ← mkEq t e
    let pr ←  g.withContext do mkFreshExprMVar prop
    let rhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -1]!
    let lhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -2]!
    let prop2 ← g.withContext do mkAppM ``LE.le #[rhs, lhs]
    let pr2 ← g.withContext do mkFreshExprMVar prop2
    let hm ← g.withContext do pr.mvarId!.assert `vNat prop2 pr2

    let gWithHyp ← g.withContext do g.assert `vNat prop pr
    let gWithHyp2 ← g.withContext do  gWithHyp.assert `subleq prop2 pr2
    setGoals [pr2.mvarId!, hm, gWithHyp2]

set_option maxHeartbeats  20000000000000000000

lemma ZMod.val_sub_mod (h0 : Fact (1 < ff)) (h : x.val ≤ (1 : ZMod ff).val)
  : ((1 : ZMod ff) - x).val = (1 - x.val)%ff := by
  valify [h0] at h
  valify [h]
  rw [Nat.mod_eq_of_lt]
  try_apply_lemma_hyps [h]
  apply h0.out


lemma Nat.val_sub_mod (h0 : Fact (1 < ff)) (h : x ≤ 1)
  : (1 - (x%ff))%ff = (1 - x)%ff := by
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  apply Nat.lt_of_le_of_lt
  apply Nat.sub_le
  apply h0.out
  apply Nat.lt_of_le_of_lt
  apply h
  apply h0.out
  rw [Nat.mod_eq_of_lt]
  apply Nat.lt_of_le_of_lt
  apply Nat.sub_le
  apply h0.out
  apply Nat.lt_of_le_of_lt
  apply h
  apply h0.out


def assertFirstAcrossGoals (name : Name) : TacticM Unit := do
  let gs ← getGoals
  if gs.isEmpty then return ()
  let g := gs.head!
  let prop ← g.withContext do instantiateMVars (← g.getType)

  -- One shared metavariable for the proof of `prop`
  let pr ← mkFreshExprMVar prop
  -- Assert `prop` into every goal, using the SAME proof metavariable `pr`
  let mut newGoals := #[]
  for g in gs do
    let g' ←  g.withContext do g.assert name prop pr
    newGoals := newGoals.push g'
  -- Put the shared proof goal first, then all updated goals
  setGoals (pr.mvarId! :: newGoals.toList)

elab "share_first_goal" : tactic => assertFirstAcrossGoals `h


syntax (name := valifyHelper) "valify_helper" ("[" ident,* "]")? : tactic


@[tactic valifyHelper]
elab_rules : tactic
 | `( tactic| valify_helper [$ids,*]) => withMainContext do
    let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
    for i in ids.getElems do
      let sa ← `(simpArg| $i:term)
      let ua :
      TSyntax [`Lean.Parser.Tactic.simpStar,
               `Lean.Parser.Tactic.simpErase,
               `Lean.Parser.Tactic.simpLemma] :=
      ⟨sa.raw⟩
      sargs := sargs.push ua
    -- what this does given an (1 - exp).val ∈ g we get
    -- g1: exp.val <= 1
    -- g2: g1 -> ( 1- exp.val) = 1 - exp.val
    -- g3: g2 -> g
    -- TODO: This is not efficient!! we end up proving some things
    -- twice; need to look into how to make this more efficient!
    --evalTactic (← `(tactic| findInsideVal))
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let some t ← firstCompositeInsideVal? ty
          | return ()
    let args := t.getAppArgs
    let exp ← pushValToNat args[0]! args[1]!
    let e ← mkAppM ``HMod.hMod #[exp, args[0]!]
    let args2 := args[1]!.getAppApps
    let e2 := args2[args2.size-1]!
    let args3:= e2.getAppArgs
    let prop ← mkEq t e
    let pr ← g.withContext do mkFreshExprMVar prop
    let rhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -1]!
    let lhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -2]!
    let prop2 ← g.withContext do mkAppM ``LE.le #[rhs, lhs]
    let pr2 ← g.withContext do mkFreshExprMVar prop2
    let hm ← g.withContext do pr.mvarId!.assert `vNat prop2 pr2
    let gWithHyp ← g.withContext do g.assert `vNat prop pr
    let gWithHyp2 ← g.withContext do gWithHyp.assert `subleq prop2 pr2
    setGoals [pr2.mvarId!, hm, gWithHyp2]
    let mut g ← getMainGoal
    logInfo m!"G0: {g}"
    evalTactic (← `(tactic| valify [$[$sargs],*]; ))
    evalTactic (← `(tactic| try simp; ))
    evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]; simp [← Nat.lt_add_one_iff]))
    assertFirstAcrossGoals `h
    g ← getMainGoal
    logInfo m!"G1: {g}"
    evalTactic (← `(tactic| focus try_apply_lemma_hyps [$[$ids],*]))
    g ← getMainGoal
    logInfo m!"G2: {g}"
    evalTactic (← `(tactic| intro NatLeq))
    evalTactic (← `(tactic|
      exact Nat.lt_of_lt_of_le NatLeq (by decide)))
    g ← getMainGoal
    evalTactic (← `(tactic|
      intro NatLeq ))
    evalTactic (← `(tactic|
      exact Nat.lt_of_lt_of_le NatLeq (by decide)))
    -- evalTactic (← `(tactic|
    --   intro NatLeq
    --   intro Leq
    -- ))
    -- evalTactic (← `(tactic| valify [$[$sargs],*]; try simp))
    -- evalTactic (← `(tactic| simp [ZMod.val_sub_mod Leq]))
    -- evalTactic (← `(tactic| valify [$[$sargs],*]))
    -- evalTactic (← `(tactic| try simp))
    -- evalTactic (← `(tactic| rw [Nat.val_sub_mod]))
    -- evalTactic (← `(tactic| simp [← Nat.lt_add_one_iff]; apply NatLeq))


abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513

instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry

instance NotTwo: BVModEq.GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry


example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) -> ( (1: ZMod ff) - ( (fv[0]*fv[1]  ))).val < 7 := by
  intro h1 h2 h3
  valify_helper [h1, h2, h3]
  intro NatLeq
  intro Leq
  valify [h1, h2, h3]
  simp
  --try simp [ZMod.val_sub_mod Leq]
  rw [ZMod.val_sub]
  --rw [Nat.mod_eq_of_lt]
  valify [h1, h2, h3]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  try_apply_lemma_hyps []
  apply Nat.lt_succ_iff.mp NatLeq
  try_apply_lemma_hyps []

  rw [Nat.val_sub_mod]



lemma hello {b a : BitVec 2} : (BVModEq.map_bv_to_f ff b + 3 - BVModEq.map_bv_to_f ff a).val = (BVModEq.map_bv_to_f ff b).val + 3 - (BVModEq.map_bv_to_f ff a).val := by
  unfold BVModEq.map_bv_to_f
  simp
  valify_helper []
  -- rw [ZMod.val_sub]
  -- valify []
  -- simp
  -- rw [Nat.mod_eq_of_lt]
  -- rw [Nat.mod_eq_of_lt]
  -- rw [Nat.mod_eq_of_lt]
  -- try_apply_lemma_hyps []
  -- valify []
  -- simp
  -- rw [Nat.mod_eq_of_lt]
  -- rw [Nat.mod_eq_of_lt]
  -- try_apply_lemma_hyps []
