import Lean
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval
import BVModEq.lemmas

open Lean Meta Elab Tactic

lemma Nat.mul_comm_ofNat (a n : Nat) :
   (OfNat.ofNat n) * a = a* (OfNat.ofNat n : Nat) := by
  rw [Nat.mul_comm ]

lemma mul_comm_num_left (n t : ℕ) :
  (n : ℕ) * t = t * (n : ℕ) := by
  simpa using Nat.mul_comm (n : ℕ) t

lemma BitVec.toNatLT {bw} {a : BitVec bw}:
  a.toNat <= 2^bw -1 := by
  have h : a.toNat < 2 ^ bw := a.toFin.isLt
  exact Nat.le_pred_of_lt h

def mkAddNat (es : List Expr) : Expr :=
  match es with
  | []      => mkNatLit 0
  | [e]     => e
  | e :: es => mkApp2 (mkConst ``Nat.add) e (mkAddNat es)

-- rebeuilding a mux expression factored
def rebuild (x sumA sumB : Expr) : MetaM Expr := do
  let one       := mkNatLit 1
  let oneMinusX := mkApp2 (mkConst ``Nat.sub) one x
  let term1     := mkApp2 (mkConst ``Nat.mul) x sumA
  let term2     := mkApp2 (mkConst ``Nat.mul) oneMinusX sumB
  let res       := mkApp2 (mkConst ``Nat.add) term2 term1
  return res

-- Inspects the expression to possibly extract mux elements.
-- Ex: xA + (1-x)B + xC --> some (x, [A,C], [B])
partial def viewAsMux (e : Expr) : Option (Expr × List Expr × List Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs])  => do
    let (lv, las, lbs) ← viewAsMux lhs
    let (rv, ras, rbs) ← viewAsMux rhs
    if (lv != rv) then none
    (lv, las ++ ras, lbs ++ rbs)
  | (``HMul.hMul, #[_, _, _, _, lhs, rhs]) =>
    match lhs.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, _, subRHS]) => some (subRHS, [], [rhs])
    | _ => some (lhs, [rhs], [])
  | _ => none

-- does split by cases reasoning
elab "elim2_norm_num" h1:ident h2:ident : tactic => do
  let id1 : TSyntax `ident := mkIdent h1.getId
  let id2 : TSyntax `ident := mkIdent h2.getId
  evalTactic (← `(tactic| apply split_one at $(id1):ident))
  evalTactic (← `(tactic| apply split_one at $(id2):ident))
  evalTactic (← `(tactic| apply Or.elim $id1))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  evalTactic (←  `(tactic| try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic|try rfl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))

/-- Determines if any expression contains a subtraction in its arguments, recursively.  Does not go
under the indexing part of a vector indexing expression. -/
partial def containsSub (e : Expr) :  MetaM Bool := do
  if not e.isApp then return false
  match e.getAppFnArgs with
  | (``HSub.hSub, _) => return true
  | (``getElem, #[_,_,_,_,_, vectorExpr, _, _]) => containsSub vectorExpr
  | (_, args) => args.anyM containsSub

/-- Recurses through the expression to find all free variables that appear in it, either as is, or
as part of some vector indexing operation. -/
partial def collectTerms (e : Expr) : MetaM NameSet := do
  let lctx ← getLCtx
  if e.isFVar then
    if let some decl := lctx.find? e.fvarId! then
      return {decl.userName}
  if e.isApp then
    let (fn, args) := e.getAppFnArgs

    match (fn, args) with
    | (``getElem, #[_,_,_,_,_, vectorExpr, indexExpr, _]) =>
      if vectorExpr.isFVar then
        if let some decl := lctx.find? vectorExpr.fvarId! then
          let idxPretty ← PrettyPrinter.ppExpr indexExpr
          return {Name.mkSimple s!"{decl.userName}[{idxPretty}]"}
      if vectorExpr.isApp then
        let idxPretty ← PrettyPrinter.ppExpr indexExpr
        return {Name.mkSimple s!"{vectorExpr}[{idxPretty}]"}
    | _ =>
      return (← args.mapM collectTerms).foldl (· ++ ·) {}
  if e.isMData then
      return (← collectTerms e.mdataExpr!)
  return {}

-- | Introduces a name in the local context, passing a term for it to the continuation, so that it
-- can be used in a syntax quotation.  Useful for testing functions working over open expressions
def withVector (n : Name) (cont : Term → TacticM a) : TacticM a := do
  withLocalDecl n .default (← elabTerm (← `(Vector (ZMod 8) 32)) none) $ fun e => do
    let t ← PrettyPrinter.delab e
    cont t

def testCollectVarsAppAndConst (test : TacticM NameSet) : MetaM Unit :=
  Term.TermElabM.run' do
    let ns ← test { elaborator := .anonymous } |>.run' { goals := [] }
    logInfo m!"{ns.toList}"

def test1 : TacticM NameSet := do
  withVector `x $ fun x => withVector `y $ fun y => withVector `z $ fun z => do
    let e ← elabTerm (← `($x[8].val + ($y[2] * $z[5]).val = 0)) none
    collectTerms e

--#eval testCollectVarsAppAndConst test1

-- Main Range Analysis Tactic
-- Args: list of hypothesis
syntax (name := tryApplyLemHyps) "try_apply_lemma_hyps" ppSpace "[" ident,* "]" : tactic

-- for muxes we need to prove the factored lemma and split by cases
def didMux : TacticM Unit := do
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try ring))
  evalTactic (← `(tactic| intro hMux))
  evalTactic (← `(tactic| try simp [hMux]))
  evalTactic (← `(tactic| try rw [Nat.mux_if_then] at ⊢))

structure LoopBodyResult where
  didMux : Bool
  madeProgress : Bool
  goals : List MVarId

def LoopBodyLabel := MonadCont.Label LoopBodyResult (ContT LoopBodyResult TacticM) Unit

def handleIfMux (loopBodyReturn : LoopBodyLabel) (g : MVarId) (args : Array Expr)
  : ContT LoopBodyResult TacticM Unit := do
  match viewAsMux args[2]! with
  | some (x, lhs@(_ :: _), rhs@(_ :: _)) =>
    let a := mkAddNat lhs
    let b := mkAddNat rhs
    let finalExpr ← monadLift $ g.withContext (rebuild x a b)
    let prop ← mkEq args[2]! finalExpr
    let pr ← mkFreshExprMVar prop
    -- create a new factored hyphesis
    let gWithHyp ← g.assert `hMux prop pr
    loopBodyReturn.apply { didMux := true, madeProgress := true, goals := [pr.mvarId!, gWithHyp] }
  | _ => return ()

def caseByCaseOnTwoVariables (loopBodyReturn : LoopBodyLabel)
  (g : MVarId) (hyps : List Name) (terms : NameSet)
  : ContT LoopBodyResult TacticM Unit := do
  logInfo m!"We are here {g}"
  let bounds ← monadLift $ g.withContext do
    let lctx ← getLCtx
    hyps.foldlM (init := []) fun acc hName => do
      let some decl := lctx.findFromUserName? hName
        | throwError m!"❌ Could not find a hypothesis named `{hName}`"
      match decl.type.getAppFnArgs with
      | (``LE.le, #[_, _, lhs, rhs]) =>
        match (← whnf rhs) with
        | (Expr.lit (Literal.natVal 1)) => do
          let LHSvars ← collectTerms lhs
          let varsList := LHSvars.toList
          if LHSvars.size == 1 && terms.contains varsList[0]! then
            return decl :: acc
          else
            return acc
        | _ => return acc
      | _ => return acc
  -- if bound exists apply a case split tactic
  if bounds.length = 2 then
    setGoals [g]
    monadLift $ g.withContext do
      let h1 := mkIdent  bounds[0]!.userName
      let h2 := mkIdent  bounds[1]!.userName
      evalTactic (← `(tactic| try elim2_norm_num $h1 $h2))
    if ← g.isAssigned then
      if (← getUnsolvedGoals).contains g then
        logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
      else
        loopBodyReturn.apply { didMux := false, madeProgress := true, goals := [g] }

def applyIfLemma (loopBodyReturn : LoopBodyLabel) : ContT LoopBodyResult TacticM Unit := do
  monadLift $ do evalTactic (← `(tactic| split_ifs))
  loopBodyReturn.apply { didMux := false, madeProgress := true, goals := (← getGoals) }

def applyZModLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  for hName in hyps do
    try
      -- need to do it with context so names are initialized
      let subgoals ← monadLift $ g.withContext do
        let lctx ← getLCtx
        let some decl := lctx.findFromUserName? hName
          | throwError m!"❌ Could not find a hypothesis named `{hName}`"
        g.apply (mkFVar decl.fvarId)
      -- Note: `return` below makes sure we end the loop after jumping to the
      -- continuation
      return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals })
    catch _err => pure ()

def applyThisLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (goalType : Expr) (stx : Syntax)
  : ContT LoopBodyResult TacticM Unit := do
  logInfo m!"{stx}"
  try
    let subgoals ← g.apply (← elabTerm stx goalType)
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals }
  catch _ => pure ()

def findAndApplyRangeAnalysisLemma (loopBodyReturn : LoopBodyLabel)
  (terms : NameSet) (g : MVarId) (mainGoalType : Expr) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType
  let lt ← monadLift (m := TacticM) ``(Nat.lt_of_le_of_lt)
  let sub ← monadLift (m := TacticM) ``(Nat.lt_sub)
  let add ← monadLift (m := TacticM) ``(Nat.add_le_add)
  let mul ← monadLift (m := TacticM) ``(Nat.mul_le_mul)
  let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
  let bitvec ← monadLift (m := TacticM) ``(BitVec.toNatLT)
  let (fn, args) := mainGoalType.getAppFnArgs
  let unfolded := ← monadLift $ withTransparency .reducible (whnf args[2]!)
  let fn3 := unfolded.getAppFn
  if (terms.size > 0) then
    -- if we have variables then we can apply < C --> <= m?
    match fn with
    | ``LT.lt =>
      match fn3 with
      | Expr.const name _ =>
        match name with
        | ``ite => applyIfLemma loopBodyReturn
        | ``OfNat.ofNat => pure ()
        | _ => applyThisLemma lt
      | _ => pure ()
    | _ => pure ()
  match fn with
  | ``LE.le =>
    match fn3 with
    | Expr.const name _ =>
      match name with
      | ``HSub.hSub => applyThisLemma sub
      | ``HAdd.hAdd => applyThisLemma add
      | ``HMul.hMul => applyThisLemma mul
      | ``OfNat.ofNat => applyThisLemma rfl
      -- rfl is a place holder should be something else
      | ``ite => applyIfLemma loopBodyReturn
      | ``ZMod.val => applyZModLemma loopBodyReturn g hyps
      | ``BitVec.toNat => applyThisLemma bitvec
      | _ =>
         pure ()
    | _ =>
      if fn3.isFVar then applyZModLemma loopBodyReturn g hyps
  | _ => pure ()

@[tactic tryApplyLemHyps]
elab_rules : tactic
| `(tactic| try_apply_lemma_hyps [$hs,*]) => do
  let hyps := (hs.getElems.map (·.getId)).toList
  let mut progress := true
  -- begin by factoring out multiplication for all goals
  -- important for mux discovery
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut cont := true
  while cont  do
    try
      evalTactic (← `(tactic| all_goals rw [Nat.mul_comm_ofNat]))
    catch _ =>
      cont := false
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut did_mux := false
  -- as long as we are making progress then continue
  while progress do
    if did_mux then do
      didMux
      did_mux := false
    let goals ← getGoals
    let mut updatedGoalsReversed : List MVarId := [] -- to keep track of goals we changed
    let mut handled := false
    progress := false
    -- Note: do not use `enqueueAll` as it would need reversing the list
    let mut goalQueue := Std.Queue.mk [] goals
    while (not handled && not goalQueue.isEmpty) do
      let some (g, rest) := goalQueue.dequeue? | unreachable!
      goalQueue := rest
      if (← g.isAssigned) then
        updatedGoalsReversed := g :: updatedGoalsReversed
        continue
      setGoals [g] -- focus on one goal at a time
      let goalType ← g.getType
      -- first we try to apply hypothesis
      let instantiatedGoalType ← instantiateMVars goalType
      let (_fn, args) := instantiatedGoalType.getAppFnArgs
      let terms ← collectTerms instantiatedGoalType
      -- Note: Here we use a continuation to let our callees return by
      -- short-circuiting the rest of the computation.
      let loopBodyResult ← (ContT.run · pure) $ MonadCont.callCC $ fun loopBodyReturn => do
        if args.size > 3 then
          let g ← getMainGoal
          let goalType ← g.getType
          let e ← instantiateMVars goalType
          let args := e.getAppArgs
          -- First check if we are dealing with a mux
          handleIfMux loopBodyReturn g args

          -- if not a mux but we have only two variables do a case by case reasoning
          -- this is necessary in case of variable dependencies
          -- Ex: x1 + x2 - x1*x2 --> Can't be negative but needs to be proven
          -- - First check that only 2 variables exist & a subtraction is involved
          -- then make sure all variables are bounded <= 1
          if terms.size == 2 && (← containsSub instantiatedGoalType) then
             caseByCaseOnTwoVariables loopBodyReturn g hyps terms
          --try to apply Lean's range analysis lemmas
          findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps
        -- if other techniques did not work try decide
        try
          monadLift $ do evalTactic (← `(tactic| decide))
          if ← g.isAssigned then
            logInfo m!"✅ Fully solved goal using decide {goalType}"
            return { didMux := false, madeProgress := true, goals := [g] }
        catch _err => pure ()
        -- if we made it here, nothing worked
        return { didMux := false, madeProgress := false, goals := [g] }
      if loopBodyResult.didMux then did_mux := true
      if loopBodyResult.madeProgress then do
        handled := true; progress := true
      updatedGoalsReversed := loopBodyResult.goals.reverse ++ updatedGoalsReversed
    -- Note: we built the updated goals list in reverse to avoid repeatedly
    -- traversing an ever-growingly long prefix.
    setGoals (updatedGoalsReversed.reverse ++ goalQueue.dList ++ goalQueue.eList.reverse)


abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513

instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry




-- example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> 1 - fv[0].val * fv[1].val < ff := by
--   intros h1 h2
--   try_apply_lemma_hyps [h1, h2]


lemma aaa {a b : BitVec 2} : a.toNat <= (b.toNat + 4 ) := by
  try_apply_lemma_hyps []
  apply Nat.le_trans
  apply BitVec.toNatLT


  simp


-- EXAMPLE 1 that needs to work
example { fv : Vector (ZMod ff) 8} :
( h1 : fv[0].val ≤ 1) -> (h2 : fv[1].val ≤ 1) -> ( h3 : fv[2].val ≤ 1) ->
( fv[0].val * fv[1].val ≤ 1) := by
try_apply_lemma_hyps []



-- Example 2 that needs to work
-- example { b a : BitVec 2} : a.toNat ≤ b.toNat + 3
