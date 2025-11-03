import Lean
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval
import BVModEq.Lemmas

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

partial def containsMVar (e : Expr) : Bool :=
  --ogInfo m! "CHECKING {e}"
  match e with
  | .mvar _ => true
  | .app f x => containsMVar f || containsMVar x
  | _ => false

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

partial def exprHasMod (e : Expr) : Bool :=
  match e with
  | .app f a =>
      exprHasMod f || exprHasMod a
  | .lam _ _ body _ =>
      exprHasMod body
  | .forallE _ _ body _ =>
      exprHasMod body
  | .letE _ _ val body _ =>
      exprHasMod val || exprHasMod body
  | .mdata _ b =>
      exprHasMod b
  | .proj _ _ b =>
      exprHasMod b
  | .const n _ =>
      -- check whether the head constant name is the modulus operator
      n == ``HMod.hMod || n == ``Mod.mod
  | _ => false

-- Main Range Analysis Tactic
-- Args: list of hypothesis
syntax (name := tryApplyLemHyps) "try_apply_lemma_hyps" ppSpace "[" ident,* "]" : tactic

-- for muxes we need to prove the factored lemma and split by cases
def didMux : TacticM Unit := do
  logInfo m!"Actually its here.. "
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try ring))
  evalTactic (← `(tactic| try intro hMux))
  evalTactic (← `(tactic| try simp [hMux]))
  evalTactic (← `(tactic| try rw [Nat.mux_if_then] at ⊢))

def bothArgsAreApps (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (_, #[_,_, lhs, rhs]) =>

    --if lhs.isApp && rhs.isApp then
      match lhs  with
        | .const ``OfNat.ofNat _ => false
        | .const ``BitVec.toNat _ => false
        | .const ``ZMod.val _ => false
        | .app f x =>
          match rhs with
          | .const ``OfNat.ofNat _ => false
          | .const ``BitVec.toNat _ => false
          | .const ``ZMod.val _ => false
          | .app f x => true
          | _ => false
        | _ => false
   -- else false
  | _ => false

structure LoopBodyResult where
  didMux : Bool
  madeProgress : Bool
  goals : List MVarId
  leftSide: Bool

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
    setGoals [pr.mvarId!, gWithHyp]
    didMux
    let MyGoals <- getGoals
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := MyGoals, leftSide := false }
  | _ => return ()


def baseName (n : Name) : Name :=
  let s := n.toString
  let base := s.takeWhile (· != '[')
  Name.mkSimple base



open Lean Meta


open Lean Meta

open Lean Meta

def checkTermsAreBitVecs (g : MVarId) (terms : NameSet) : MetaM Nat:=
  g.withContext do
    let lctx ← getLCtx
    let locals := lctx.getFVarIds.map (fun id => lctx.get! id)
    let mut bitVecCount := 0

    for n in terms.toList do
      -- clean up weird names like «a» or a[0]
      let rawStr := n.toString
      let baseStr := rawStr.takeWhile (· != '[')
      let cleanStr := (baseStr.trim.replace "«" "" |>.replace "»" "")

      -- find by string-based user name match
      match locals.findSome? (fun d =>
        let uname := d.userName.toString
        if uname == cleanStr || uname.endsWith cleanStr then some d else none) with
      | none =>

        logInfo m!"⚠️ variable {cleanStr} not found in goal (locals: {locals.map (·.userName)})"
      | some decl =>
        let t ← whnf decl.type
        match t.getAppFnArgs with
        | (``BitVec, #[_]) =>  bitVecCount :=  bitVecCount + 1  -- ✅ ok
        | _ =>
          logInfo m!"⚠️ variable {cleanStr} has non-BitVec type {t}"

    return  bitVecCount


open Lean Meta Elab Tactic

open Lean Meta Elab Tactic

def caseSplitOnBitVecNames (g : MVarId) (terms : NameSet) : TacticM (List MVarId) :=
  g.withContext do
    let lctx ← getLCtx
    let names := terms.toList

    for idx in [0:names.length] do
      let n := names[idx]!
      let s := n.toString.trim.replace "«" "" |>.replace "»" ""
      let (base, idxStr) :=
        match s.splitOn "[" with
        | [v, rest] => (v.trim, rest.takeWhile (·.isDigit))
        | _ => (s, "0")

      let some idxNat := idxStr.toNat?
        | logInfo m!"⚠️ cannot parse index in {s}"; continue

      match lctx.findFromUserName? (Name.mkSimple base) with
      | none => logInfo m!"⚠️ variable {base} not found in goal"
      | some decl =>
        let t ← whnf decl.type
        match t.getAppFnArgs with
        | (``BitVec, #[_]) => do
          let tacticStx ←
            `(tactic| cases h : $(mkIdent (Name.mkSimple base))[$(Quote.quote idxNat)])
          evalTactic tacticStx
          logInfo m!"🟢 Split on {base}[{idxNat}]"

          -- 🟣 If this is the *last* variable, simp first, then split again
          if idx == names.length - 1 then
            logInfo m!"🧹 Running simp before final split"
            let mut progress := true
            while progress do
              try evalTactic (← `(tactic| simp))
              catch _ => progress := false

            logInfo m!"🟣 Second split on last variable {base}[{idxNat}]"
            evalTactic tacticStx

        | _ =>
          logInfo m!"⚠️ {base} is not a BitVec variable, skipping"

    getGoals




def caseByCaseOnTwoVariables (loopBodyReturn : LoopBodyLabel)
  (g : MVarId) (hyps : List Name) (terms : NameSet)
  : ContT LoopBodyResult TacticM Unit := do
  let m <- checkTermsAreBitVecs g terms

  --Step 1 we should check if terms are bit vectors
  if (m==0)  then
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
          loopBodyReturn.apply { didMux := false, madeProgress := true, goals := [g], leftSide:= false }
    else if (m == 2 ) then
      logInfo m! "we are here"
      let newGoals ← caseSplitOnBitVecNames g terms
      loopBodyReturn.apply { didMux := false, madeProgress := true, goals := newGoals, leftSide:= false }
    else
      loopBodyReturn.apply { didMux := false, madeProgress := false, goals := [g], leftSide:= false }




def applyIfLemma (loopBodyReturn : LoopBodyLabel) : ContT LoopBodyResult TacticM Unit := do
  logInfo m! "split_ifs"
  monadLift $ do evalTactic (← `(tactic| split_ifs))
  loopBodyReturn.apply { didMux := false, madeProgress := true, goals := (← getGoals), leftSide := false }

def applyZModLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  logInfo m!"ZMODLEMMA"
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
      return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals , leftSide := false})
    catch _err => pure ()

def applyThisLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (goalType : Expr) (leftSide : Bool) (stx : Syntax)
  : ContT LoopBodyResult TacticM Unit := do
  logInfo m!"{stx}"
  try
    let subgoals ← g.apply (← elabTerm stx goalType)
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals,  leftSide := leftSide }
  catch _ => pure ()

def findAndApplyRangeAnalysisLemma (loopBodyReturn : LoopBodyLabel)
  (terms : NameSet) (g : MVarId) (mainGoalType : Expr) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  --let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType
  let lt ← monadLift (m := TacticM) ``(Nat.lt_of_le_of_lt)
  let sub ← monadLift (m := TacticM) ``(Nat.lt_sub)
  let add ← monadLift (m := TacticM) ``(Nat.add_le_add)
  let mul ← monadLift (m := TacticM) ``(Nat.mul_le_mul)
  let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
  let bitvec ← monadLift (m := TacticM) ``(BitVec.toNatLT)
  let expLeq ← monadLift (m := TacticM) ``(Nat.le_trans)
  let constLeq ← monadLift (m := TacticM) ``(Nat.le_of_lt_add_one)
  let (fn, args) := mainGoalType.getAppFnArgs
  --logInfo m! "{args[args.size-1]!} => {containsMVar args[args.size-1]!}"

  --logInfo m! "Args 1: {args[1]!}"
  let mut leftSide := false
  let unfolded ←  if args[2]!.isApp then
     monadLift $ withTransparency .reducible (whnf args[2]!)
  else
     monadLift $ withTransparency .reducible (whnf args[3]!)
  logInfo m! "UNFOLDED: {unfolded}"
  if !args[2]!.isApp  && args[3]!.isApp then
    leftSide := true
  else
    leftSide := false
  let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType leftSide
  let fn3 := unfolded.getAppFn
  logInfo m! "fn3: {fn3}"
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
    if containsMVar mainGoalType then
      match fn3 with
        | Expr.const name _ =>
          match name with
          | ``HSub.hSub => applyThisLemma sub
          | ``HAdd.hAdd => applyThisLemma add
          | ``HMul.hMul => applyThisLemma mul
          --| ``OfNat.ofNat => applyThisLemma rfl
          -- rfl is a place holder should be something else
          | ``ite => applyIfLemma loopBodyReturn
          | ``ZMod.val => applyZModLemma loopBodyReturn g hyps
          | ``BitVec.toNat => applyThisLemma bitvec
          | _ => pure ()
        | _ =>
          if fn3.isFVar then applyZModLemma loopBodyReturn g hyps
      else
        --logInfo m! "{args[args.size-1]!.getAppFn}"
         match  fn3 with
        | .const ``OfNat.ofNat _ => applyThisLemma constLeq
        | .const ``ite _  => applyIfLemma loopBodyReturn
        | _ =>
          if terms.size >= 2 then
            applyThisLemma expLeq
          else
            pure ()
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
  let mut count  := 0
  while (progress ) do
    count := count + 1
    if did_mux then do
      logInfo m! "We are post did mux"
      didMux
      did_mux := false
    let goals ← getGoals
    let mut updatedGoalsReversed : List MVarId := [] -- to keep track of goals we changed
    let mut handled := false
    progress := false
    -- Note: do not use `enqueueAll` as it would need reversing the list
    let mut goalQueue := Std.Queue.mk [] goals
    while (not handled && not goalQueue.isEmpty ) do
      count := count + 1
      let mut some (g, rest) := goalQueue.dequeue? | unreachable!
      goalQueue := rest
      if (← g.isAssigned) then
        updatedGoalsReversed := g :: updatedGoalsReversed
        continue
      setGoals [g] -- focus on one goal at a time
      --let k <- instantiateMVars ty
      -- if bothArgsAreApps k then
      --   logInfo m! "WE MADE IT {k}"
      --   try
      --     evalTactic (← `(tactic| simp))
      --     g <- getMainGoal
      --     if (← g.isAssigned) then
      --       updatedGoalsReversed := g :: updatedGoalsReversed
      --       continue
      --     setGoals [g]
      --   catch _ => pure ()

      let goalType ← g.getType
      -- first we try to apply hypothesis
      let instantiatedGoalType ← instantiateMVars goalType
      let (fn, args) := instantiatedGoalType.getAppFnArgs
      let terms ← collectTerms instantiatedGoalType
      if exprHasMod instantiatedGoalType then do
        let mut modLoop:= true
        logInfo m! "The issue is here?\n {goalType}"
        evalTactic (← `(tactic| try simp))
        while (modLoop) do
          try
              evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
              evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
          catch  _ =>
              evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
              modLoop := false

        let gs <- getGoals
        updatedGoalsReversed := gs ++ updatedGoalsReversed
        progress := true
        handled := true
        continue
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
          --logInfo m! "{<- getGoals}"

          -- if not a mux but we have only two variables do a case by case reasoning
          -- this is necessary in case of variable dependencies
          -- Ex: x1 + x2 - x1*x2 --> Can't be negative but needs to be proven
          -- - First check that only 2 variables exist & a subtraction is involved
          -- then make sure all variables are bounded <= 1
          -- TODO: this should be check to containsSUb OR both sides are applications
          logInfo m! "{terms.size}"
          if ((terms.size = 2))  && ( (← containsSub instantiatedGoalType) ||  bothArgsAreApps instantiatedGoalType ) then
             logInfo m!"We are here"
             caseByCaseOnTwoVariables loopBodyReturn g hyps terms
          --try to apply Lean's range analysis lemmas
          -- for n in terms.toArray do
          --   logInfo m!"{n}"
          logInfo m!"✅ Stuck on {goalType} with {terms.size}"
          if terms.size >= 1 then
            findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps
          else
            let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
            let bitvec ← monadLift (m := TacticM) ``(BitVec.toNatLT)
            let (fn, args) := instantiatedGoalType.getAppFnArgs
 -- logInfo m! "{args[args.size-1]!} => {containsMVar args[args.size-1]!}"
            let unfolded := ← monadLift $ withTransparency .reducible (whnf args[2]!)
            let fn3 := unfolded.getAppFn
               match fn with
                  | ``LE.le =>
                    --if containsMVar instantiatedGoalType then
                      match fn3 with
                        | Expr.const name _ =>
                          match name with
                          | ``OfNat.ofNat => applyThisLemma loopBodyReturn g instantiatedGoalType false rfl
                          | ``ZMod.val =>
                              applyZModLemma loopBodyReturn g hyps
                          | ``BitVec.toNat => applyThisLemma loopBodyReturn g instantiatedGoalType false bitvec
                          -- rfl is a place holder should be something else
                          | _ =>
                              -- this is good we have zero variables we should do this
                              if containsMVar instantiatedGoalType then
                                applyThisLemma loopBodyReturn g instantiatedGoalType false rfl
                              else
                                pure ()

                        | _ => pure ()
                  | _ => pure ()
            --applyThisLemma loopBodyReturn g instantiatedGoalType rfl
            --findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps

        -- if other techniques did not work try decide
        try
          monadLift $ do evalTactic (← `(tactic| decide))
          if ← g.isAssigned then
            logInfo m!"✅ Fully solved goal using decide {goalType}"
            return { didMux := false, madeProgress := true, goals := [g] , leftSide := false}
        catch _err => pure ()
        -- last shot try simp
        --  try
        --   monadLift $ do evalTactic (← `(tactic| simp))
        --   if ← g.isAssigned then
        --     logInfo m!"✅ Fully solved goal using simp {goalType}"
        --     let mut gs <- getGoals
        --     return { didMux := false, madeProgress := true, goals := gs }
        -- catch _err => pure ()
        -- if we made it here, nothing worked
        return { didMux := false, madeProgress := false, goals := [g], leftSide:=false }
      if loopBodyResult.didMux then did_mux := true
      if loopBodyResult.madeProgress then do
        handled := true; progress := true
      if loopBodyResult.leftSide && !did_mux then
         logInfo m! "LEFTSIDE: {loopBodyResult.leftSide}"
         let rev := loopBodyResult.goals
         logInfo m! "{rev}"
         let rev :=
            match rev with
            | a :: b :: rest => b :: a :: rest
            | _ =>
              rev
          updatedGoalsReversed :=  updatedGoalsReversed ++ rev.reverse
      else
        logInfo m! "we are here?"
        updatedGoalsReversed := loopBodyResult.goals.reverse ++ updatedGoalsReversed
    -- Note: we built the updated goals list in reverse to avoid repeatedly
    -- traversing an ever-growingly long prefix.
    logInfo m! "NEW GOALS {updatedGoalsReversed}"
    setGoals (updatedGoalsReversed.reverse ++ goalQueue.dList ++ goalQueue.eList.reverse)
    if (!progress) then
      try
        evalTactic (← `(tactic| omega))
        --handled := true; progress := true
        progress:= true
      catch _ => pure ()
    if (!progress) then
      try
        let g <- getMainGoal
        logInfo m! "NO the issue is here?\n {g}"
        evalTactic (← `(tactic| simp))
        --handled := true; progress := true
        progress:= true
      catch _ => pure ()


  --evalTactic (← `(tactic| try apply Nat.le_refl; try simp))


abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513

instance : Fact (Nat.Prime ff) := by sorry

instance : Fact (NeZero ff) := by sorry




example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> 1 - fv[0].val * fv[1].val < ff := by
  intros h1 h2
  try_apply_lemma_hyps [h1, h2]


lemma aaa {a b : BitVec 2} : a.toNat <= (b.toNat + 3 ) := by
  --try_apply_lemma_hyps []
  --apply BitVec.toNatLT
  try_apply_lemma_hyps []


-- -- -- -- -- Idea: when doing Nat.le_refl check if we have at least two variables

lemma aaa1 {a b : BitVec 2} : a.toNat ≤ (b.toNat + 3) := by
  try_apply_lemma_hyps []
-- --   --apply Nat.lt_of_le_of_lt


-- --   --  apply Nat.le_trans
-- --   --  apply BitVec.toNatLT
-- --   --  apply Nat.le_trans
-- --    --apply BitVec.toNatLT



-- --   --  apply Nat.le_trans

-- --   --  apply BitVec.toNatLT

-- --   --  apply Nat.le_trans

-- --   --  apply Nat.lt_sub
-- --   --  apply Nat.le_trans
-- --   --  apply Nat.le_refl
-- --   --  simp


example { fv : Vector (ZMod ff) 8} :
( h1 : fv[0].val ≤ 1) -> (h2 : fv[1].val ≤ 1) -> ( h3 : fv[2].val ≤ 1) ->
( fv[0].val * fv[1].val ≤ 1) := by
  intros h1 h2 h3

  try_apply_lemma_hyps [h1, h2 ,h3]



example { fv : Vector (ZMod ff) 8} :
( h1 : fv[0].val ≤ 1) -> (h2 : fv[1].val ≤ 1) -> ( h3 : fv[2].val ≤ 1) ->
( fv[0].val * fv[1].val < 2) := by
intros h1 h2 h3

try_apply_lemma_hyps [h1, h2 ,h3]


-- -- -- -- -- -- -- -- -- --Example 2 that needs to work

example {fv : Vector (ZMod ff) 8}:
(h1 : fv[0].val ≤ 1) ->
(h2 : fv[1].val ≤ 1) ->
(h3 : fv[2].val ≤ 1) ->  (1 - fv[0].val * fv[1].val < ff) := by
intros h1 h2 h3
try_apply_lemma_hyps [h1, h2, h3]

example {fv : Vector (ZMod ff) 8}:
(h1 : fv[0].val ≤ 1) ->
(h2 : fv[1].val ≤ 1) ->
(h3 : fv[2].val ≤ 1) ->
(fv[0].val * fv[1].val + (1 - fv[0].val) * (1 - fv[1].val) <= 1) := by

intros h1 h2 h3
try_apply_lemma_hyps [h1, h2, h3]



-- example { b a : BitVec 2} : a.toNat ≤
 example {fv : Vector (ZMod ff) 8}:
(h1 : fv[0].val ≤ 1) ->
(h2 : fv[1].val ≤ 1) ->
(h3 : fv[2].val ≤ 1) ->
(if fv[0] = 0 then 1 - fv[1].val else fv[1].val )< 2 := by
intro h1 h2 h3
try_apply_lemma_hyps [h1, h2, h3]



-- -- -- -- BAD B/C NAT.le_trans should be 2 variables or more only


example {b a : BitVec 2} :
  (a.toNat * (b.toNat + 3 - a.toNat) ≤ 200) := by
  try_apply_lemma_hyps []


-- -- PROBLEM
example {fv : Vector (ZMod ff) 8} :
(h1 : fv[0].val ≤ 1) ->
(h2 : fv[1].val ≤ 1) ->
(h3 : fv[2].val ≤ 1) -> fv[0].val + fv[1].val < ff
 /\ (fv[0].val * fv[1].val % ff ≤ (fv[0].val + fv[1].val) % ff) := by
intros h1 h2 h3
split_ands
try_apply_lemma_hyps [h1, h2, h3]


example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) -> ( (1 - (fv[0].val * fv[1].val % ff + (1 - fv[0].val) * (1 - fv[1].val) % ff) % ff) % ff < 7
/\ (fv[0].val * fv[1].val % ff + (1 - fv[0].val) * (1 - fv[1].val) % ff) % ff ≤ 1) := by
  intro h1 h2 h3
  split_ands
  try_apply_lemma_hyps [h1, h2, h3]


example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) ->  1 - (fv[0].val * fv[1].val + (1 - fv[0].val) * (1 - fv[1].val)) < 7 := by
try_apply_lemma_hyps [h1, h2, h3]

lemma hello {b a : BitVec 2} : a.toNat * ((((b.toNat) + 3 % ff) % ff - (a.toNat)) % ff) % ff ≤ 200 /\ (a.toNat) ≤ ((b.toNat) + 3 % ff) % ff := by
  split_ands
  try_apply_lemma_hyps []




example {a b :BitVec 2} : ((if b[0] = true then 1 else 0) + if a[0] = true then 1 else 0) ≥
 if a[0] = true then if b[0] = true then 2 else 0 else 0 := by
 try_apply_lemma_hyps []









  -- simp
  -- have h1: a[0] <= 1 := by BitVec.ofNatLT a
  -- rw [BitVec.ofNatLT a]
   -- try_apply_lemma_hyps []

-- --  example {a b :BitVec 2} :  1 ≤ (if b[0] = true then 1 else 0) := by
-- --  --simp [<- ge_iff_le]
-- --  try_apply_lemma_hyps []
-- --  split_ifs



--  apply Nat.le_trans

--  decide
--  simp
-- apply Nat.add_le_add
--  apply Nat.le_refl
-- rw [← ge_iff_le]
 --apply Nat.le_trans

--  apply Nat.add_le_add
--  apply Nat.le_refl  -- rfl
--  apply Nat.le_trans --expLeq
