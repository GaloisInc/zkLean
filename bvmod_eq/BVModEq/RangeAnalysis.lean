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
import BVModEq.Valify
import BVModEq.BVify

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

lemma Nat.mul_comm_ofNat (a n : Nat) :
   (OfNat.ofNat n) * a = a* (OfNat.ofNat n : Nat) := by
  rw [Nat.mul_comm ]

lemma mul_comm_num_left (n t : ℕ) :
  (n : ℕ) * t = t * (n : ℕ) := by
  simpa using Nat.mul_comm (n : ℕ) t

lemma BitVec.toNatLT {bw} {a : BitVec bw}:
  a.toNat <= (2^bw -1) := by
  have h : a.toNat < 2 ^ bw := a.toFin.isLt
  exact Nat.le_pred_of_lt h

lemma BitVec.toNatGT {bw} {a : BitVec bw}:
 0  <= a.toNat  := by
  sorry
  -- have h : a.toNat < 2 ^ bw := a.toFin.isLt
  -- exact Nat.le_pred_of_lt h
lemma neg_add_to_sub {α : Type*} [AddCommGroup α] (a b : α) :
  -a + b = b - a := by
  rw [sub_eq_add_neg]
  rw [add_comm (-a) b]

lemma  neg_param (x y z : ZMod p) :
  x + (-y -z) = (x - y) -z := by
  ring_nf

lemma if_to_bounds {b: Prop} {x: ZMod f} [Decidable b]: (if b then 1 else 0) =  x <->
(if b then 1 else 0) =  x /\  ZMod.val x <= 1 := by
sorry

lemma duplicate {b a : ZMod ff} : b = a <->
  b = a /\ b = a := by
  simp

lemma sub_add_right_recursive {α : Type*} [AddCommGroup α]
    (a b c : α) : a - b + c = (a + c) - b := by
  rw [sub_eq_add_neg, add_assoc]
  rw [sub_eq_add_neg]
  rw [add_comm (-b) (c)]
  rw [add_assoc]

lemma ZMod.toNatLT {n} {a : ZMod n}
  (h: n> 0) : a.val <= n := by
  sorry

lemma ZMod.toNatGT {n} {a : ZMod n}
  (h: n> 0) : a.val >= 0 := by
  sorry

lemma mod_le_pred {m k : ℕ} (hm : m > 0) :
    k % m ≤ m - 1 := by
  have hlt : k % m < m := Nat.mod_lt k hm
  exact Nat.le_pred_of_lt hlt



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


def isArithmeticHead (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n =>
      n == ``HAdd.hAdd || n == ``Add.add ||
      n == ``HSub.hSub || n == ``Sub.sub ||
      n == ``HMul.hMul || n == ``Mul.mul ||
      n == ``Neg.neg   || n == ``HMod.hMod ||
      n == ``HPow.hPow || n == ``Pow.pow || n == ``ite
  | none => false

private def compositeInsideValHere? (e : Expr) : MetaM ( Bool) := do
  --let e ← whnf e
  if e.isAppOf ``ZMod.val then
    let args := e.getAppArgs
    if let some t := args.back? then
      if isArithmeticHead t then

        return true
  return false

/-- DFS for first subterm of the form `ZMod.val t` where `t` is composite
(arithmetic-headed). -/
partial def firstCompositeInsideVal? (e : Expr) : MetaM ( Bool) := do
  if  (← compositeInsideValHere? e) then
    return true
  match e with
  | .app f a =>
      if (← firstCompositeInsideVal? f ) then return true
      return ← firstCompositeInsideVal? a
  | _ =>
    return false

/-- Recurses through the expression to find all free variables that appear in it, either as is, or
as part of some vector indexing operation. -/
partial def collectTerms (e : Expr) : MetaM NameSet := do
  let lctx ← getLCtx
  let e <- instantiateMVars e
  --logInfo m!"{e.getAppFnArgs}"
  -- if e.isBVar then
  --   logInfo m!"{e}"
  --   if let some decl := lctx.find? e.fvarId! then
  --     return {decl.userName}
  -- reconstruct name using local context

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
        let (fn1, args1) := vectorExpr.getAppFnArgs
          match (fn1, args1) with
          | (``ite, _) =>
              return {Name.mkSimple s!"{args1[4]!}"} ++ {Name.mkSimple s!"{args1[3]!}"} ++ {Name.mkSimple s!"{args1[2]!}" }
          | _ =>
            let idxPretty ← PrettyPrinter.ppExpr indexExpr
            --logInfo m! "{vectorExpr}"
            return {Name.mkSimple s!"{vectorExpr}[{idxPretty}]"}
    | _ =>
      return (← args.mapM collectTerms).foldl (· ++ ·) {}
  if e.isMData then
      return (← collectTerms e.mdataExpr!)
  return {}

-- | Introduces a name in the local context, passing a term for it to the continuation, so that it
-- can be used in a syntax quotation.  Useful for testing functions working over open expressions
def withVector (n : Name) (cont : Term → TacticM a) : TacticM a := do
  withLocalDecl n .default (← elabTerm (← `(BitVec 1)) none) $ fun e => do
    let t ← PrettyPrinter.delab e
    cont t

def withBool (n : Name) (cont : Term → TacticM a) : TacticM a := do
  withLocalDecl n .default (← elabTerm (← `(Bool)) none) $ fun e => do
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


def test2 : TacticM NameSet := do
  withVector `x $ fun a =>
  withVector `y $ fun b =>
  withVector `z $ fun c => do
    let e ← elabTerm (← `( (((if $c[0]! = true then 1 else 0) + if $b[0]! = true then 1 else 0) -  if $b[0]! = true then if $c[0]! = true then 2 else 0 else 0) *
    2)) none
    collectTerms e

#eval testCollectVarsAppAndConst test2

partial def countMinusOps (e : Expr) : Nat :=
  if e.isAppOfArity ``HSub.hSub 2 then
    let args := e.getAppArgs
    let a := args[0]!
    let b := args[1]!
    1 + countMinusOps a + countMinusOps b
  else
    match e with
    | .app f x => countMinusOps f + countMinusOps x
    | .lam _ _ body _ => countMinusOps body
    | .letE _ t v b _ => countMinusOps t + countMinusOps v + countMinusOps b
    | .proj _ _ e => countMinusOps e
    | _ => 0


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
  --logInfo m!"Actually its here.. "
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try ring))
  evalTactic (← `(tactic| try intro hMux))
  evalTactic (← `(tactic| try simp [hMux]))
  evalTactic (← `(tactic| try rw [Nat.mux_if_then] at ⊢))

def bothArgsAreApps (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (_, #[_,_, lhs, rhs]) =>
      isArithmeticHead lhs && isArithmeticHead rhs
    --if lhs.isApp && rhs.isApp then
      -- match lhs  with
      --   | .const ``OfNat.ofNat _ => false
      --   | .const ``BitVec.toNat _ => false
      --   | .const ``ZMod.val _ => false
      --   | .app f x =>
      --     match rhs with
      --     | .const ``OfNat.ofNat _ => false
      --     | .const ``BitVec.toNat _ => false
      --     | .const ``ZMod.val _ => false
      --     | .app f x => true
      --     | _ => false
      --   | _ => false
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
        return 200000
      | some decl =>
        let t ← whnf decl.type
        match t.getAppFnArgs with
        --| (``ZMod, #[_]) => return 0
        | (``BitVec.toNat, #[_]) => return 0
        | (``ZMod, #[_]) => return 0
        | (``BitVec, #[_]) =>
          --logInfo m!"{t.getAppFnArgs}"
          bitVecCount :=  bitVecCount + 1  -- ✅ ok
        | (``Vector, #[ty, len]) =>
            match ty.getAppFnArgs with
                | (``ZMod, #[_]) => return 0
                | (``BitVec, #[_]) =>  bitVecCount :=  bitVecCount + 1  -- ✅ ok
                | _ => return 0
        | _ =>
          logInfo m!"⚠️ variable { t.getAppFnArgs} has non-BitVec type {t}"
          return 0
    return  bitVecCount


def isValType (e : Expr) : Bool :=
  match e.getAppFn with
  | .const ``ZMod.val _ => true
  | _ => false

def isBitVecType (ty : Expr) : Bool :=
  match ty.getAppFn with
  | .const ``BitVec _ => true
  | _ => false

def caseSplitOnBitVecNames (g : MVarId) (terms : NameSet) : TacticM (List MVarId) :=
  g.withContext do
    let lctx ← getLCtx
    let names := terms.toList

    for idx in [0:names.length] do
      let n := names[idx]!
      let s := n.toString.trim.replace "«" "" |>.replace "»" ""
      if ! (s.contains '[') then
        return []
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
         -- logInfo m!"🟢 Split on {base}[{idxNat}]"

          -- 🟣 If this is the *last* variable, simp first, then split again
          if idx == names.length - 1 then
            let mut progress := true
            while progress do
              try
                let gs <- getGoals
                if gs.isEmpty then
                  return gs
                evalTactic (← `(tactic| simp))
              catch _ => progress := false

            --logInfo m!"🟣 Second split on last variable {base}[{idxNat}]"
            evalTactic tacticStx

        | _ =>
          logInfo m!"⚠️ {base} is not a BitVec variable, skipping"

    getGoals




def caseByCaseOnTwoVariables (loopBodyReturn : LoopBodyLabel)
  (g : MVarId) (hyps : List Name) (terms : NameSet)
  : ContT LoopBodyResult TacticM Unit := do
  let m <- checkTermsAreBitVecs g terms
  --logInfo m!"umm for {m}"
  --Step 1 we should check if terms are bit vectors
  if (m==0)  then
    --logInfo m!"HUH"
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
          --logInfo m!"HUH"
          loopBodyReturn.apply { didMux := false, madeProgress := true, goals := [g], leftSide:= false }
      else
         --logInfo m!"HUH11"
         return ()
         --loopBodyReturn.apply { didMux := false, madeProgress := false, goals := [g], leftSide:= false }
  else if (m == 2 ) then
      --logInfo m! "we are here"
       --if ← g.isAssigned then
        let newGoals ← caseSplitOnBitVecNames g terms
        if ← g.isAssigned then
          if (← getUnsolvedGoals).contains g then
            --logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
            loopBodyReturn.apply { didMux := false, madeProgress := true, goals := [g], leftSide:= false }
          else
           -- logInfo m!"HUH"
            loopBodyReturn.apply { didMux := false, madeProgress := true, goals := newGoals, leftSide:= false }
      else
         --logInfo m!"{m}"
         return ()

syntax (name := splitPropIf) "split_prop_if " term : tactic

macro_rules
  | `(tactic| split_prop_if $p) =>
      `(tactic| by_cases h : $p <;> simp [h] at *)

def applyIfLemma (loopBodyReturn : LoopBodyLabel) (cond0: Expr): ContT LoopBodyResult TacticM Unit := do
  let decTy ← Meta.inferType cond0
  if (decTy.getAppApps.size != 0) then
    let condSyn ← monadLift <| Lean.Elab.Term.exprToSyntax decTy.getAppArgs[0]!
    monadLift $ do evalTactic (← `(tactic| split_prop_if $condSyn))
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := (← getGoals), leftSide := false }
  else
    monadLift $ do evalTactic (← `(tactic| split_ifs))
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := (← getGoals), leftSide := false }

def applyThisLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (goalType : Expr) (leftSide : Bool) (stx : Syntax)
  : ContT LoopBodyResult TacticM Unit := do
  try
    --logInfo m!"WHY{stx} for {goalType}"
    let subgoals ← g.apply (← elabTerm stx goalType)
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals,  leftSide := leftSide }
  catch _ =>
    pure ()
     --pure ()
    --logInfo (Lean.Exception.toMessageData e)

def applyZModLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (goalType : Expr) (leftSide : Bool) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  --logInfo m!"ZMODLEMMA"
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
    try
    --   let ok ← monadLift <| g.withContext do
    --     let lctx ← getLCtx
    --     return (lctx.findFromUserName? hName).isSome

    --   if !ok then
    --     pure ()
    --   else
    --     -- This is the key: use the NAME, not exprToSyntax
    --     let hId : TSyntax `term := Lean.mkIdent hName

    --     -- Run simp [← hName]
    --      monadLift $ do evalTactic (← `(tactic| simp [← $hId] ))
    -- catch _ => pure ()

    -- let subgoals ← getGoals
      let hypSyn <- monadLift $ g.withContext do
        let lctx1 ← getLCtx
        let some decl := lctx1.findFromUserName? hName
          | throwError m!"❌ Could not find a hypothesis named `{hName}`"
        --return decl
        let hypExpr : Expr := mkFVar decl.fvarId
        let hypSyn ←  Lean.Elab.Term.exprToSyntax hypExpr
        return hypSyn
        --return (hypSyn)
      --monadLift $ do evalTactic (← `(tactic| try rw [BVModEq.bool_to_bv] at $hypSyn))
      monadLift $ do evalTactic  (← `(tactic| simp [← $hypSyn] ))
      let subgoals ← getGoals
      return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals , leftSide := false})

    catch _ => pure ()
  try
       --logInfo m!"and we did this?"
       monadLift $ do evalTactic  (← `(tactic| valify [] ))
       let subgoals ← getGoals
       return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals , leftSide := false})
  catch e =>
      try
         monadLift $ do evalTactic  (← `(tactic| simp))
         let subgoals ← getGoals
         return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals , leftSide := false})
      catch e =>
      --logInfo m!"valify failed?"
      logInfo m!"{e.toMessageData}"
      pure ()

        -- Convert to syntax (safe version)
        -- let hypSyn? ← monadLift <| Lean.Elab.Term.exprToSyntax? hypExpr
        -- match hypSyn? with
        -- | none =>
        --     logInfo "exprToSyntax failed"
        --     pure ()
        -- | some hypSyn => do
        --     -- Try simp
        --     monadLift $ evalTactic (← `(tactic| simp [← $hypSyn] ))

        -- Update goals and return to loop continuation

            --match lctx.findFromUserName? h with

  --       | none =>
  --           --logInfo m!"Variable {onlyName} not found in context"
  --           break
  --       | some decl =>
  --           let fvarId := decl.fvarId

  --           let varMap ← varToHypRef.get

  --           match lookup varMap fvarId with
  --           | some hypExpr =>
  --             --logInfo m! "{hypExpr}"
  --             evalTactic (← `(tactic| simp [← $hypExpr] at *))
  --             after ← getGoals
  --           | none =>
  --               break

      -- catch _err =>
      --  logInfo m! "Error: {(_err.toMessageData)}"
      --  pure ()
  --logInfo m! "How did we get here?"
  let lt ← monadLift (m := TacticM) ``(ZMod.toNatLT)
  let applyThisLemma := applyThisLemma loopBodyReturn g goalType leftSide
  applyThisLemma lt

-- lemma Nat.add_ge_add{a b c d : Nat} (h₁ : a >= b) (h₂ : c >= d) :
-- a + c >= b + d := by sorry

-- example (x y: Nat) (h1: x <= 1) (h2: y <= 1):  (y+x) <= 2 := by
--   apply Nat.le_trans
--   apply Nat.add_le_add
--   apply h2
--   apply h1
--   decide


-- example (x y: Nat) (h1: x <= 1) (h2: y <= 1):  (y*x) <= (y+x) := by
--   apply Nat.le_trans
--   apply Nat.mul_le_mul
--   apply h2
--   apply h1
--   apply Nat.le_trans
--   swap
--   apply Nat.add_le_add
--   apply Nat.zero_le
--   apply Nat.zero_le
--   sorry



-- example (x y: Nat) (h1: x <= 1) (h2: y <= 1):  1 <= (y+x) := by
--   apply Nat.le_trans
--   swap
--   apply Nat.add_le_add
--   apply Nat.mul_le_mul
--   apply h2
--   apply h1
--   apply Nat.le_trans
--   swap
--   apply Nat.add_le_add
--   apply Nat.zero_le
--   apply Nat.zero_le
--   sorry
  --sorry
  --apply Nat.add_le_add
  --apply Nat.zero_le
  --apply Nat.zero_le



  -- apply Nat.add_le_add
  -- apply h2
  -- apply h1
  -- decide

  -- --apply Nat.lt_of_le_of_lt

def findAndApplyRangeAnalysisLemma (loopBodyReturn : LoopBodyLabel)
  (terms : NameSet) (g : MVarId) (mainGoalType : Expr) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  --let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType
  let lt ← monadLift (m := TacticM) ``(Nat.lt_of_le_of_lt)
  --let sub ← monadLift (m := TacticM) ``(BitVec.setWidth)

  let sub ← monadLift (m := TacticM) ``(Nat.lt_sub)
  let add ← monadLift (m := TacticM) ``(Nat.add_le_add)
  let mul ← monadLift (m := TacticM) ``(Nat.mul_le_mul)
  let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
  let bitvecLT ← monadLift (m := TacticM) ``(BitVec.toNatLT)
  let bitvecGT ← monadLift (m := TacticM) ``(BitVec.toNatGT)
  let bitwidth ← monadLift (m := TacticM) ``(BitVec.setWidth)
  let zmodGT  ← monadLift (m := TacticM) ``(ZMod.toNatGT)
  let modLemma ← monadLift (m := TacticM) ``(mod_le_pred)
  let expLeq ← monadLift (m := TacticM) ``(Nat.le_trans)
  let constLeq ← monadLift (m := TacticM) ``(Nat.le_of_lt_add_one)
  let (fn, args) := mainGoalType.getAppFnArgs
  --logInfo m! "{args[args.size-1]!} => {containsMVar args[args.size-1]!}"

  --logInfo m! "Args 1: {args[1]!}"
  let mut leftSide := false

  --logInfo m! "UNFOLDED: {unfolded}"
  if (!args[2]!.isApp  && args[3]!.isApp) || ( (<- collectTerms args[2]!).size == 0  && (<- collectTerms args[3]!).size != 0  ) then
    leftSide := true
  else
    leftSide := false
  let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType leftSide
  let unfolded ←  if !leftSide then
     monadLift $ withTransparency .reducible (whnf args[2]!)
  else
     monadLift $ withTransparency .reducible (whnf args[3]!)
  let fn3 := unfolded.getAppFn
  --logInfo m! "LEFTHS: {leftSide} for {mainGoalType}"
  if (terms.size > 0) then
    -- if we have variables then we can apply < C --> <= m?
    match fn with
    | ``LT.lt =>
      match fn3 with
      | Expr.const name _ =>
        match name with
        | ``ite =>
            let iteArgs := unfolded.getAppArgs
            if iteArgs.size == 5 then
                let cond := iteArgs[2]!
                let t    := iteArgs[3]!
                let e    := iteArgs[4]!


                --   -- Boolean IF → split_ifs
                applyIfLemma loopBodyReturn cond
              else
                -- unexpected shape
                pure ()
        | ``OfNat.ofNat => pure ()
        | _ => applyThisLemma lt
      | _ => pure ()
    | _ => pure ()
  --logInfo m! "here?"
  match fn with
  | ``LE.le =>
    if containsMVar mainGoalType then
      --logInfo m! "here?{fn3}"
      match fn3 with
        | Expr.const name _ =>
          match name with
          | ``HSub.hSub => applyThisLemma sub
          | ``HAdd.hAdd => applyThisLemma add
          | ``HMul.hMul => applyThisLemma mul
          | ``HMod.hMod => applyThisLemma modLemma
          --| ``OfNat.ofNat => applyThisLemma rfl
          -- rfl is a place holder should be something else
          | ``ite =>

              let iteArgs := unfolded.getAppArgs
              if iteArgs.size == 5 then
                let cond := iteArgs[2]!
                let t    := iteArgs[3]!
                let e    := iteArgs[4]!


                --   -- Boolean IF → split_ifs
                applyIfLemma loopBodyReturn cond
              else
                -- unexpected shape
                pure ()
          | ``ZMod.val =>
              if !leftSide then
                applyZModLemma loopBodyReturn g mainGoalType leftSide hyps
              else
                applyThisLemma zmodGT
          | ``BitVec.toNat =>
            --logInfo m! "why not here?"
            if exprHasMod mainGoalType then
              applyThisLemma modLemma
            else
              if !leftSide then
                applyThisLemma bitvecLT
              else
                applyThisLemma bitvecGT
          | _ =>
              --logInfo m!"{name}"
              pure ()
        | _ =>
          if fn3.isFVar then applyZModLemma loopBodyReturn g mainGoalType leftSide hyps
    else
      --logInfo m! "here2 {fn3}"
        --logInfo m! "{args[args.size-1]!.getAppFn}"
         match fn3 with
          | Expr.const name _ =>
            match name with
            | ``OfNat.ofNat => applyThisLemma constLeq
            -- | ``BitVec.toNat =>
            --     if exprHasMod mainGoalType then
            --         applyThisLemma modLemma
            --     else
            --         logInfo m! "here3"
            --         applyThisLemma  bitvec
            | ``HMod.hMod => applyThisLemma  modLemma
            | ``ite   =>
                let iteArgs := unfolded.getAppArgs
                  if iteArgs.size == 5 then
                    let cond := iteArgs[2]!
                    let t    := iteArgs[3]!
                    let e    := iteArgs[4]!


                    --   -- Boolean IF → split_ifs
                    applyIfLemma loopBodyReturn cond
                  else
                    -- unexpected shape
                    pure ()
            | _ =>
             -- logInfo m! "Why are we not here?"
              if terms.size >= 1 then
                applyThisLemma expLeq
              else
                pure ()
          | _ =>
           --logInfo m! "Because we are here?"
           pure ()
    | _ =>
      --logInfo m! "{fn3}"
      pure ()

@[tactic tryApplyLemHyps]
elab_rules : tactic
| `(tactic| try_apply_lemma_hyps [$hs,*]) => do
  let hyps := (hs.getElems.map (·.getId)).toList
  let mut progress := true
  let mut need_to_valify :=false
  let mut sargs :
  Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                        `Lean.Parser.Tactic.simpErase,
                        `Lean.Parser.Tactic.simpLemma]) := #[]
  for i in hs.getElems do
          let sa ← `(simpArg| $i:term)
          let ua :
          TSyntax [`Lean.Parser.Tactic.simpStar,
                  `Lean.Parser.Tactic.simpErase,
                  `Lean.Parser.Tactic.simpLemma] :=
          ⟨sa.raw⟩
          sargs := sargs.push ua
  -- begin by factoring out multiplication for all goals
  -- important for mux discovery
  evalTactic (← `(tactic| all_goals try rw [neg_add_to_sub]))
  evalTactic (← `(tactic| all_goals try rw [<- sub_eq_add_neg]))
  evalTactic (← `(tactic| all_goals try rw [neg_param]))
  evalTactic (← `(tactic| all_goals try rw [sub_add_right_recursive]))
  evalTactic (← `(tactic|  all_goals try simp [Nat.mul_assoc]))
  let mut sanity <- getGoals
  if sanity.isEmpty then
    return
  let mut cont := true
  let mut count  := 0
  while (cont ) do
    try
      evalTactic (← `(tactic| all_goals rw [Nat.mul_comm_ofNat]))
    catch _ =>
      cont := false
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut did_mux := false
  -- as long as we are making progress then continue
  count  := 0
  while (progress ) do
    --logInfo m!"we get here?"
    count := count + 1
    if did_mux then do
      --logInfo m! "We are post did mux"
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
      --logInfo m! "GOAL {g}"
      let goalType ← g.getType
      --logInfo m! "GOALS {<- getGoals}"
      -- first we try to apply hypothesis
      let instantiatedGoalType ← instantiateMVars goalType
      let (fn, args) := instantiatedGoalType.getAppFnArgs
      let terms ← collectTerms instantiatedGoalType
      let i := countMinusOps instantiatedGoalType
     -- logInfo m!"HUH{<- firstCompositeInsideVal? instantiatedGoalType}"
      if (<- firstCompositeInsideVal? instantiatedGoalType) ||  need_to_valify then do
        try
          evalTactic (← `(tactic| valify [$sargs,*]))
          progress := true
          handled := true
        catch _ => pure ()
        if i > 0 then
          try
            for _ in [:i] do
                evalTactic (← `(tactic| try valify [$sargs,*]))
                evalTactic (← `(tactic| rw [ZMod.val_sub]))
                evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
                evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
                evalTactic (← `(tactic| try simp))
            let gs <- getGoals
            updatedGoalsReversed := gs ++ updatedGoalsReversed
            progress := true
            handled := true
            --logInfo m! "why do we end up here"
            continue
              --evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
          catch  e =>
              --progress := false
              let gs <- getGoals
              updatedGoalsReversed := gs ++ updatedGoalsReversed
              --logInfo m! "FAILED"
              continue
        else
            let gs <- getGoals
            updatedGoalsReversed := gs ++ updatedGoalsReversed
      else
        if isBitVecType instantiatedGoalType then do
          try
            if i == 0 then
              evalTactic (← `(tactic| bvify [$sargs,*]))
            for _ in [:i] do
                evalTactic (← `(tactic|  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
                evalTactic (← `(tactic| try bvify [$[$sargs],*] ) )
            let gs <- getGoals
            updatedGoalsReversed := gs ++ updatedGoalsReversed
            progress := true
            handled := true
            continue
                --evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
            catch  _ =>
              handled :=true
              progress := false
              let gs <- getGoals
              updatedGoalsReversed := gs ++ updatedGoalsReversed
              --logInfo m! "FAILED"
              continue
      -- UNCOMMENT LATER

      if exprHasMod instantiatedGoalType then do

         let mut modLoop:= true
         while (modLoop) do
            count :=count + 1
            try
              evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
              let cur_g ← getGoals
              --logInfo m! "Goals after [Nat.mod_eq_of_lt]):\n{← getGoals}"
              match cur_g with
              | [] =>
                  throwError "❌ No goals after Nat.mod_eq_of_lt"
              | g_one :: []  =>
                  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$hs],*]))

                  let after ← getGoals
                  --logInfo m! "Goals after try_apply_lemma_hyps:\n{after}"

                  if after.isEmpty then
                    --logInfo "🎉 SUCCESS: isolated goal solved. Restoring remaining goals."
                    progress := true
                    handled := true
                    let gs <- getGoals
                    updatedGoalsReversed := gs ++ updatedGoalsReversed
              --logInfo m! "FAILED"
                    --logInfo m! "Goals after restore {<- getGoals}:\n"
                    continue
                  else
                    --logInfo "❌ try_apply_lemma_hyps did NOT solve the isolated goal"
                    throwError m! "try_apply failed {after}"
              | g_one :: g_last :: rest_rev => do
                  setGoals [g_last]
                  --logInfo m! "Goals after isolate:\n{← getGoals}"
                  --logInfo "Attempting: try_apply_lemma_hyps"
                  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$hs],*]))

                  let after ← getGoals
                  --logInfo m! "Goals after try_apply_lemma_hyps:\n{after}"

                  if after.isEmpty then
                    --logInfo "🎉 SUCCESS: isolated goal solved. Restoring remaining goals."
                    setGoals ( [g_one ] ++ rest_rev )
                    progress := true
                    handled := true
                    let gs <- getGoals
                    updatedGoalsReversed := gs ++ updatedGoalsReversed
              --logInfo m! "FAILED"
                    --logInfo m! "Goals after restore {<- getGoals}:\n"
                    continue
                  else
                    --logInfo "❌ try_apply_lemma_hyps did NOT solve the isolated goal"
                    throwError m! "try_apply failed {after}"
            catch e =>
                --logInfo m! "Could not remove mod {e.toMessageData}?"
                modLoop := false

      --   evalTactic (← `(tactic| try simp))
      --   while (modLoop) do
      --     try
      --         evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
      --         --evalTactic (← `(tactic| nth_rewrite 2 [Nat.mod_eq_of_lt]))
      --     catch  _ =>
      --         evalTactic (← `(tactic| try rw [Nat.mod_eq_of_lt]))
      --         modLoop := false

      --   let gs <- getGoals
      --   updatedGoalsReversed := gs ++ updatedGoalsReversed
      --   progress := true
      --   handled := true
      --   continue
      -- Note: Here we use a continuation to let our callees return by
      -- short-circuiting the rest of the computation.
      if progress then
          --setGoals (updatedGoalsReversed.reverse ++ goalQueue.dList ++ goalQueue.eList.reverse)
          --progress := false
          --logInfo m! "but not here?"
          continue
     -- logInfo m!"umm..."
      let loopBodyResult ← (ContT.run · pure) $ MonadCont.callCC $ fun loopBodyReturn => do
       -- logInfo m!"here?"
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
          --logInfo m! "TERMS{terms.toList}"
          --logInfo m! "TERMS{bothArgsAreApps instantiatedGoalType}"
          if ((terms.size = 2))  && ( (← containsSub instantiatedGoalType) ||  bothArgsAreApps instantiatedGoalType ) then
             --try
             --logInfo m! "HASSDSA"
             caseByCaseOnTwoVariables loopBodyReturn g hyps terms
            -- catch _ => pure ()
          --try to apply Lean's range analysis lemmas
          -- for n in terms.toArray do
          --   logInfo m!"{n}"
          --logInfo m!"✅ Stuck on {goalType} with {terms.size}"
          if terms.size >= 1 then
            findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps
          else
            let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
            let bitvec ← monadLift (m := TacticM) ``(BitVec.toNatLT)
            let modLemma ← monadLift (m := TacticM) ``(mod_le_pred)
            let (fn, args) := instantiatedGoalType.getAppFnArgs
 -- logInfo m! "{args[args.size-1]!} => {containsMVar args[args.size-1]!}"
            let unfolded := ← monadLift $ withTransparency .reducible (whnf args[2]!)
            let fn3 := unfolded.getAppFn
            --ogInfo m! "{fn}"
               match fn with
                  | ``LE.le =>
                    --if containsMVar instantiatedGoalType then
                      match fn3 with
                        | Expr.const name _ =>
                          match name with
                          --| ``OfNat.ofNat => applyThisLemma loopBodyReturn g instantiatedGoalType false rfl
                          | ``ZMod.val =>
                              applyZModLemma loopBodyReturn g  instantiatedGoalType false hyps
                          | ``BitVec.toNat =>
                              if exprHasMod instantiatedGoalType then
                                applyThisLemma loopBodyReturn g instantiatedGoalType false modLemma
                              else
                                 applyThisLemma loopBodyReturn g instantiatedGoalType false bitvec
                          --|  ``HMod.hMod => applyThisLemma loopBodyReturn g instantiatedGoalType false modLemma
                          -- rfl is a place holder should be something else
                          | _ =>
                              --logInfo m! "{fn}"
                              -- this is good we have zero variables we should do this
                              if containsMVar instantiatedGoalType then
                                applyThisLemma loopBodyReturn g instantiatedGoalType false rfl
                              else
                                pure ()

                        | _ =>
                          if containsMVar instantiatedGoalType then
                              applyThisLemma loopBodyReturn g instantiatedGoalType false rfl
                          else
                              pure ()
                  -- | ``LT.lt =>
                  --   match fn3 with
                  --     | Expr.const name _ =>
                  --         match name with
                  --        -- |  ``HMod.hMod => applyThisLemma loopBodyReturn g instantiatedGoalType false modLemma
                  --          | _ => pure ()
                  --     | _ => pure ()
                  | _ => pure ()
            --applyThisLemma loopBodyReturn g instantiatedGoalType rfl
            --findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps

        -- if other techniques did not work try decide
        try
          monadLift $ do evalTactic (← `(tactic| decide))
          --logInfo m! "Issue here!!"
          if ← g.isAssigned then
            --logInfo m!"✅ Fully solved goal using decide {goalType}"
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
         --logInfo m! "LEFTSIDE: {loopBodyResult.leftSide}"
         let rev := loopBodyResult.goals
         --logInfo m! "{rev}"
         let rev :=
            match rev with
            | a :: b :: rest => b :: a :: rest
            | _ =>
              rev
          updatedGoalsReversed :=  updatedGoalsReversed ++ rev.reverse
      else
        --logInfo m! "we are here?"
        updatedGoalsReversed := loopBodyResult.goals.reverse ++ updatedGoalsReversed
    -- Note: we built the updated goals list in reverse to avoid repeatedly
    -- traversing an ever-growingly long prefix.
    --logInfo m! "NEW GOALS {updatedGoalsReversed}"
    setGoals (updatedGoalsReversed.reverse ++ goalQueue.dList ++ goalQueue.eList.reverse)
    if (!progress) then
      try
        evalTactic (← `(tactic| omega))
        --logInfo m! "Issue here?"
        --handled := true; progress := true
        progress:= true
      catch _ => pure ()
    if (!progress) then
      try
        let g <- getMainGoal
        --logInfo m! "NO the issue is here?\n {g}"
        evalTactic (← `(tactic| simp))
        --handled := true; progress := true
        progress:= true
      catch _ => pure ()


  --evalTactic (← `(tactic| try apply Nat.le_refl; try simp))
--   try_apply_lemma_hyps []


abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
variable (x : FF0)
variable (y : FF0)
 abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513

-- abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513


-- -- instance : Fact (Nat.Prime ff) := by sorry
-- -- instance : Fact (NeZero ff) := by sorry


-- -- example {b a : BitVec 1} : (if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[1] = true then
-- -- --       if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[1] = true then 1 else 0
-- -- --     else 0) %
-- -- --     52435875175126190479447740508185965837690552500527637822603658699938581184513 <
-- -- --   4 := by
-- -- --  try_apply_lemma_hyps []

-- example {x y:  FF0}  (fv1 fv2 : Vector FF0 8)  (h1: ZMod.val fv2[7] ≤ 1) (h2: ZMod.val fv1[7] ≤ 1) : ZMod.val (fv1[7] * fv2[7]) ≤ ZMod.val (fv1[7] + fv2[7])  := by
-- --ry valify
-- --simp [Nat.mul_assoc]
-- --rw [ZMod.val_sub]
-- try_apply_lemma_hyps [h1, h2]


-- example {b a:BitVec 1} : ZMod.val (Nat.cast b.toNat : FF0)   < 10 := by
-- simp
-- try_apply_lemma_hyps []



-- example : 52435875175126190479447740508185965837690552500527637822603658699938581184514 >= (fresh_pf1_is_zero).val := by
--     try_apply_lemma_hyps []


-- lemma aaa {a b : BitVec 2} : a.toNat <= (b.toNat + 3 ) := by
--   try_apply_lemma_hyps []


-- example : 64 < 5243ss5875175126190479447740508185965837690552500527637822603658699938581184513 := by
--  try_apply_lemma_hyps []




-- instance : Fact (NeZero ff) := by sorry
-- example {x : BitVec 100} : (x+y) % 500 < 2000 := by
--   try_apply_lemma_hyps []


-- example {smt_fresh_1  smt_fresh_2: FF0} : (ZMod.val smt_fresh_1 <= 1 ) -> (ZMod.val smt_fresh_1) + (ZMod.val smt_fresh_2)  ≤  2^256 := by
-- intro h
-- try_apply_lemma_hyps [h]

-- example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> 1 - fv[0].val * fv[1].val < ff := by
--   intros h1 h2
--   try_apply_lemma_hyps [h1, h2]


-- lemma aaa2 {a b : BitVec 2} : a.toNat <= (b.toNat + 3 ) := by

--   try_apply_lemma_hyps []


-- -- -- -- -- -- -- -- -- -- Idea: when doing Nat.le_refl check if we have at least two variables

-- lemma aaa1 {a b : BitVec 2} : a.toNat ≤ (b.toNat + 3) := by
--   try_apply_lemma_hyps []



-- example { fv : Vector (ZMod ff) 8} :
-- ( h1 : fv[0].val ≤ 1) -> (h2 : fv[1].val ≤ 1) -> ( h3 : fv[2].val ≤ 1) ->
-- ( fv[0].val * fv[1].val ≤ 1) := by
--   intros h1 h2 h3

--   try_apply_lemma_hyps [h1, h2 ,h3]



-- example { fv : Vector (ZMod ff) 8} :
-- ( h1 : fv[0].val ≤ 1) -> (h2 : fv[1].val ≤ 1) -> ( h3 : fv[2].val ≤ 1) ->
-- ( fv[0].val * fv[1].val < 2) := by
-- intros h1 h2 h3

-- try_apply_lemma_hyps [h1, h2 ,h3]


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --Example 2 that needs to work

-- example {fv : Vector (ZMod ff) 8}:
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) ->  (1 - fv[0].val * fv[1].val < ff) := by
-- intros h1 h2 h3
-- try_apply_lemma_hyps [h1, h2, h3]

-- example {fv : Vector (ZMod ff) 8}:
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) ->
-- (fv[0].val * fv[1].val + (1 - fv[0].val) * (1 - fv[1].val) <= 1) := by

-- intros h1 h2 h3
-- try_apply_lemma_hyps [h1, h2, h3]



-- -- -- -- -- -- example { b a : BitVec 2} : a.toNat ≤
--  example {fv : Vector (ZMod ff) 8}:
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) ->
-- (if fv[0] = 0 then 1 - fv[1].val else fv[1].val )< 2 := by
-- intro h1 h2 h3
-- try_apply_lemma_hyps [h1, h2, h3]



-- -- -- -- -- -- -- -- BAD B/C NAT.le_trans should be 2 variables or more only

-- example {b a : BitVec 2} :
--   (a.toNat * (b.toNat + 3 - a.toNat) ≤ 200) := by
--   try_apply_lemma_hyps []


-- -- -- -- -- PROBLEM

-- example {fv : Vector (ZMod ff) 8} :
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) -> fv[0].val * fv[1].val % ff ≤ (fv[0].val + fv[1].val) % ff := by
-- intros h1 h2 h3
-- focus try_apply_lemma_hyps [h1, h2, h3]



-- example {fv : Vector (ZMod ff) 8} :
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) -> fv[0].val + fv[1].val < ff
--  /\ (fv[0].val * fv[1].val % ff ≤ (fv[0].val + fv[1].val) % ff) := by
-- intros h1 h2 h3
-- split_ands
-- try_apply_lemma_hyps [h1, h2, h3]

-- -- --focus try_apply_lemma_hyps [h1, h2, h3]


-- example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) -> ( (1 - (fv[0].val * fv[1].val % ff + (1 - fv[0].val) * (1 - fv[1].val) % ff) % ff) % ff < 7
-- /\ (fv[0].val * fv[1].val % ff + (1 - fv[0].val) * (1 - fv[1].val) % ff) % ff ≤ 1) := by
--   intro h1 h2 h3
--   split_ands
--   try_apply_lemma_hyps [h1, h2, h3]


-- example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) ->  1 - (fv[0].val * fv[1].val + (1 - fv[0].val) * (1 - fv[1].val)) < 7 := by
-- try_apply_lemma_hyps [h1, h2, h3]



-- example {a b :BitVec 2} : ((if b[0] = true then 1 else 0) + if a[0] = true then 1 else 0) ≥
--  if a[0] = true then if b[0] = true then 2 else 0 else 0 := by
--  try_apply_lemma_hyps []


-- example {fv : Vector (ZMod ff) 8} :
-- (h1 : fv[0].val ≤ 1) ->
-- (h2 : fv[1].val ≤ 1) ->
-- (h3 : fv[2].val ≤ 1) -> (fv[0] + fv[1]).val < ff := by
--  intro h1 h2 h3
--  try_apply_lemma_hyps [h1, h2, h3]








--  example {a b c : BitVec 1} :
--  (if a[0] = true then
--       (((if c[0] = true then 1 else 0) + if b[0] = true then (1: ZMod ff) else 0) -
--           if b[0] = true then if c[0] = true then 2 else 0 else 0) *
--         2
--     else 0).val ≤
--   ((((if c[0] = true then 1 else 0) + if b[0] = true then (1: ZMod ff) else 0) + if a[0] = true then 1 else 0) -
--       if b[0] = true then if c[0] = true then 2 else 0 else 0).val := by
--     try_apply_lemma_hyps []








-- example {a b : BitVec 1} : ((if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[0] = true then 1 else 0) +
--     if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[1] = true then 2 else 0) <
--   115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
--   try_apply_lemma_hyps []

-- variable (c : BitVec 2)
-- variable (b : BitVec 2)
-- variable (a : Bool)
-- variable (d : Bool)
-- example : (if (a) then 1 else 0) <= 2 := by
--   try_apply_lemma_hyps[]


-- -- -- -- WHY IS THIS BREAKING BOTH
-- variable (c : BitVec 2)
-- variable (b : BitVec 2)
-- variable (a : Bool)
-- example :((if (if a = true then b else c)[0] = true then 1 else 0) - if (if a = true then b else c)[1] = true then 2 else 0) <
--   2 ^ 256
--  := by
--   try_apply_lemma_hyps[]



-- variable (a : BitVec 2)
-- variable (x_bit1 : FF0)
-- variable (x_bit0 : FF0)
-- lemma correct
-- (a : BitVec 2)
-- (x_bit1 x_bit0 : FF0)
-- (h0_new :  (if (if a[0] = true then 1#1 else 0#1) = 1#1 then 1 else 0) = x_bit0)
-- (h0 : (if a[0] = true then 1#256 else 0#256) = BitVec.ofNat 256 (ZMod.val x_bit0))
-- (h1_new : (if (if a[1] = true then 1#1 else 0#1) = 1#1 then 1 else 0) = x_bit1)
-- (h1 : (if a[1] = true then 1#256 else 0#256) = BitVec.ofNat 256 (ZMod.val x_bit1)) :
-- ZMod.val x_bit0 + ZMod.val x_bit1  * 2 < 52435875175126190479447740508185965837690552500527637822603658699938581184513 := by
-- try_apply_lemma_hyps [h0_new, h1_new]
