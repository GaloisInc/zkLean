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
open Std

namespace BVModEq

set_option maxHeartbeats 20000000000

syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")? : tactic

def varToHyp : Std.HashMap FVarId Expr := {}

lemma neg_add_to_sub {α : Type*} [AddCommGroup α] (a b : α) :
  -a + b = b - a := by
  rw [sub_eq_add_neg]
  rw [add_comm (-a) b]

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

/-- Detect `BitVec.ofNat k (ZMod.val x)` with debugging prints. -/
def matchOfNatVal? (e : Expr) : MetaM (Option (Nat × Expr × Expr)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Debug

  -- We expect: BitVec.ofNat k (ZMod.val x)
  if fn.isConstOf ``BitVec.ofNat ∧ args.size = 2 then
    let kExpr := args[0]!
    let valExpr := args[1]!
    match kExpr.getAppFn with
    | Expr.const ``OfNat.ofNat _ =>
        -- logInfo m!"    Found nat literal width = {kExpr}"
        -- logInfo m!"    kExpr.args = {kExpr.getAppArgs}"
        match kExpr.getAppArgs with
        | #[_, numExpr, _inst] =>
            match numExpr with
            | Expr.lit (Literal.natVal k) =>
               let fn2 := valExpr.getAppFn
               let args1 := kExpr.getAppArgs
               let args2 := valExpr.getAppArgs

                if fn2.isConstOf ``ZMod.val ∧ args2.size = 2 ∧ args1.size=3 then
                  return some (k, args2[1]!, args2[0]!)
                else
                  return none
            | _ => return none

        | _ => return none
    | _ =>
        return none
  else
    return none



-- /-- Recursively gather all `(width, x)` inside an expression -/
-- partial def collectMatches (e : Expr) : MetaM (Array (Nat × Expr)) := do

--   let mut acc := #[]
--   if let some p <- matchOfNatVal? e then
--     logInfo m!"  MATCHED pattern: {p}"
--   for a in e.getAppArgs do
--     acc := acc ++ (← collectMatches a)
--   return acc

/-- Collect from goal AND hypotheses -/


def exprInsert (k : Expr) (v : α) (l : List (Expr × α)) : MetaM (List (Expr × α)) := do
  let mut out := []
  let mut replaced := false
  for (k', v') in l do
    if ← isDefEq k k' then
      out := (k, v) :: out
      replaced := true
    else
      out := (k', v') :: out
  if ¬ replaced then
    out := (k, v) :: out
  return out

def exprLookup (k : Expr) (l : List (Expr × α)) : MetaM (Option α) := do
  for (k', v) in l do
    if ← isDefEq k k' then
      return some v
  return none


/-- Recursively gather all `(width, x)` pairs inside an expression, for matches
    of the form `BitVec.ofNat k (ZMod.val x)`. -/
partial def collectMatches (e : Expr) : MetaM (Array (Nat × Expr × Expr)) := do
  let mut acc := #[]
  if let some p ← matchOfNatVal? e then
    acc := acc.push p
  for arg in e.getAppArgs do
    acc := acc ++ (← collectMatches arg)
  return acc

/-- Collect all `(width, x)` pairs from the goal type and all local hypotheses
    (both their types and, if present, their values). -/
def collectFromContext : TacticM (Array (Nat × Expr × Expr)) := do
  let goal ← getMainGoal
  let goalTy ← goal.getType
  goal.withContext do
    let mut out : Array (Nat × Expr × Expr) := #[]
    out := out ++ (← collectMatches goalTy)

    let lctx ← getLCtx
    --logInfo "=== RAW HYP TYPES ==="
    for decl in lctx do
      --logInfo m!"{decl.userName}: {← ppExpr decl.type}"

      if decl.isImplementationDetail then
        continue

      -- collect from hypothesis type
      out := out ++ (← collectMatches decl.type)

      -- collect from hypothesis value (if any)
      if let some v := decl.value? then
        out := out ++ (← collectMatches v)

    return out


/--
`autoCastBits`:
- scans the goal + hypotheses for occurrences of `BitVec.ofNat k (ZMod.val x)`
- groups them by variable `x`
- for any `x` that appears at multiple widths, say `{6, 256}`, it adds a lemma

  `have x_cast_6 :
    BitVec.ofNat 6 (ZMod.val x) =
      (BitVec.ofNat 256 (ZMod.val x)).setWidth 6 := by simp`
- you can then use those lemmas to rewrite / simp.
-/

def lookupGroup (fid : FVarId) (gs : List (FVarId × List Nat))
  : Option (List Nat) :=
  match gs.find? (fun (p : FVarId × List Nat) => p.fst == fid) with
  | some (_, ws) => some ws
  | none => none

#check ZMod.val

def insertGroup (fid : FVarId) (w : Nat)
    (gs : List (FVarId × List Nat))
    : List (FVarId × List Nat) :=
  let rec go (acc : List (FVarId × List Nat)) (rest : List (FVarId × List Nat)) :=
    match rest with
    | [] => (fid, [w]) :: acc
    | (fid', ws) :: tl =>
      if fid' == fid then
        (fid', w :: ws) :: acc ++ tl
      else
        go ((fid', ws) :: acc) tl
  go [] gs


elab "autoCastBits" : tactic => do
  --logInfo "=== autoCastBits: starting ==="

  let pairsArr ← collectFromContext
  let pairs := pairsArr.toList
  --logInfo m!"Detected pairs (width, expr): {pairs}"

  -- Group widths by underlying variable, keyed by FVarId
  let mut groups : List (FVarId × List Nat) := []
  let mut modulus : Option Expr := none
  for (w, x, f) in pairs do
    modulus := some f
    if let some fid := x.fvarId? then
      match lookupGroup fid groups with
      | some ws =>
          groups := insertGroup fid w groups
      | none =>
          groups := (fid, [w]) :: groups
  --logInfo "=== Groups after aggregation ==="
  for (fid, ws) in groups do
   -- logInfo m!"{fid.name}: widths = {ws}"

  let some modExpr := modulus
    | throwError "[autoCastBits] no modulus found"
  let lctx ← getLCtx
  let mut goal ← getMainGoal

  -- For each variable that appears with multiple distinct widths, create a lemma
  for (fid, ws) in groups do
    let uniq := ws.eraseDups
    if uniq.length > 1 then
      let minW := uniq.foldl Nat.min uniq.head!
      let maxW := uniq.foldl Nat.max uniq.head!

      -- reconstruct the variable and get a nicer name
      let x := Expr.fvar fid
      match lctx.find? fid with
      | none =>
          pure ()
      | some decl => do
          let baseName := decl.userName
          let lemmaName := baseName.appendAfter s!"_cast_{minW}"

          let zmodValBase := mkConst ``_root_.ZMod.val
          let zmodValTyped := mkApp zmodValBase modExpr
          let valExpr := mkApp zmodValTyped x

          -- lhs : BitVec.ofNat minW (ZMod.val x)
          --logInfo m!"x = {← ppExpr x}"
          let lhs :=
             mkAppN (mkConst ``BitVec.ofNat) #[mkNatLit minW, valExpr]

          let bigVec :=
            mkAppN (mkConst ``BitVec.ofNat)
              #[ mkNatLit maxW, valExpr ]

          let rhs :=
            mkAppN (mkConst ``BitVec.setWidth)
              #[ mkNatLit maxW, mkNatLit minW, bigVec ]


          let eq <- mkEq lhs rhs
          --logInfo m!"Adding lemma {eq} for {baseName}: minW={minW}, maxW={maxW}"

          -- Build the proof by `simp`
          let pf ← elabTerm (← `(by simp)) eq

          let newGoal ← goal.assert lemmaName eq pf
          goal := newGoal

  replaceMainGoal [goal]
  --logInfo "=== autoCastBits: finished ==="













def isExists (e : Expr) : Bool :=
  match e with
  | .app (.app (.const ``Exists _) _) (.lam _ _ _ _) => true
  | _ => false

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

partial def countAnds (e : Expr) : Nat :=
  let e := e.consumeMData

  match e.getAppFn with
  | Expr.const ``And _ =>
      let args := e.getAppArgs
      if h : args.size ≥ 2 then
        let a := args[0]!
        let b := args[1]!
        1 + countAnds a + countAnds b
      else
        1
  | _ =>
      match e with
      | Expr.app f x => countAnds f + countAnds x
      | Expr.lam _ _ body _ => countAnds body
      | Expr.forallE _ _ body _ => countAnds body
      | _ => 0


partial def countOrs (e : Expr) : Nat :=
  let e := e.consumeMData

  match e.getAppFn with
  | Expr.const ``Or _ =>
      let args := e.getAppArgs
      if h : args.size ≥ 2 then
        let a := args[0]!
        let b := args[1]!
        1 + countOrs a + countOrs b
      else
        1
  | _ =>
      match e with
      | Expr.app f x => countOrs f + countOrs x
      | Expr.lam _ _ body _ => countOrs body
      | Expr.forallE _ _ body _ => countOrs body
      | _ => 0



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
  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try unfold BVModEq.smtSignExtend at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try unfold BVModEq.smtZeroExtend at $(mkIdent h.getId):ident ))
  evalTactic (← `(tactic| try unfold BVModEq.BitVec.mod at $(mkIdent h.getId):ident ))
  evalTactic (← `(tactic| try rw [map_f_to_bv_circ_spec] at $(mkIdent h.getId):ident) )
  let mut subLoop := true
    while (subLoop) do
    try
      evalTactic (← `(tactic| rw [<- sub_eq_add_neg] at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop := false
  subLoop := true
    while (subLoop) do
    try
      evalTactic (← `(tactic|  rw [neg_add_to_sub] at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop := false
  let i ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    countMinusOps2 decl.type
  --logInfo m! "MINUSES HIP {i}"

  -- TO DO THIS SHOULD BE A TRY CATCH LOOP!
  if i > 0 then
    let mut mLoop := true
    while (mLoop) do
    try
     evalTactic (← `(tactic| rw [sub_add_right_recursive] at $(mkIdent h.getId):ident))
    catch _ =>
      mLoop := false
  evalTactic (← `(tactic| try simp (config := { maxSteps := 200000 }) only [BVModEq.ZMod.eq_if_val] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  --evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  for _ in [0:i] do
       evalTactic (← `(tactic| try rw [ZMod.val_sub] at $(mkIdent h.getId):ident))
       evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident ) )
       evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
       evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))

  evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  subLoop := true
  while (subLoop ) do
    try
      evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
      evalTactic (← `(tactic| try valify [$[$sargs],*]   at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop  := false
  subLoop := true
  while (subLoop) do
    try
       evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop := false
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256] at $(mkIdent h.getId):ident))
  let n ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    let ty ← instantiateMVars decl.type
    let ty ← whnfR ty
    logInfo m!"{ty}"
    pure (countAnds decl.type + countOrs ty)
  logInfo m!"ORS {n}"
  for _ in [:n] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))
  for _ in [:i] do
      evalTactic (← `(tactic| try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))








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
      --logInfo m!"🔍 Found composite: {if_comp}"

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

  evalTactic (← `(tactic| try unfold BVModEq.bool_to_bv ))
  evalTactic (← `(tactic| try unfold BVModEq.map_bv_to_f  ))
  evalTactic (← `(tactic| try unfold BVModEq.smtSignExtend ))
  evalTactic (← `(tactic| try unfold BVModEq.smtZeroExtend  ))
  evalTactic (← `(tactic| try unfold BVModEq.BitVec.mod  ))
  evalTactic (← `(tactic| try rw [map_f_to_bv_circ_spec] ))
  let mut subLoop := true
    while (subLoop) do
    try
      evalTactic (← `(tactic| rw [<- sub_eq_add_neg]))
    catch _ =>
      subLoop := false
  subLoop := true
    while (subLoop) do
    try
      evalTactic (← `(tactic| rw [neg_add_to_sub]))
    catch _ =>
      subLoop := false
  let mut g ← getMainGoal
  let mut t ← g.getType
  -- if isExists t then
  --      evalTactic (← `(tactic| refine ?_))
  let i  ←  countMinusOps2 t
  let k := countOrs t + countAnds t
  logInfo m! "MINUSUS {i} for {t}"

  --TO DO THIS SHOULD BE A TRY CATCH LOOP!
  if i > 0 then
    let mut mLoop := true
    while (mLoop) do
    try
     evalTactic (← `(tactic| rw [sub_add_right_recursive]))
    catch _ =>
      mLoop := false
  evalTactic (← `(tactic| try simp (config := { maxSteps := 200000 }) only [BVModEq.ZMod.eq_if_val] ))
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]))
  evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
  for _ in [0:k] do
      -- let me <- getMainGoal
      -- logInfo m! "Me1 {me}"
      evalTactic (← `(tactic| try rw [BVModEq.ZMod.eq_if_val] ))
      evalTactic (← `(tactic| try valify [$[$sargs],*] ) )




  if i > 0 then
     evalTactic (← `(tactic|  try rw [<- sub_eq_add_neg]))
     evalTactic (← `(tactic|  try rw [sub_add_right_recursive]))
    for _ in [0:i] do
      -- let me <- getMainGoal
      -- logInfo m! "Me2 {me}"
      evalTactic (← `(tactic| try rw [ZMod.val_sub]))
      evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
      --evalTactic (← `(tactic| try simp ) )
      --evalTactic (← `(tactic| try rw  [Nat.mod_eq_of_lt]))
  evalTactic (← `(tactic| try simp ) )
  let goals <- getGoals
  if goals.isEmpty then
    return
  loopUntilDone
  let mut modLeft := true
  while (modLeft) do
    try
      evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val] ))
      evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
    catch _ =>
      modLeft := false
   subLoop := true
    while (subLoop) do
    try
       evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] ))
    catch _ =>
      subLoop := false
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  let n := countAnds t + k
  for _ in [:n] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff 256]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  if i > 0 then
    for _ in [:i] do
      evalTactic (← `(tactic| try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] ) )


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


def getVarEq (e : Expr) : Option FVarId :=
  match e with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
      if rhs.isFVar then
        some rhs.fvarId!
      else
        none
  | _ => none

def flattenAnds (h : TSyntax `ident) : TacticM (Array (TSyntax `ident)) :=
  withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hyp `{h.getId}` in context"

    let ty ← whnf decl.type
    let num := countAnds ty + 1
    if num == 1 then
      return #[h]

    -- perform `rcases h with ⟨h1, h2, ..., hn⟩`
    let names : Array (TSyntax `ident) :=
      (List.range num).map (fun i => mkIdent (Name.mkSimple s!"{h.getId}_{i+1}")) |>.toArray
    evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident with ⟨$[$names],*⟩))
    return names

/-- If the goal is `x < rhs` or `x ≤ rhs` and `x` is an fvar,
    return `some (lhsFVarId, rhs)`. Otherwise return `none`. -/
def detectLeOrLtGoal (goalExpr : Expr) : Option (FVarId × Expr) :=
  match goalExpr with
  -- x < rhs
  | .app (.app (.const ``LT.lt _) lhs) rhs =>
      if lhs.isFVar then
        some (lhs.fvarId!, rhs)
      else
        none
  -- x ≤ rhs
  | .app (.app (.const ``LE.le _) lhs) rhs =>
      if lhs.isFVar then
        some (lhs.fvarId!, rhs)
      else
        none
  | _ =>
      none



def smartTranslateOne
    (h : TSyntax `ident)
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma]))
                        (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident))): TacticM ( Option (TSyntax `ident) × Option (TSyntax `ident)) := do
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
        return (some h1, none)
    | none =>
         match getVarEq hType with
          | some rhsVarId => do
               --logInfo m! "We are here!!!"
              try

                evalTactic (← `(tactic| rw [duplicate] at $(mkIdent h.getId):ident))

                let newName := mkIdent (Name.mkSimple s!"{h.getId}_new")

                evalTactic (← `(tactic|
                  rcases $(mkIdent h.getId):ident with ⟨$(mkIdent h.getId):ident, $newName⟩))

                evalTactic (← `(tactic| try rw [BVModEq.bool_to_bv] at $(mkIdent newName.getId):ident))


                --evalTactic (← `(tactic| translate_hypothesis $h))

                -- in-place update:
                let m ← varToHypRef.get
                if m.contains rhsVarId then
                  pure ()
                else
                  varToHypRef.modify fun m => m.insert rhsVarId newName
                  -- if extraArgs.isEmpty then
                  --   evalTactic (← `(tactic| translate_hypothesis $h))

                  -- else
                  --   evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))
                  return (some newName ,some h)
              catch _ => pure ()
           | _ => pure ()


       return (none, some h)


def lookup (m : Std.HashMap FVarId (TSyntax `ident)) (id : FVarId) : Option (TSyntax `ident):=
  match m.toList.find? (fun (k, _) => k == id) with
  | some (_, v) => some v
  | none        => none
/-- Batch helper over a list of hypothesis idents.
    Returns the collected `*_1` names from `x*x=x` cases. -/
def smartTranslateMany
    (hs : Array (TSyntax `ident))
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma]))
    (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident))) : TacticM (Array (TSyntax `ident)) := do
  let mut picked : Array (TSyntax `ident) := #[]
  let mut translate : Array (TSyntax `ident) := #[]

  for h in hs do

   let (k?, w?) ← smartTranslateOne h extraArgs varToHypRef

-- If we got a k, push it
    match k? with
    | some k => picked := picked.push k
    | none   => pure ()

    -- If we got a w, translate the hypothesis
    match w? with
    | some w =>translate := translate.push h
    | none => pure ()
  for h in translate do
    if extraArgs.isEmpty then
              evalTactic (← `(tactic| translate_hypothesis $h))
            else
              evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))

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


  let varToHypRef ← IO.mkRef ({} : Std.HashMap FVarId (TSyntax `ident))
  let collected := (← smartTranslateMany ids sargs varToHypRef)

  let mut after ← getGoals
  if after.isEmpty then
    return
  evalTactic (← `(tactic| translate_goal))

  after ← getGoals
  if after.isEmpty then
    return
  try
     evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
  catch _ =>
    evalTactic (← `(tactic| autoCastBits))
    try
      while (true) do
        evalTactic (← `(tactic| intro h))
        evalTactic (← `(tactic| rw [h]))
    catch _ =>
       evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))


  --logInfo m! "Collected {collected}"
  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
  after ← getGoals

  if !after.isEmpty then
    while (!after.isEmpty) do
  -- record the current state
      let before ← getGoals

  -- run your tactics
      evalTactic (← `(tactic| translate_goal))
      evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))

  -- read the new state
      after ← getGoals

      -- if no change → stop
      if before == after then
        let goal ← getMainGoal
        let goalExpr ← instantiateMVars (← goal.getType)
        let terms <- collectTerms goalExpr

          -- detect goals of form  x < m  or  x ≤ m
        let termList := terms.toList

  -- require exactly one variable
        if termList.length != 1 then
            break
        let onlyName := termList.head!
        let lctx ← getLCtx
        match lctx.findFromUserName? onlyName with
        | none =>
            --logInfo m!"Variable {onlyName} not found in context"
            break
        | some decl =>
            let fvarId := decl.fvarId

            let varMap ← varToHypRef.get

            match lookup varMap fvarId with
            | some hypExpr =>
              --logInfo m! "{hypExpr}"
              evalTactic (← `(tactic| simp [← $hypExpr] at *))
              after ← getGoals
            | none =>
                break



 --rw [<- sub_eq_add_neg]



--ISSUES WITH RANGE ANALYSIS
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (a : BitVec 2)
-- variable (x_bit1 : FF0)
-- variable (x_bit0 : FF0)
-- lemma correct :
-- (((((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit1))))) → (((BVModEq.map_f_to_bv_circ 2  (((x_bit0) + (((x_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) = (a)))))
--  := by
--  translate_all


-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : Bool)
-- variable (a : Bool)
-- lemma correct :
-- (((((((((- (((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((a) → (b)))))))
--  := by
--  translate_all

--  rw [ZMod.val_sub]
--  valify


-- -- OVERFLOW INSTANCE
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : BitVec 2)
-- variable (b : BitVec 2)
-- variable (a : Bool)
-- lemma correct :
-- (((((if (((BVModEq.bool_to_bv 1 (if a then b else c)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (if a then b else c)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))) + (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))
--  := by
--    unfold map_bv_to_f
-- Options
-- def strict add n for all subtractions and don't remove mod aka always assume overflow
-- 1) strict translation out of scope
-- 2) up to user when to do strict translation
-- 3) first do weak then do strong
-- 4) try to prove that it is greater if it is not then do add n and continue
--

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (fresh_pf2_div_q_bit0 : FF0)
-- variable (b : BitVec 1)
-- variable (a : BitVec 1)
-- variable (fresh_pf7_cmp_bit1 : FF0)
-- variable (fresh_pf5_is_zero : FF0)
-- variable (fresh_pf1_div_r : FF0)
-- variable (fresh_pf6_cmp_bit0 : FF0)
-- variable (fresh_pf0_div_q : FF0)
-- variable (fresh_pf4_is_zero_inv : FF0)
-- variable (fresh_pf3_div_r_bit0 : FF0)



-- lemma correct :
-- ((((((((fresh_pf2_div_q_bit0) * (fresh_pf2_div_q_bit0))) = (fresh_pf2_div_q_bit0))) ∧ (((fresh_pf2_div_q_bit0) = (fresh_pf0_div_q))) ∧ (((((fresh_pf3_div_r_bit0) * (fresh_pf3_div_r_bit0))) = (fresh_pf3_div_r_bit0))) ∧ (((fresh_pf3_div_r_bit0) = (fresh_pf1_div_r))) ∧ (((((fresh_pf0_div_q) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b))) = (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- fresh_pf1_div_r))))) ∧ (((((fresh_pf4_is_zero_inv) * (((fresh_pf0_div_q) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- fresh_pf5_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf5_is_zero) * (((fresh_pf0_div_q) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((fresh_pf6_cmp_bit0) * (fresh_pf6_cmp_bit0))) = (fresh_pf6_cmp_bit0))) ∧ (((((fresh_pf7_cmp_bit1) * (fresh_pf7_cmp_bit1))) = (fresh_pf7_cmp_bit1))) ∧ (((((fresh_pf6_cmp_bit0) + (((fresh_pf7_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((fresh_pf1_div_r) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)) + (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((((- fresh_pf5_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (fresh_pf7_cmp_bit1))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) → (((if (((BVModEq.bool_to_bv 1 (BitVec.udiv a b)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf2_div_q_bit0)))))
--  := by
--   translate_all
  ---rw [BVModEq.ZMod.eq_if_val]


   -- (b + f - c) % f

  --  translate_goal
  --  bv_decide
  --  focus try_apply_lemma_hyps []
  --  sorry
  --  focus try_apply_lemma_hyps []
  --  focus try_apply_lemma_hyps []
  -- focus try_apply_lemma_hyps []


-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (d : Bool)
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (fresh_pf1_is_zero : FF0)
-- variable (fresh_pf0_is_zero_inv : FF0)
-- lemma correct :
-- (((((((((fresh_pf0_is_zero_inv) * (((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if d then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) = (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf1_is_zero) * (((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if d then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) → (((((((((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((a) ∧ (b)) ∧ (c)) ∧ (d)))))))))
--  := by
--  translate_all
--  --translate_goal
