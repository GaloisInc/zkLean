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
import ZKLean.Formalism

import BVModEq.RangeAnalysis
--import BVModEq.BVify
import BVModEq.Mappings

open Lean Meta Elab Tactic
open Lean.Parser.Tactic
open Std

namespace BVModEq


set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900

syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")?  (ppSpace term)? : tactic

def varToHyp : Std.HashMap FVarId Expr := {}

open Lean Meta



/-- Recursively compute a bit-width for a Nat expression.

    Strategy:
    * literals: exact width from their value
    * free vars: width = 1 (you can replace this with something smarter later)
    * application: recurse on args to get widths, then:
        - match on the head `fn` to handle known operators (HAdd, HSub, HMul, HMod, ZMod.val)
        - otherwise, combine child widths conservatively
-/

private def termFor (nm : Name) : TacticM (TSyntax `term) := withMainContext do
  match (← getLCtx).findFromUserName? nm with
  | some d => pure ⟨(mkIdent d.userName).raw⟩
  | none   => pure ⟨(mkIdent nm).raw⟩


partial def CalcBitWidth (e : Expr) (hs : Array (TSyntax `ident)) : MetaM Nat := do
  let fn  := e.getAppFn
  let args := e.getAppArgs

  match (← whnf e) with
    | (Expr.lit (Literal.natVal n)) =>
       return n
    | _ => pure ()
  match fn with
  | Expr.const name _ =>
     match name with
    | ``ZMod.val  =>

      let hyps := (hs.map (·.getId)).toList
      let lctx ← getLCtx

      for hName in hyps do
        let some decl := lctx.findFromUserName? hName
          | throwError m!"❌ Could not find a hypothesis named `{hName}`"
        match decl.type.getAppFnArgs with
        | (``LE.le, #[_, _, lhs, rhs]) =>
          match (← whnf rhs) with
          | (Expr.lit (Literal.natVal n)) => do

              if  (<- collectTerms e).contains (<- collectTerms lhs).toList[0]!  then
                 --logInfo m!"this is not the issue"
                 return n
              else
                pure ()

          | _ =>  pure ()
        | _ =>  pure ()
      --logInfo m! "WHY ARE WE HERE {e}"
      return ( <- CalcBitWidth args[0]! hs)
    |  ``Eq  =>
      return (Nat.max (<- CalcBitWidth args[args.size-1]! hs) (<- CalcBitWidth args[args.size-2]! hs))
    | ``HAdd.hAdd  =>
        if  args.size ≥ 2 then
          return  (<- CalcBitWidth args[args.size-1]! hs) + (<- CalcBitWidth args[args.size-2]! hs)
        else
          throwError "wrong # args Add"

    |  ``HSub.hSub  =>
        if  args.size ≥ 2 then
         return (<- CalcBitWidth args[args.size-2]! hs)
        else
          throwError "wrong # args Sub"
    | ``HMul.hMul  =>
        if  args.size ≥ 2 then
          return (<- CalcBitWidth args[args.size-1]! hs)  *  (<- CalcBitWidth args[args.size-2]! hs)
        else
          throwError "wrong # args Sub"
    | ``HMod.hMod  =>
        if  args.size ≥ 2 then
          return (<- CalcBitWidth args[args.size-2]! hs)
        else
          throwError "wrong # args Mod"
    | ``ite =>
        if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
        throwError "wrong # args ite"
    | ``Iff =>
        if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
        throwError "wrong # args Iff"
    | ``BitVec.ofNat =>
        if args.size ≥ 2 then
          return 2^(<- CalcBitWidth args[args.size-2]! hs)
        throwError "wrong # args BitVec.ofNat"
    | ``BitVec.toNat =>
        if  args.size ≥ 2 then
          return (<- CalcBitWidth args[args.size-2]! hs)
        throwError "wrong # args BitVec.toNat"
        --return 10
    | ``Or =>
       if  args.size ≥ 2 then
        return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
       throwError "wrong # args or {args}"
    | ``And =>
       if  args.size ≥ 2 then
        return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
       throwError "wrong # args and {args}"
    | ``GetElem.getElem =>
       if  args.size ≥ 2 then
        return  (<- CalcBitWidth args[args.size-2]! hs)
       throwError "wrong # args and {args}"
    | ``LE.le =>
       if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
       throwError "wrong # args and {args}"
    | _ =>
      logInfo m!"unsupported ap {name} with {args}"
      if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
      return 1
  | _ =>
      logInfo m!"unsupported ap {fn} with {args}"
      if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
      return 1

variable (x : ZMod 17 )

def X : ZMod 17:= sorry


def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    let lg := Nat.log2 (n - 1)
    lg + 1


lemma BitVec.ofNat_mod_move
    {f n w: Nat}
    [h: NeZero f]
    [h2: NeZero w]
    (hn : n < 2^w)
    (hf : f <  2^w) :
  BitVec.ofNat w (n % f)
    =
  BitVec.ofNat w n % BitVec.ofNat w f := by
  unfold BitVec.ofNat
  --simp
  apply congrArg
  simp_all
  apply Fin.eq_of_val_eq
  simp_all
  rw [Nat.mod_eq_of_lt]
  nth_rewrite 3 [Nat.mod_eq_of_lt]
  nth_rewrite 3 [Nat.mod_eq_of_lt]
  simp
  apply hf
  apply hn
  have h2: n % f < f := by
      apply Nat.mod_lt
      apply (Nat.pos_of_ne_zero h.out)
  simp
  apply lt_trans h2
  apply hf


lemma ZMod.val_le_BV {n : ℕ} [NeZero n] (a : ZMod n) (w : ℕ ) (h: n< 2^w) : BitVec.ofNat w (a.val) ≤ BitVec.ofNat w (n) := by sorry



lemma ZMod.val_sub_strict {f} [NeZero f]   (x y: ZMod f) : (x - y).val = (x.val + f - y.val ) % f
  := by
  by_cases h: y.val <= x.val
  --rw [<- Nat.add_mod_right]
  rw [ZMod.val_sub]
  have h1: (x.val - y.val) % f = (x.val - y.val)  := by
    rw [Nat.mod_eq_of_lt]
    apply Nat.lt_of_le_of_lt
    apply Nat.lt_sub
    apply ZMod.val_lt
  have h2 : (x.val - y.val) % f = (x.val + f - y.val) % f  := by
    rw [<- Nat.add_comm]
    rw [<- Nat.add_mod_right]
    rw [<- Nat.add_comm]
    rw [Nat.add_sub_assoc]
    apply h
  rw [<- h1]
  rw [<- h2]
  apply h
  have hxy : x - y = x + (-y) := by ring_nf
  rw [hxy]
  rw [ZMod.val_add]
  rw [ZMod.neg_val']
  simp
  rw [Nat.add_sub_assoc]
  apply ZMod.val_le



-- lemma neg_add_to_sub {α : Type*} [AddCommGroup α] (a b : α) :
--   -a + b = b - a := by
--   rw [sub_eq_add_neg]
--   rw [add_comm (-a) b]

lemma if_to_bounds {b: Prop} {x: ZMod f} [Decidable b]: (if b then 1 else 0) =  x <->
(if b then 1 else 0) =  x /\  ZMod.val x <= 1 := by
sorry

lemma duplicate {b  a: ZMod f} : b = a <->
  b = a /\ b = a := by
  simp

lemma duplicate_leq {b a: Nat} : b <= a <->
  b <= a /\ b <= a := by
  simp

-- lemma sub_add_right_recursive {α : Type*} [AddCommGroup α]
--     (a b c : α) : a - b + c = (a + c) - b := by
--   rw [sub_eq_add_neg, add_assoc]
--   rw [sub_eq_add_neg]
--   rw [add_comm (-b) (c)]
--   rw [add_assoc]

/-- Detect `BitVec.ofNat k (ZMod.val x)` with debugging prints. -/
def matchOfNatVal? (e : Expr) : MetaM (Option (Nat × Expr × Expr)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Debug
  --logInfo m!"{fn}"
  --logInfo m!"{args}"
  -- We expect: BitVec.ofNat k (ZMod.val x)
  if fn.isConstOf ``BitVec.ofNat ∧ args.size = 2 then
   --logInfo m!"{fn}"
    let kExpr := args[0]!
    let valExpr := args[1]!
    match kExpr.getAppFn with
    | Expr.const ``OfNat.ofNat _ =>
        --logInfo m!"    Found nat literal width = {kExpr}"
       -- logInfo m!"    kExpr.args = {kExpr.getAppArgs}"
        match kExpr.getAppArgs with
        | #[_, numExpr, _inst] =>
            match numExpr with
            | Expr.lit (Literal.natVal k) =>
               let fn2 := valExpr.getAppFn
               let args1 := kExpr.getAppArgs
               let args2 := valExpr.getAppArgs

                if fn2.isConstOf ``ZMod.val ∧ args2.size = 2 ∧ args1.size=3 then
                 -- logInfo m!"Ecuse me? {args2}"
                  return some (k, args2[1]!, args2[0]!)
                if fn2.isConstOf ``GetElem ∧ args2.size = 2 ∧ args1.size=3 then
                   --logInfo m!"{fn2}"
                   return some (k, args2[1]!, args2[0]!)
                else
                  --  logInfo m!"{valExpr}"
                  --  logInfo m!"{fn2}"
                  --  logInfo m!"{args2}"
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
  -- first inspect this node
  if let some p ← matchOfNatVal? e then
    acc := acc.push p
    --logInfo m!"{acc}"

  -- recursively explore all children
  --logInfo m!"{e}"
  match e with
  | .app f x =>
      acc := acc ++ (← collectMatches f)
      acc := acc ++ (← collectMatches x)
  | .lam _ ty bd _ =>
      acc := acc ++ (← collectMatches ty)
      acc := acc ++ (← collectMatches bd)
  | .forallE _ ty bd _ =>
      acc := acc ++ (← collectMatches ty)
      acc := acc ++ (← collectMatches bd)
  | .letE _ ty val bd _ =>
      acc := acc ++ (← collectMatches ty)
      acc := acc ++ (← collectMatches val)
      acc := acc ++ (← collectMatches bd)
  | .mdata _ b =>
      acc := acc ++ (← collectMatches b)
  | .proj _ _ b =>
      acc := acc ++ (← collectMatches b)
  | _ =>
      --logInfo m!"{<- inferType e}"
      pure ()

  return acc


/-- Collect all `(width, x)` pairs from the goal type and all local hypotheses
    (both their types and, if present, their values). -/
def collectFromContext : TacticM (Array (Nat × Expr × Expr)) := do
  let goal ← getMainGoal
  let goalTy ← goal.getType
  goal.withContext do
    let mut out : Array (Nat × Expr × Expr) := #[]
    --logInfo m!"Starting {goalTy}"
    out := out ++ (← collectMatches (goalTy))
    --logInfo m!"GOT {out}"
    let lctx ← getLCtx
    --logInfo "=== RAW HYP TYPES ==="
    for decl in lctx do


      if decl.isImplementationDetail then
        continue

      --logInfo m!"Starting {decl.userName}: {← ppExpr decl.type}"
      -- collect from hypothesis type
      let e <- instantiateMVars decl.type
      let e ← whnf e
      out := out ++ (← collectMatches e)
      --logInfo m!"Gor {out}"
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

def lookupGroup (fid : Name) (gs : List (Name × Expr × List Nat))
  : Option (Expr × List Nat) :=
  match gs.find? (fun (p : Name × Expr × List Nat) => p.fst == fid) with
  | some (_, ws) => some ws
  | none => none



def insertGroup (fid : Name) (e:Expr) (w : Nat)
    (gs : List (Name × Expr × List Nat))
    : List (Name × Expr × List Nat) :=
  let rec go (acc : List (Name × Expr ×  List Nat)) (rest : List (Name × Expr ×  List Nat)) :=
    match rest with
    | [] => (fid, e, [w]) :: acc
    | (fid', x, ws) :: tl =>
      if fid' == fid then
        (fid', x, w :: ws) :: acc ++ tl
      else
        go ((fid',x, ws) :: acc) tl
  go [] gs

syntax "autoCastBits" "[" ident,* "]" : tactic

elab_rules : tactic
| `(tactic| autoCastBits [$ids,*]) => do
    --let names := ids.map (·.getId)
    --logInfo m!"Parsed names: {names}"
    -- your real logic here
  --logInfo "=== autoCastBits: starting ==="
  let hyps := (ids.getElems.map (·.getId)).toList
  let pairsArr ← collectFromContext
  let pairs := pairsArr.toList
  --logInfo m!"Detected pairs (width, expr): {pairs}"

  -- Group widths by underlying variable, keyed by FVarId
  let mut groups : List (Name  × Expr × List Nat) := []
  let mut modulus : Option Expr := none
  for (w, x, f) in pairs do
    modulus := some f
    let myName := (<- collectTerms x).toList[0]!
    --let fid := (<- collectTerms x).toList[0]!
   -- if let some fid := x.fvarId? then
      match lookupGroup myName groups with
      | some ws =>
          groups := insertGroup myName x w groups
      | none =>
          groups := (myName, x, [w]) :: groups
  --logInfo "=== Groups after aggregation ==="
  -- for (fid, ws) in groups do
  --  logInfo m!"{fid.name}: widths = {ws}"

  let some modExpr := modulus
    | throwError "[autoCastBits] no modulus found"
  let lctx ← getLCtx
  let mut goal ← getMainGoal

  -- For each variable that appears with multiple distinct widths, create a lemma
  for (fid, x, ws) in groups do

    let uniq := ws.eraseDups
    --if uniq.length > 1 then
      --let minW := uniq.foldl Nat.min uniq.head!
    let maxW := uniq.foldl Nat.max uniq.head!

        -- reconstruct the variable and get a nicer name
      --let x := Expr.fvar fid
    --logInfo m!"{x}, {ws}"
          -- match lctx.find? fid with
          -- | none =>
          --     pure ()
          -- | some decl => do
    let baseName := fid
    for w in ws do
       if w != maxW then
                  let lemmaName := baseName.appendAfter s!"_cast_{w}"

                  let zmodValBase := mkConst ``_root_.ZMod.val
                  let zmodValTyped := mkApp zmodValBase modExpr
                  let valExpr := mkApp zmodValTyped x

                  -- lhs : BitVec.ofNat minW (ZMod.val x)
                  --logInfo m!"x = {← ppExpr x}"
                  let lhs :=
                    mkAppN (mkConst ``BitVec.ofNat) #[mkNatLit w, valExpr]

                  let bigVec :=
                    mkAppN (mkConst ``BitVec.ofNat)
                      #[ mkNatLit maxW, valExpr ]

                  let rhs :=
                    mkAppN (mkConst ``BitVec.setWidth)
                      #[ mkNatLit maxW, mkNatLit w, bigVec ]


                  let eq <- mkEq lhs rhs
                  --logInfo m!"Adding lemma {eq} for {baseName}: minW={minW}, maxW={maxW}"

                  -- Build the proof by `simp`
                  let pf ← elabTerm (← `(by simp)) eq
                  --let mut goal2 <- getMainGoal
                  --goal ← getMainGoal
                  let newGoal ← goal.assert lemmaName eq pf
                  goal := newGoal


              replaceMainGoal [goal]
              -- HARD CODED FIX
     let bitsStx : TSyntax `term := Syntax.mkNumLit (toString maxW)
    if maxW > 250 then

                let hname := Name.mkSimple s!"h_val_{baseName}"
                let hident : TSyntax `ident := mkIdent hname
                let xStx ← Term.exprToSyntax x
                let tac ← `(tactic|
                have $hident :=
                    ZMod.val_le_BV $xStx $bitsStx (h := by try decide)
                )
                try
                  evalTactic tac
                catch _ => pure ()
    let g <- getMainGoal
    g.withContext do
      let lctx ← getLCtx

      for c in hyps do
        try
          -- ✅ resolve the Name `c` to a real local hypothesis
          let some decl := lctx.findFromUserName? c
            | throwError m!"❌ Cannot find hypothesis {c}"

          let hIdent := Lean.mkIdent decl.userName

          -- ✅ specialize hIdent with a TERM
          evalTactic (← `(tactic| specialize $hIdent $bitsStx (by decide)))

          -- ✅ simp at that hypothesis
        -- evalTactic (← `(tactic| simp at $(mkIdent c):ident))

        catch e =>
          pure ()
          --logInfo m!"{e.toMessageData}"

    goal ← getMainGoal


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
            -- else
            --    let lhsArgs := lhs.getAppArgs
            --    if lhsArgs.size > 5 then
            --     if lhsArgs[5]!.isAppOf ``BitVec.toNat then
                        -- logInfo m!"{lhs}"
                        --return some cond
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
| `(tactic| translate_hypothesis $h:ident [$ids,*] $[$b:term]? ) => withMainContext do
  /- Build simpArg array (empty if none provided) -/
  let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
  for i in ids.getElems do
      let sa ← `(simpArg| $i:term)
      let ua : TSyntax [`Lean.Parser.Tactic.simpStar,
                        `Lean.Parser.Tactic.simpErase,
                        `Lean.Parser.Tactic.simpLemma] := ⟨sa.raw⟩
      sargs := sargs.push ua
  let hName := h.getId   -- the Name of the identifier
  let flag ←
    match b with
    | some bterm =>
        pure true
    | none => pure false
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
  subLoop := true
  while (subLoop) do
    try
      evalTactic (← `(tactic|  rw [neg_param] at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop := false
  let i ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    countMinusOps2 decl.type
   let k ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    let ty ← instantiateMVars decl.type
    let ty ← whnfR ty
    --logInfo m!"{ty}"
    pure (countAnds decl.type + countOrs ty)
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
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  for _ in [0:k] do

      evalTactic (← `(tactic| try rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
      evalTactic (← `(tactic| try valify [$[$sargs],*]   at $(mkIdent h.getId):ident))
  let mut progress:= true
  while(progress ) do
      try
        evalTactic (← `(tactic| rw [ZMod.val_sub]  at $(mkIdent h.getId):ident) )
        let cur_g ← getGoals
        match cur_g.reverse with
        | [] => throwError "No goals after reorder"
        | _ :: [] => throwError "wrong number of goals"
        | last :: init => do
            --logInfo m!"CUR GOALS: {cur_g}"
            -- let last := cur_g.getLast!
            -- let init := cur_g.dropLast
            -- focus only the last goal
            setGoals [last]
            evalTactic (← `(tactic| try_apply_lemma_hyps []))
            let after ← getGoals
            logInfo m!"CUR GOALS: {after}"
            if after.isEmpty then
              setGoals (init.reverse)
              evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))
               --evalTactic (← `(tactic| try valify [$[$sargs],*]
            else
              throwError "lemma application did not solve goal"

      catch _ =>
        try
          evalTactic (← `(tactic| rw [ZMod.val_sub_strict]  at $(mkIdent h.getId):ident))
          evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))
        catch _ =>
          progress := false
    evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))

  evalTactic (← `(tactic| try simp at $(mkIdent h.getId):ident) )
  subLoop := true
  while (subLoop ) do
    try
      evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
      evalTactic (← `(tactic| try valify [$[$sargs],*]   at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop  := false
  let m ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    CalcBitWidth decl.type ids
  let bitsize := ceilLog2 (Nat.max m 4)
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  --logInfo m!"{bitsize}"
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_leq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))
  for _ in [:k] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))
  for _ in [:i] do
      evalTactic (← `(tactic| try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  subLoop := true
    while (subLoop ) do
      try
        evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident) )
        let cur_g ← getGoals
        match cur_g with
        | [] =>
            throwError "❌ No goals after Nat.mod_eq_of_lt"
        | _ :: []  =>
            throwError "❌ wrong number of goals left after Nat.mod_eq_of_lt"
        | _ => do
            let last := cur_g.getLast!
            let init := cur_g.dropLast
            -- focus only the last goal
            setGoals [last]
            evalTactic (← `(tactic| try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ( init)
              evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
            else
              throwError m! "try_apply failed {after}"
      catch _ =>
        try
          evalTactic (← `(tactic| rw [BitVec.ofNat_mod_move] at $(mkIdent h.getId):ident) )
          evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
        catch _ =>
          try
            evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident) )
            evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
          catch _ =>
            subLoop := false
  evalTactic (← `(tactic| try simp  at $(mkIdent h.getId):ident))


syntax (name := translateGoal)
  "translate_goal" ppSpace ("[" ident,* "]")? (ppSpace term)? : tactic


partial def loopUntilDone (flag: Bool) (hs : Array (TSyntax `ident)) : TacticM Unit := do
  let g ← getMainGoal
  let t ← g.getType
  let t2 <- instantiateMVars t
  let flagStx ←
  if flag then
    `(true)
  else
    `(false)
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
      evalTactic (← `(tactic| translate_hypothesis hc [$hs,*] $flagStx ))

      -- -- Simplify the goal using this new equality
      evalTactic (← `(tactic| all_goals try simp [hc]))

      -- -- Recurse on updated goal
      loopUntilDone flag hs

@[tactic translateGoal]
elab_rules : tactic
| `(tactic| translate_goal [$ids,*] $[$b:term]? ) => withMainContext do
  /- Build simpArg array (empty if none provided) -/
  let mut sargs :
    Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                    `Lean.Parser.Tactic.simpErase,
                    `Lean.Parser.Tactic.simpLemma]) := #[]
  for i in ids.getElems do
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
  let flag ←
    match b with
    | some bterm =>
        pure true
    | none => pure false
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
  subLoop := true
  while (subLoop) do
    try
      evalTactic (← `(tactic| rw [neg_param]))
    catch _ =>
      subLoop := false
  let mut mLoop := true
  while (mLoop) do
    try
     evalTactic (← `(tactic| rw [sub_add_right_recursive]))
    catch _ =>
      mLoop := false
  let mut g ← getMainGoal
  let mut t ← g.getType
  -- if isExists t then
  --      evalTactic (← `(tactic| refine ?_))
  let i  ←  countMinusOps2 t
  let k := countOrs t + countAnds t
  --logInfo m! "MINUSUS {i} for {t}"

  --TO DO THIS SHOULD BE A TRY CATCH LOOP!
 -- if i > 0 then
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
  let mut progress:= true
  let mut count := 0
  while(progress ) do
      count := count + 1
      try
        evalTactic (← `(tactic| rw [ZMod.val_sub]))
        let cur_g ← getGoals
        match cur_g with
        | [] => throwError "No goals after reorder"
        | _ :: [] => throwError "wrong number of goals"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            logInfo m!"{g_last}"
            evalTactic (← `(tactic| try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ([g_one] ++ rest_rev)
              evalTactic (← `(tactic| try valify [$[$sargs],*]))
            else
              throwError "lemma application did not solve goal"

      catch _ =>
        try
          evalTactic (← `(tactic| rw [ZMod.val_sub_strict]))
          evalTactic (← `(tactic| try valify [$[$sargs],*]))
        catch _ => progress := false
     -- evalTactic (← `(tactic| try valify [$[$sargs],*]))

  --l--ogInfo m! "HERE?"
  evalTactic (← `(tactic| try simp ) )

  let goals <- getGoals
  if goals.isEmpty then
    logInfo m!"SOLVED"
    return
  -- --- FOR DEBUGGING REMOVE LATER PLEASE
  loopUntilDone flag ids

  -- let goals <- getGoals
  -- if goals.isEmpty then
  --   return
  --logInfo m! "HERE?!"
  let m <- CalcBitWidth (<-goals[0]!.getType) ids
  let bitsize := ceilLog2 (Nat.max m 4)
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  logInfo m!"BIT SIZE {bitsize} with {m}"
  --  --loopUntilDone flag
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  --let n := countAnds t + k
  --logInfo m!"ORS"
  for _ in [:k] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  if i > 0 then
    for _ in [:i] do
      evalTactic (← `(tactic| try rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*] ) )
  let mut modLeft := true
  subLoop := true
  while (subLoop ) do
      count :=count + 1
      try
        evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
        let cur_g ← getGoals
        match cur_g with
        | [] =>
            throwError "❌ No goals after Nat.mod_eq_of_lt"
        | _ :: []  =>
            throwError "❌ wrong number of goals left after Nat.mod_eq_of_lt"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            evalTactic (← `(tactic| try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ( [g_one ] ++ rest_rev )
              evalTactic (← `(tactic| try bvify [$[$sargs],*]))

            else
              throwError m! "try_apply failed {after}"
      catch e =>
        try
          evalTactic (← `(tactic| rw [BitVec.ofNat_mod_move]))
          evalTactic (← `(tactic| try bvify [$[$sargs],*]))
        catch _ =>
           try
             evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
             evalTactic (← `(tactic| try bvify [$[$sargs],*]))
            catch _ =>
              subLoop := false
    evalTactic (← `(tactic| try simp ) )







  -- loopUntilDone flag

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


def addZModValBounds (bits : Nat) : TacticM (Array (TSyntax `ident)) := do
  let lctx ← getLCtx
  let bitsStx : TSyntax `term := Syntax.mkNumLit (toString bits)

  let mut out : Array (TSyntax `ident) := #[]

  for decl in lctx do

    if decl.isImplementationDetail || decl.isAuxDecl then
      continue

    let ty ← whnf decl.type
    let fn := ty.getAppFn
    let args := ty.getAppArgs
    --logInfo m!"{fn} for {ty}"
    match fn with
    | Expr.const ``Fin _ =>
        -- Declare hypothesis name
        let uname := decl.userName
        let hname := Name.mkSimple s!"h_val_{uname}"
        let hident : TSyntax `ident := mkIdent hname
        let xStx ← Term.exprToSyntax decl.toExpr

        -- Generate lemma:
        let tac ← `(tactic|
          have $hident :=
            ZMod.val_le_BV $xStx $bitsStx (h := by decide)
        )
        evalTactic tac
        --evalTactic (← `( tactic| try simp at $(mkIdent hident.getId):ident))

        out := out.push hident

    | _ => pure ()

  return out


def smartTranslateOne
    (h : TSyntax `ident)
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma]))
                        (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident))): TacticM ( Option (TSyntax `ident) × Option (TSyntax `ident ) × Option (TSyntax `ident)) := do
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
        return (some h1, some h2, none)
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
                  return (some newName ,none, some h)
              catch _ => pure ()
          | _ => --pure ()
          try
            evalTactic (← `(tactic| rw [BVModEq.extract_bv_rel] at $(mkIdent h.getId):ident))
            -- evalTactic (← `(tactic|  rw [BVModEq.map_f_to_bv] at $(mkIdent h.getId):ident))
            let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
            let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
            --evalTactic (← `(tactic| simp at $(mkIdent h.getId):ident))
            evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $h2⟩))
            return (some h1, some h2, none)
          catch _ =>
            try
              evalTactic (← `(tactic| rw [BVModEq.map_f_to_bv] at $(mkIdent h.getId):ident))
              evalTactic (← `(tactic| simp at $(mkIdent h.getId):ident))
              let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
              let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
              evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $(mkIdent h.getId):ident⟩))
              evalTactic (← `(tactic| apply Nat.le_of_lt_succ  at $h1))
              evalTactic (← `(tactic| rw [duplicate_leq] at $h1:ident))
              let newName := mkIdent (Name.mkSimple s!"{h.getId}_new")

              evalTactic (← `(tactic|
                  rcases $h1:ident with ⟨$h1:ident, $newName⟩))
              evalTactic (← `(tactic| rw [BVModEq.extract_bv_leq] at $h1:ident))

              return (some newName, some h1, none)
            catch e =>
                pure ()
                --logInfo m!"{e.toMessageData}"


       return (none, none, some h)


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
    (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident)))
    (flag: Bool)
    : TacticM (Array (TSyntax `ident) × Array (TSyntax `ident)  )
    := do
  let mut picked : Array (TSyntax `ident) := #[]
  let mut translate : Array (TSyntax `ident) := #[]
  let mut changed : Array (TSyntax `ident) := #[]
  let flagStx ←
  if flag then
    `(true)
  else
    `(false)
  for h in hs do

   let (k?, x?, w?) ← smartTranslateOne h extraArgs varToHypRef

-- If we got a k, push it
    match k? with
    | some k => picked := picked.push k
    | none   => pure ()

    match x? with
    | some x => changed := changed.push x
    | none   => pure ()


    -- If we got a w, translate the hypothesis
    match w? with
    | some w =>translate := translate.push h
    | none => pure ()
  for h in translate do
    evalTactic (← `(tactic| translate_hypothesis $h [$[$picked],*] $flagStx ))

  return (picked,changed)

/-- One-shot orchestrator:
    intro h; split; smart-translate; translate_goal; bv_decide; try_apply_lemma_hyps [*_1 ...] -/
syntax (name := translateAll) "translate_all" ppSpace
  ("[" ident,* "]")?  (ppSpace term)? : tactic

@[tactic translateAll]
elab_rules : tactic
| `(tactic| translate_all $[[ $extraSimp,* ]]? $[$b:term]? ) => withMainContext do
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
  let flag ←
    match b with
    | some bterm =>
        pure true
    | none => pure false
  -- evalTactic (← `(tactic| try simp))
  -- let gs ← getGoals
  -- if gs.isEmpty then
  --   logInfo "✅ No goals left!"
  --   return

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
  let (collected, changed) := (← smartTranslateMany ids sargs varToHypRef flag)

  let mut after ← getGoals
  if after.isEmpty then
    return
  let flagStx ←
  if flag then
    `(true)
  else
    `(false)
  evalTactic (← `(tactic| translate_goal [$[$collected],*] $flagStx ))
  evalTactic (← `(tactic| try simp ))
  let flag ←
    match b with
    | some bterm =>
        pure true
    | none => pure false
  after ← getGoals
  if after.isEmpty then
    return

  try
     evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
  catch _ =>
    --evalTactic (← `(tactic| autoCastBits))
    --let hs <- addZModValBounds 256
   -- logInfo m!"{changed}"
    evalTactic (← `(tactic| autoCastBits [$[$changed],*]))
    let mut rw := true
    while (rw) do
      try
          evalTactic (← `(tactic| intro h))
          evalTactic (← `(tactic| try rw [h]))
          for hyp in ids ++ changed  do
            evalTactic (← `(tactic| try rw [h] at $(mkIdent hyp.getId):ident))
          evalTactic (← `(tactic| clear h))
           -- evalTactic (← `(tactic| try simp only [BitVec.setWidth] at $(mkIdent hyp.getId):ident))
      catch _ =>
        rw := false
    --try
      evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
    -- catch _ =>
    --   rw := false
    --   pure ()
      -- THIS IS NEEDED FOR JOLT BUT NOT CIRC WE SHOULD FIND A WAY TO ABSTRACT THIS
    --   let mut index :=0
    --   let fv1T : TSyntax `term := (← termFor `fv1)
    --   let fv2T : TSyntax `term := (← termFor `fv2)
    --   while index < collected.size/2 do

    --     -- names for the bound and its equality
    --     let idName  := Name.mkSimple s!"b0_{index}"

    --     -- identifiers/syntax nodes
    --     let idSyn   : TSyntax `ident := mkIdent idName
    --     let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    --     -- safest access: .get! (parses reliably inside quotations)
    --     evalTactic (← `(tactic|
    --       set $idSyn := $fv1T[$idxSyn]
    --     ))
    --     index := index + 1
    --   index := 0
    --   while index < collected.size/2 do
    --     -- names for the bound and its equality
    --     let idName  := Name.mkSimple s!"b1_{index}"

    --     -- identifiers/syntax nodes
    --     let idSyn   : TSyntax `ident := mkIdent idName
    --     let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    --     -- safest access: .get! (parses reliably inside quotations)
    --     evalTactic (← `(tactic|
    --       set $idSyn := $fv2T[$idxSyn]
    --     ))
    --     index := index + 1
    --evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))

  -- -- -- -- --logInfo m! "Collected {collected}"
  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
  after ← getGoals

  if !after.isEmpty then
    while (!after.isEmpty) do
  -- record the current state
      let before ← getGoals

  -- run your tactics
      evalTactic (← `(tactic| translate_goal [$[$collected],*] $flagStx))
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


 --sorry
 --try_apply_lemma_hyps [h0_1_1,h0_2_1]

 --bv_decide




--  translate_all [] false
--  bv_decide


-- (a.toNat + 2) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 +
--       52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--     b.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513 <
--   52435875175126190479447740508185965837690552500527637822603658699938581184513





-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 4)
-- variable (a : BitVec 4)
-- variable (fresh_pf4_cmp_bit4 : FF0)
-- variable (fresh_pf3_cmp_bit3 : FF0)
-- variable (fresh_pf2_cmp_bit2 : FF0)
-- variable (fresh_pf1_cmp_bit1 : FF0)
-- variable (fresh_pf0_cmp_bit0 : FF0)
-- lemma correct :
-- ((((((((fresh_pf0_cmp_bit0) * (fresh_pf0_cmp_bit0))) = (fresh_pf0_cmp_bit0))) ∧ (((((fresh_pf1_cmp_bit1) * (fresh_pf1_cmp_bit1))) = (fresh_pf1_cmp_bit1))) ∧ (((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2))) ∧ (((((fresh_pf3_cmp_bit3) * (fresh_pf3_cmp_bit3))) = (fresh_pf3_cmp_bit3))) ∧ (((((fresh_pf4_cmp_bit4) * (fresh_pf4_cmp_bit4))) = (fresh_pf4_cmp_bit4))) ∧ ((((fresh_pf0_cmp_bit0) + (((fresh_pf1_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_cmp_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf3_cmp_bit3) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf4_cmp_bit4) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)) + (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) → (((((((fresh_pf4_cmp_bit4) * (fresh_pf4_cmp_bit4))) = (fresh_pf4_cmp_bit4))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (fresh_pf4_cmp_bit4))) = (BitVec.ult a b)))))))
--  := by
-- translate_all [] false
-- -- unfold map_bv_to_f
-- simp
-- intro h1 h2 h3 h4 h5 h7

-- translate_hypothesis h7 [] false
--  unfold map_bv_to_f
--  simp
--  intro h1 h2 h3 h4 h5 h7
--  simp only [ZMod.eq_if_val] at h7
--  rw [<- sub_eq_add_neg] at h7
--  rw [sub_add_right_recursive] at h7
--  valify at h7
--  rw [ZMod.val_sub] at h7
--  swap
--  focus try_apply_lemma_hyps []

 --translate_all [] false
--  split_ands
--  bv_decide
--  --bv_normalize
--  bv_decide
--  try_apply_lemma_hyps [h0_1,h1_1, h2_1, h3_1, h4_1]



--set_option maxRecDepth 200000000
-- lemma  neg_param (x y z : ZMod p) :
--   x + (-y -z) = (x - y) -z := by
--   ring_nf

--abbrev ff := 52435875175126190479447740508185965837690552500527637822603658699938581184513


-- instance : ZKField (ZMod ff) where
--   hash x :=
--     match x.val with
--     | 0 => 0
--     | n + 1 => hash n

--   field_to_bits {num_bits: Nat} f :=
--     let bv : BitVec 64 := BitVec.ofFin ⟨f.val, Nat.lt_trans (ZMod.val_lt f) (by decide : ff < 2 ^ 64)⟩
--     -- TODO: Double check the endianess.
--     Vector.map (fun i =>
--       if _:i < 3 then
--         if bv[i] then 1 else 0
--       else
--         0
--     ) (Vector.range num_bits)
--   field_to_nat f := f.val


-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ff) := by sorry
-- variable (b : BitVec 2)
-- variable (a : BitVec 2)
-- variable (fresh_pf2_cmp_bit2 : FF0)
-- variable (fresh_pf1_cmp_bit1 : FF0)
-- variable (fresh_pf0_cmp_bit0 : FF0)
-- -- lemma correct :
-- -- (((((((((((fresh_pf0_cmp_bit0) * (fresh_pf0_cmp_bit0))) = (fresh_pf0_cmp_bit0))) ∧ (((((fresh_pf1_cmp_bit1) * (fresh_pf1_cmp_bit1))) = (fresh_pf1_cmp_bit1)))) ∧ (((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2)))) ∧ ((((((fresh_pf0_cmp_bit0) + (((fresh_pf1_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((fresh_pf2_cmp_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (- (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) → (((((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (fresh_pf2_cmp_bit2))) = (BitVec.ult a b)))))))
-- --  := by
-- --  translate_all [] false

-- instance : Witnessable (ZMod ff) (ZMod ff) := by sorry

-- instance NotTwo: BVModEq.GtTwo (ff) := by
--   have hlt: 2 < ff := by decide
--   sorry

-- #check (inferInstance : SubNegMonoid (ZMod ff))

-- instance IsThisTrue: SubNegMonoid (ZMod ff) :=
--   inferInstance

-- example (x y: FF0) (h1: x.val ≤ 1) (h2: x.val ≤ 2) : (x.val + y.val - x.val * y.val >= 0 ) := by
--  ring_nf

-- def OR_16  : Subtable FF0 16 :=
--   subtableFromMLE (fun x => 0 + ((1*((x[7] + x[15] - x[7]*x[15])))) + 2*(x[6] + x[14] - x[6]*x[14]) + 4*(x[5] + x[13] - x[5]*x[13]) + 8*(x[4] + x[12] - x[4]*x[12]) + 16*(x[3] + x[11] - x[3]*x[11]) + 32*(x[2] + x[10] - x[2]*x[10]) + 64*(x[1] + x[9] - x[1]*x[9]) + 128*(x[0] + x[8] - x[0]*x[8]))

-- -- #check FF0

-- lemma or_mle_one_chunk(bv1 bv2 : BitVec 8) (fv1 fv2 : Vector FF0 8) :
--   some bvoutput = BVModEq.map_f_to_bv 8 foutput ->
--    some (BVModEq.bool_to_bv 8 bv1[7])  = BVModEq.map_f_to_bv 8 fv1[0]  ->
--    some (BVModEq.bool_to_bv 8 bv1[6]) = BVModEq.map_f_to_bv 8 fv1[1]  ->
--    some (BVModEq.bool_to_bv 8 bv1[5]) = BVModEq.map_f_to_bv 8 fv1[2]  ->
--    some (BVModEq.bool_to_bv 8 bv1[4]) = BVModEq.map_f_to_bv 8 fv1[3]  ->
--    some (BVModEq.bool_to_bv 8 bv1[3]) = BVModEq.map_f_to_bv 8 fv1[4]  ->
--   some (BVModEq.bool_to_bv 8 bv1[2]) = BVModEq.map_f_to_bv 8 fv1[5]  ->
--    some (BVModEq.bool_to_bv 8 bv1[1]) =BVModEq.map_f_to_bv 8 fv1[6]  ->
--    some (BVModEq.bool_to_bv 8  bv1[0]) = BVModEq.map_f_to_bv 8 fv1[7]  ->
--   some (BVModEq.bool_to_bv 8 bv2[7]) = BVModEq.map_f_to_bv 8 fv2[0]  ->
--   some (BVModEq.bool_to_bv 8 bv2[6]) = BVModEq.map_f_to_bv 8 fv2[1]  ->
--   some (BVModEq.bool_to_bv 8 bv2[5]) = BVModEq.map_f_to_bv 8 fv2[2]  ->
--   some (BVModEq.bool_to_bv 8 bv2[4]) = BVModEq.map_f_to_bv 8 fv2[3]  ->
--   some (BVModEq.bool_to_bv 8 bv2[3]) = BVModEq.map_f_to_bv 8 fv2[4]  ->
--   some (BVModEq.bool_to_bv 8 bv2[2]) = BVModEq.map_f_to_bv 8 fv2[5]  ->
--   some (BVModEq.bool_to_bv 8 bv2[1]) = BVModEq.map_f_to_bv 8 fv2[6]  ->
--   some (BVModEq.bool_to_bv 8 bv2[0]) = BVModEq.map_f_to_bv 8 fv2[7]  ->
--   (bvoutput = (BitVec.or bv1  bv2 ))
--   =
--   (foutput = evalSubtable OR_16 (Vector.append fv1 fv2))
--  := by
--   unfold OR_16
--   unfold evalSubtable
--   unfold subtableFromMLE
--   unfold Vector.append
--   --have h:  foutput.val < 256 := by sorry

--   translate_all false
--   sorry
--   simp
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   rw [Nat.mod_eq_of_lt]
--   --ring_nf
--   ring_nf
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega
--   omega






  --bv_decide
  --have h : ∀ x : Nat, x < 2 → 2* foutput.val = 0#2 := by sorry


  -- sorry
  --try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1,h5_1, h6_1,h7_1, h8_1,h9_1,h10_1,h11_1, h12_1, h13_1, h14_1,h15_1,h16_1]



  --rw [BVModEq.map_f_to_bv] at h0


  --simp
  ---translate_all [] false
  -- rw [ZMod.val_sub]
  -- sorry

  -- -- sorry
  -- try_apply_lemma_hyps [ h16_1, h8_1]
  -- try_apply_lemma_hyps [h0_1, h1_1,h2_1,h3_1,h4_1,h5_1,h6_1,h7_1,h8_1,h9_1]
  -- -- rw [ZMod.val_sub]


--  sorry
--  try_apply_lemma_hyps [h0_1]
--  unfold OR_16
--  unfold evalSubtable
--  unfold subtableFromMLE
--  unfold Vector.append
--  simp
--  intro h1 h2 h3 h4 h5 h6 h7 h9 h8 h10 h11 h12 h13 h14 h15 h16 h17
--  translate_hypothesis h1 [] false

--  translate_goal []
-- --  intro h
--  unfold map_f_to_bv at h
--  simp at h
--  rcases h with ⟨h1, h2⟩
--  intro h3
--  unfold bool_to_bv at h3
--  unfold map_f_to_bv at h3
--  simp at h3
--  rcases h3 with ⟨h4, h5⟩

--  unfold OR_16
--  unfold evalSubtable
--  unfold subtableFromMLE
--  unfold Vector.append
--  simp
--  translate_all

-- BAD OVERFLOW

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 2)
-- variable (a : BitVec 2)
-- variable (fresh_pf2_cmp_bit2 : FF0)
-- variable (fresh_pf1_cmp_bit1 : FF0)
-- variable (fresh_pf0_cmp_bit0 : FF0)
-- lemma correct :
-- (((((((((((fresh_pf0_cmp_bit0) * (fresh_pf0_cmp_bit0))) = (fresh_pf0_cmp_bit0))) ∧ (((((fresh_pf1_cmp_bit1) * (fresh_pf1_cmp_bit1))) = (fresh_pf1_cmp_bit1)))) ∧ (((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2)))) ∧ ((((((fresh_pf0_cmp_bit0) + (((fresh_pf1_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((fresh_pf2_cmp_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (- (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) → (((((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (fresh_pf2_cmp_bit2))) = (BitVec.ult a b)))))))
--  := by
--  translate_all [] false

--  bv_decide

 --try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]
--  focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]

 --focus try_apply_lemma_hyps [h0_1,h1_1, h2_1]














-- NOT FIXED
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 4)
-- variable (a : BitVec 4)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (! (((((((((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (! (((((((((if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))))) = (((- (if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (if (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (((a) = (b)))))))))))))
--  := by
-- translate_goal [] false
-- rw [BVModEq.BitVec_ofNat_eq_iff 510 ]





-- abbrev f := 7

-- lemma BitVec.ofNat_Sub_Strict   [h: NeZero 7]
--     {x y : ZMod 7} (h: x.val + 7 - y.val < 2^256 ) :  BitVec.ofNat 256 ( (x.val + 7 - y.val ) % 7 ) =
-- (BitVec.ofNat 256 ( x.val) + BitVec.ofNat 256 (7) - BitVec.ofNat 256 (y.val ) ) % BitVec.ofNat 256 (f ) := by
--   rw [BitVec.ofNat_mod_move]
--   rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
--   bvify
--   try_apply_lemma_hyps []

-- BIG PROBLEM AAAAA
-- ZMod.val fresh_pf1_is_zero * (a.toNat + 52435875175126190479447740508185965837690552500527637822603658699938581184449) +
--     (52435875175126190479447740508185965837690552500527637822603658699938581184577 -
--       a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513)



-- #eval (ceilLog2 7)
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance Notwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 1)
-- variable (a : BitVec 1)
-- lemma correct :
-- ((((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ ((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 3  ((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (BitVec.ult a b)))))))
--  := by
--   translate_all false
--   bv_decide
--   try_apply_lemma_hyps []

--   --bv_decide


--  try simp
--  bv_decide
--  try_apply_lemma_hyps []



--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []

 --try_apply_lemma_hyps []
-- ((if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[0] = true then 1 else 0) +
--     if (BitVec.setWidth 2 b + 1#2 - BitVec.setWidth 2 a)[1] = true then 2 else 0) <
--   4
--  translate_goal [] false

--  try_apply_lemma_hyps []
--  translate_goal [] false
--  try_apply_lemma_hyps []
--  translate_goal [] false
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []

--  focus try_apply_lemma_hyps []











 --translate_goal [] false

 --translate_goal [] false


 --focus try_apply_lemma_hyps []



 --bv_decide










-- lemma correct_me :
--  fresh_pf1_is_zero.val * (a.toNat + 52435875175126190479447740508185965837690552500527637822603658699938581184449) +(64 - a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513) = 10 := by
--  translate_all [] false
-- --  := by
--  --have h3 := ZMod.val_le_BV fresh_pf1_is_zero 256 (h := by decide)
--  --have h4 := ZMod.val_le_BV fresh_pf0_is_zero_inv 256 (h := by decide)
--  translate_all [] false
--  try_apply_lemma_hyps []


-- lemma correct :
-- (((((((((fresh_pf0_is_zero_inv) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))) = (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf1_is_zero) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) → (((((((((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (32 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((fresh_pf1_is_zero) * (- (((- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (64 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (((- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (64 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))))
--  := by
--  --have h3 := ZMod.val_le_BV fresh_pf1_is_zero 510 (h := by decide)
--  --have h4 := ZMod.val_le_BV fresh_pf0_is_zero_inv 510 (h := by decide)
-- translate_all [] false

 --autoCastBits


--  intro h_1
--  intro h_2
--  rw [h_1] at h1
--  rw [h_1] at h3



--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []



--  focus try_apply_lemma_hyps []


-- TODOS (TOODAY!!!)
--1) INTRO THE HYPOTHESIS
--2) CALCULATE BITWIDTH


--  have h3 := ZMod.val_le_BV fresh_pf1_is_zero 256 (h := by decide)
--  have h4 := ZMod.val_le_BV fresh_pf0_is_zero_inv 256 (h := by decide)
--  sorry
--  --cide
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  decide
 --focus try_apply_lemma_hyps []
 --translate_hypothesis h3 [] false



 --rw [ZMod.val_sub] at h0
 --valify [] at h1
 --valify at h1


 --bv_decide
--  translate_hypothesis h0 [] false
--  translate_hypothesis h1 [] false

--  translate_goal [] false
--  rw [ZMod.val_sub_strict]

--  --valify at h
--  --bv_decide
--  rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub]


 --rw [ZMod.val_sub]

 --translate_goal [] false
--  simp
--  rw [neg_add_to_sub]
--  try rw [<- sub_eq_add_neg]
--  try rw [sub_add_right_recursive]
--  rw [ZMod.val_sub ]
--  rw [ZMod.val_sub_strict ]
--  valify
--  simp
 --simp




-- -- OVERFLOW INSTANCE
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
-- -- (((((if (((BVModEq.bool_to_bv 1 (if a then b else c)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (if a then b else c)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))) + (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : BitVec 2)
-- variable (b : BitVec 2)
-- variable (x : FF0)
-- variable (a : Bool)
-- lemma correct :
--  (((((if (((BVModEq.bool_to_bv 1 (if a then b else c)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (if a then b else c)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))) + (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  c)))))
--  := by
--  unfold map_bv_to_f
--  translate_goal []
 --translate_all


--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  sorry
--  unfold map_bv_to_f
--  translate_goal [] strict
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
--  rw [BitVec.ofNat_mod_move]
--  bvify
--  rw [BitVec.ofNat_mod_move]
--  bvify
--  bv_decide

 --bvify
 --rw [Nat.mod_eq_of_lt]
--  rw [BitVec.ofNat_mod_move]
-- --  bvify
-- --  rw [BitVec.ofNat_mod_move]
-- --  bvify
-- --  rw [BitVec.ofNat_mod_move]
--  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub]
--  bvify
--  rw [Nat.mod_eq_of_lt]
--  rw [Nat.mod_eq_of_lt]
--  simp
--  bv_decide (config := {timeout := 300})
--  try_apply_lemma_hyps []

 -- TRADE OFF
 -- when to do
 -- rw [Nat.mod_eq_of_lt] v.s
 -- rw [BitVec.ofNat_mod_move]
 -- when to do



 --focus try_apply_lemma_hyps []

-- lemma help : BitVec.ofNat 256 (ZMod.val x) =
--   BitVec.ofNat 256
--     (b.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513 +
--             52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--           c.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513 +
--         c.toNat) % 52435875175126190479447740508185965837690552500527637822603658699938581184513 := by
--    rw [Nat.mod_eq_of_lt]



 --bv_decide
 --valify
--  sorry
--  --focus_

-- -- Options
-- -- def strict add n for all subtractions and don't remove mod aka always assume overflow
-- -- 1) strict translation out of scope
-- -- 2) up to user when to do strict translation
-- -- 3) first do weak then do strong
-- -- 4) try to prove that it is greater if it is not then do add n and continue
-- --

-- -- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- instance : Fact (Nat.Prime ffff0) := by sorry
-- -- instance : Fact (NeZero ffff0) := by sorry
-- -- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- -- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- variable (x_pf2_div_q_bit0 : FF0)
-- -- variable (b : BitVec 1)
-- -- variable (a : BitVec 1)
-- -- variable (fresh_pf7_cmp_bit1 : FF0)
-- -- variable (fresh_pf5_is_zero : FF0)
-- -- variable (fresh_pf1_div_r : FF0)
-- -- variable (fresh_pf6_cmp_bit0 : FF0)
-- -- variable (fresh_pf0_div_q : FF0)
-- -- variable (fresh_pf4_is_zero_inv : FF0)
-- -- variable (fresh_pf3_div_r_bit0 : FF0)



-- -- lemma correct :
-- -- ((((((((fresh_pf2_div_q_bit0) * (fresh_pf2_div_q_bit0))) = (fresh_pf2_div_q_bit0))) ∧ (((fresh_pf2_div_q_bit0) = (fresh_pf0_div_q))) ∧ (((((fresh_pf3_div_r_bit0) * (fresh_pf3_div_r_bit0))) = (fresh_pf3_div_r_bit0))) ∧ (((fresh_pf3_div_r_bit0) = (fresh_pf1_div_r))) ∧ (((((fresh_pf0_div_q) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b))) = (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) + (- fresh_pf1_div_r))))) ∧ (((((fresh_pf4_is_zero_inv) * (((fresh_pf0_div_q) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- fresh_pf5_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf5_is_zero) * (((fresh_pf0_div_q) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((fresh_pf6_cmp_bit0) * (fresh_pf6_cmp_bit0))) = (fresh_pf6_cmp_bit0))) ∧ (((((fresh_pf7_cmp_bit1) * (fresh_pf7_cmp_bit1))) = (fresh_pf7_cmp_bit1))) ∧ (((((fresh_pf6_cmp_bit0) + (((fresh_pf7_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((fresh_pf1_div_r) + (- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)) + (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((((- fresh_pf5_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (fresh_pf7_cmp_bit1))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) → (((if (((BVModEq.bool_to_bv 1 (BitVec.udiv a b)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf2_div_q_bit0)))))
-- --  := by
-- --   translate_all
--   ---rw [BVModEq.ZMod.eq_if_val]


--    -- (b + f - c) % f

--   --  translate_goal
--   --  bv_decide
--   --  focus try_apply_lemma_hyps []
--   --  sorry
--   --  focus try_apply_lemma_hyps []
--   --  focus try_apply_lemma_hyps []
--   -- focus try_apply_lemma_hyps []


-- -- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- instance : Fact (Nat.Prime ffff0) := by sorry
-- -- instance : Fact (NeZero ffff0) := by sorry
-- -- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- -- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- variable (d : Bool)
-- -- variable (c : Bool)
-- -- variable (b : Bool)
-- -- variable (a : Bool)
-- -- variable (fresh_pf1_is_zero : FF0)
-- -- variable (fresh_pf0_is_zero_inv : FF0)
-- -- lemma correct :
-- -- (((((((((fresh_pf0_is_zero_inv) * (((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if d then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) = (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((fresh_pf1_is_zero) * (((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (((- (if d then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) → (((((((((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (((- fresh_pf1_is_zero) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((a) ∧ (b)) ∧ (c)) ∧ (d)))))))))
-- --  := by
-- --  translate_all
-- --  --translate_goal

-- -- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- instance : Fact (Nat.Prime ffff0) := by sorry
-- -- instance : Fact (NeZero ffff0) := by sorry
-- -- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- -- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- -- variable (b : BitVec 7)
-- -- variable (a : BitVec 7)
-- -- lemma correct :
