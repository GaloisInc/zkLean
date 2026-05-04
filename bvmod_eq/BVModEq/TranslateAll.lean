/-
Translation tactics for BVModEq.

This file implements tactics that translate hypotheses and goals between
`ZMod`, `Nat`, and `BitVec` forms. The translation pipeline normalizes
arithmetic, pushes `.val` and `BitVec.ofNat` through expressions, applies
range analysis to discharge side conditions, and then rewrites into a form
that can be handled by bitvector reasoning.

This cleanup keeps the original tactic behavior intact while removing
scratch/debug comments and timing instrumentation.
-/

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
import BVModEq.Mappings

open Lean Meta Elab Tactic
open Lean.Parser.Tactic
open Std

namespace BVModEq


set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900
set_option linter.unusedVariables false

/-- Translate a named hypothesis into a bitvector-friendly form.

The optional identifier lists are forwarded to simplification and range-analysis
steps. The optional term is used as a flag for recursive translation of
composite `BitVec.ofNat` subterms. -/
syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")?  ("[" ident,* "]")? (ppSpace term)? : tactic

/-- Resolve a local name to term syntax when possible. -/
private def termFor (nm : Name) : TacticM (TSyntax `term) := withMainContext do
  match (← getLCtx).findFromUserName? nm with
  | some d => pure ⟨(mkIdent d.userName).raw⟩
  | none   => pure ⟨(mkIdent nm).raw⟩


/-- Conservatively estimate a natural bound used to choose a BitVec width. -/
partial def CalcBitWidth (e : Expr) (hs : Array (TSyntax `ident)) : MetaM Nat := do
  let e ← withReducible <| whnf e
  let fn  := e.getAppFn
  let args := e.getAppArgs
  /- Atomic expressions get widths from their type or literal value. -/
  if args.isEmpty then
    let ty ← inferType e >>= whnf
    match ty.getAppFnArgs with
    | (``BitVec , #[w]) =>
        match (← whnf w) with
          | (Expr.lit (Literal.natVal n)) =>
             return 2^n
          | _ =>  logInfo m!"BitVec width is not a numeral; falling back to recursive width analysis."
    | _ =>pure ()
  match e with
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
          | throwError m!"Could not find hypothesis `{hName}`"
        match decl.type.getAppFnArgs with
        | (``LE.le, #[_, _, lhs, rhs]) =>
          match (← whnf rhs) with
          | (Expr.lit (Literal.natVal n)) => do

              if  (<- collectTerms e).contains (<- collectTerms lhs).toList[0]!  then
                 return n
              else
                pure ()

          | _ =>  pure ()
        | _ =>  pure ()
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
          return (<- CalcBitWidth args[args.size-1]! hs)
        throwError "wrong # args BitVec.toNat"
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
    | ``Not =>
        return (<- CalcBitWidth args[args.size-1]! hs)
    | ``instOfNatNat =>
        return (<- CalcBitWidth args[args.size-1]! hs)
    | ``OfNat.ofNat =>
       return (<- CalcBitWidth args[args.size-2]! hs)
    | _ =>
      --logInfo m!"unsupported application head {name} with {args} and {args.size}"
      if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
      return 1
  | _ =>
     -- logInfo m!"unsupported op {fn} with {args}"
      if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
      return 1


/-- Small helper for choosing the smallest bit-width representing numbers below `n`. -/
def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    let lg := Nat.log2 (n - 1)
    lg + 1


/-- Detect `BitVec.ofNat k (ZMod.val x)`. -/
def matchOfNatVal? (e : Expr) : MetaM (Option (Nat × Expr × Expr)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs

  if fn.isConstOf ``BitVec.ofNat ∧ args.size = 2 then
    let kExpr := args[0]!
    let valExpr := args[1]!
    match kExpr.getAppFn with
    | Expr.const ``OfNat.ofNat _ =>
        match kExpr.getAppArgs with
        | #[_, numExpr, _inst] =>
            match numExpr with
            | Expr.lit (Literal.natVal k) =>
               let fn2 := valExpr.getAppFn
               let args1 := kExpr.getAppArgs
               let args2 := valExpr.getAppArgs

                if fn2.isConstOf ``ZMod.val ∧ args2.size = 2 ∧ args1.size=3 then
                  return some (k, args2[1]!, args2[0]!)
                if fn2.isConstOf ``GetElem ∧ args2.size = 2 ∧ args1.size=3 then
                   return some (k, args2[1]!, args2[0]!)
                else
                  return none
            | _ => return none

        | _ => return none
    | _ =>
        return none
  else
    return none


/-- Detect whether exactly one side of a relation contains an external `% n`. -/
def externalModulusOneSide? (ty : Expr) : MetaM (Option (Expr × Nat)) := do
    let ty ← instantiateMVars ty
    let (fn, args) := ty.getAppFnArgs
    let sides? : Option (Expr × Expr) :=
      match fn with
      | ``Eq    => if args.size >= 2 then some (args[args.size-2]!, args[args.size-1]!) else none
      | ``LT.lt  => if args.size >= 2 then some (args[args.size-2]!, args[args.size-1]!) else none
      |  ``LE.le  => if args.size >= 2 then some (args[args.size-2]!, args[args.size-1]!) else none
      | ``GT.gt  => if args.size >= 2 then some (args[args.size-2]!, args[args.size-1]!) else none
      | ``GE.ge  => if args.size >= 2 then some (args[args.size-2]!, args[args.size-1]!) else none
      | _ => none
    match sides? with
    | none => pure (none)
    | some (lhs, rhs) =>
        let getModLit (e : Expr) :  MetaM (Option (Expr × Nat)) := do

          let (f, as) := e.getAppFnArgs

          match f with
          | ``HMod.hMod =>
              if h : as.size >= 2 then

                let (f2, as2) := as[as.size-1].getAppFnArgs
                match f2 with
                | ``OfNat.ofNat =>

                   match as2[as2.size-2]! with
                      | Expr.lit (Literal.natVal n) => pure (some (as[as.size-2], n))
                      | _ => pure ( none )
                | _ => pure none
              else
                pure none
          | _ => pure none

        let ml ← getModLit lhs
        let mr ← getModLit rhs
        match ml, mr with
        | some n, none   => pure (some n)
        | none,   some n => pure (some n)
        | _,      _      => pure none


/-- Extend external modulus detection through top-level `Iff` and `And`. -/
def externalModulusOneSideWrapper? (ty : Expr) : MetaM (Option (Expr × Nat)) := do
let (fn, args) := ty.getAppFnArgs
    match fn with
      | ``Iff => do
          if args.size >= 2 then
            let h ← externalModulusOneSide? args[args.size-2]!
            let k ← externalModulusOneSide? args[args.size-1]!
            match h, k with
            | some n, none   => pure (some n)
            | none,   some n => pure (some n)
            | _,      _      => pure none
          else
            pure none
       | ``And => do
          if args.size >= 2 then
            let h ← externalModulusOneSide? args[args.size-2]!
            let k ← externalModulusOneSide? args[args.size-1]!
            match h, k with
            | some n, none   => pure (some n)
            | none,   some n => pure (some n)
            | _,      _      => pure none
          else
            pure none
       | _ => externalModulusOneSide? ty


/-- Internal tactic used by translation to discharge external modulus side conditions. -/
syntax (name := dbg_mod_syn) "dbg_mod" num "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| dbg_mod $k:num [$ids:ident,*]) => do
  withMainContext do
    let k : Nat := k.getNat

    let g ← getMainGoal
    let goalTy ← g.getType
    let oldGoals ← getGoals

     match (← externalModulusOneSideWrapper? goalTy) with
    | none => pure ()
    | some (exp, n) =>
        if k < n then
          let A : Expr := mkApp2 (mkConst ``Nat.lt) exp (mkNatLit k)

          let pr ← g.withContext do mkFreshExprMVar (some A)

          let gWithHyp ← g.withContext do
            liftMetaM <| g.assert (Name.mkSimple "hmod") A pr

          let rest : List MVarId := oldGoals.erase g

          setGoals (pr.mvarId! :: gWithHyp :: rest)

          evalTactic (← `(tactic| try simp) )
          withMainContext do
            let g <- getMainGoal
            evalTactic (← `(tactic| focus  try_apply_lemma_hyps [$[$ids],*] ))
          evalTactic (← `(tactic| try simp ) )
          let g ← getMainGoal
          let name := Name.mkSimple s!"proof"
          let (kId, g')  <- g.intro name
          replaceMainGoal [g']
          g.withContext do
            evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] ))
            evalTactic (← `(tactic| swap ))
            let hcTerm  : TSyntax `term  := ⟨mkIdent `proof⟩
            evalTactic (← `(tactic| apply lt_of_lt_of_le $hcTerm (by decide)))
            let bitsize := ceilLog2 k
            let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
            evalTactic (← `(tactic|  rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
            evalTactic (← `(tactic| all_goals try apply $hcTerm))
        else
          throwError "Why is modulus bigger? {k} and {n}"


/-- Recursively gather all `(width, x)` pairs inside an expression, for matches
    of the form `BitVec.ofNat k (ZMod.val x)`. -/
partial def collectMatches (e : Expr) : MetaM (Array (Nat × Expr × Expr)) := do
  let mut acc := #[]
  if let some p ← matchOfNatVal? e then
    acc := acc.push p

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
      pure ()

  return acc


/-- Collect all `(width, x)` pairs from the goal type and all local hypotheses
    (both their types and, if present, their values). -/
def collectFromContext : TacticM (Array (Nat × Expr × Expr)) := do
  let goal ← getMainGoal
  let goalTy ← goal.getType
  goal.withContext do
    let mut out : Array (Nat × Expr × Expr) := #[]
    out := out ++ (← collectMatches (goalTy))
    let lctx ← getLCtx
    for decl in lctx do


      if decl.isImplementationDetail then
        continue

      let e <- instantiateMVars decl.type
      let e ← whnf e
      out := out ++ (← collectMatches e)
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

/-- Add cast-width bridge lemmas for variables occurring at multiple bit-widths. -/
syntax "autoCastBits" "[" ident,* "]" : tactic

elab_rules : tactic
| `(tactic| autoCastBits [$ids,*]) => do
  let hyps := (ids.getElems.map (·.getId)).toList
  /- Scan the current context for casts that need width-bridge lemmas. -/
  let pairsArr ← collectFromContext
  let pairs := pairsArr.toList

  let mut groups : List (Name  × Expr × List Nat) := []
  let mut modulus : Option Expr := none
  for (w, x, f) in pairs do
    modulus := some f
    let myName := (<- collectTerms x).toList[0]!
      match lookupGroup myName groups with
      | some ws =>
          groups := insertGroup myName x w groups
      | none =>
          groups := (myName, x, [w]) :: groups

  let some modExpr := modulus
    | throwError "[autoCastBits] no modulus found"
  let lctx ← getLCtx
  let mut goal ← getMainGoal

  for (fid, x, ws) in groups do

    let uniq := ws.eraseDups
    let maxW := uniq.foldl Nat.max uniq.head!

    let baseName := fid
    for w in ws do
       if w != maxW then
                  let lemmaName := baseName.appendAfter s!"_cast_{w}"

                  let zmodValBase := mkConst ``_root_.ZMod.val
                  let zmodValTyped := mkApp zmodValBase modExpr
                  let valExpr := mkApp zmodValTyped x

                  let lhs :=
                    mkAppN (mkConst ``BitVec.ofNat) #[mkNatLit w, valExpr]

                  let bigVec :=
                    mkAppN (mkConst ``BitVec.ofNat)
                      #[ mkNatLit maxW, valExpr ]

                  let rhs :=
                    mkAppN (mkConst ``BitVec.setWidth)
                      #[ mkNatLit maxW, mkNatLit w, bigVec ]


                  let eq <- mkEq lhs rhs

                  let pf ← elabTerm (← `(by simp)) eq
                  let newGoal ← goal.assert lemmaName eq pf
                  goal := newGoal


              replaceMainGoal [goal]
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
          let some decl := lctx.findFromUserName? c
            | throwError m!"Cannot find hypothesis {c}"

          let hIdent := Lean.mkIdent decl.userName

          evalTactic (← `(tactic| specialize $hIdent $bitsStx (by decide)))


        catch e =>
          pure ()

    goal ← getMainGoal

/-- Introduce all leading binders with generated names. -/
partial def introAll (i : Nat := 0) (revNames : List Name := []) : TacticM (List Name) := do
  let name := Name.mkSimple s!"h{i}"
  let g ← getMainGoal
  try
    let (_, g') ← g.intro name
    replaceMainGoal [g']
  catch _ => return revNames.reverse
  introAll (i + 1) (name :: revNames)


/-- Count subtraction nodes in an expression after metavariable instantiation. -/
partial def countMinusOps2 (e : Expr) : MetaM Nat := do
  let e ← instantiateMVars e


  let here :=
    match e.getAppFn with
    | .const n _ =>
        if n == ``HSub.hSub || n == ``Sub.sub || n == ``Nat.sub then 1 else 0
    | _ => 0

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

/-- Count top-level and nested conjunction nodes. -/
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


/-- Count top-level and nested disjunction nodes. -/
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
| `(tactic| translate_hypothesis $h:ident [$ids,*] [$non_v,*] $[$b:term]? ) => withMainContext do
  /- Build simpArg array (empty if none provided). -/
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
  let all : Array Lean.Ident := ids ++ non_v
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
  /- Expand CirC/BVModEq mapping definitions before normalization. -/
  let mut circLoop := true
  while (circLoop) do
  try
    evalTactic (← `(tactic|  rw [map_f_to_bv_circ_spec] at $(mkIdent h.getId):ident) )
  catch _ =>
    circLoop := false
  /- Normalize subtraction-heavy expressions into the shapes expected by later lemmas. -/
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
  subLoop := true
  while (subLoop) do
    try
      evalTactic (← `(tactic| rw [<- zero_sub] at $(mkIdent h.getId):ident))
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
    pure (countAnds decl.type + countOrs ty)

  if i > 0 then
    let mut mLoop := true
    while (mLoop) do
      try
      evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_l] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_r] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| rw [sub_add_right_recursive] at $(mkIdent h.getId):ident))
      catch _ =>
        mLoop := false
  evalTactic (← `(tactic| try simp (config := { maxSteps := 200000 }) only [BVModEq.ZMod.eq_if_val] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [<- zero_sub] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try simp (config := { zeta := false, beta := false }) at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try rw [neg_add_to_sub]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [<- zero_sub] at $(mkIdent h.getId):ident))


  subLoop := true
  if k > 0 then
    while (subLoop) do
      try
        evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
      catch _ => subLoop := false
  evalTactic (← `(tactic| try valify [$[$sargs],*]   at $(mkIdent h.getId):ident))
  let mut progress:= true
  while(progress ) do
      try
        evalTactic (← `(tactic| rw [ZMod.val_sub]  at $(mkIdent h.getId):ident) )
        let cur_g ← getGoals
        match cur_g with
        | [] => throwError "No goals after reorder"
        | _ :: [] => throwError "wrong number of goals"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            withMainContext  do
               evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$all],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ( [g_one] ++ rest_rev)
              evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))
            else
              throwError "lemma application did not solve goal"

      catch _ =>
        try
          evalTactic (← `(tactic| rw [ZMod.val_sub_strict]  at $(mkIdent h.getId):ident))
          evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))
        catch _ =>
          progress := false
    evalTactic (← `(tactic| try valify [$[$sargs],*]  at $(mkIdent h.getId):ident))


  let m ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    CalcBitWidth decl.type ids
  let bitsize := ceilLog2 (Nat.max (m+1) 4)
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_leq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))
  if k > 0  then
    subLoop := true
    while (subLoop ) do
      try
        evalTactic (← `(tactic|  rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx] at $(mkIdent h.getId):ident))
        evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident))
      catch _ =>
        subLoop := false
  if i > 0  then
    subLoop := true
    while (subLoop ) do
      try
        evalTactic (← `(tactic|  rw [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident))
        evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
      catch _ =>
        subLoop := false
  subLoop := true
  while (subLoop ) do
      try
        evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] at $(mkIdent h.getId):ident) )
        let cur_g ← getGoals
        match cur_g with
        | [] => throwError "No goals after reorder"
        | _ :: [] => throwError "wrong number of goals"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            withMainContext  do
              evalTactic (← `(tactic| try focus try_apply_lemma_hyps [$[$all],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ([g_one] ++ rest_rev)
              evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
            else
              throwError m! "try_apply failed {after}"
      catch e =>
        try
          evalTactic (← `(tactic| rw [BitVec.ofNat_mod_move] at $(mkIdent h.getId):ident) )
          evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
        catch _ =>
          try
            evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident) )
            evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
          catch _ =>
            subLoop := false
    evalTactic (← `(tactic|  try simp (config := { zeta := false, beta := false }) at $(mkIdent h.getId):ident) )


/-- Translate the current goal into a bitvector-friendly form. -/
syntax (name := translateGoal)
  "translate_goal" ppSpace ("[" ident,* "]")? (ppSpace term)? : tactic


/-- Detect a `BitVec.ofNat` whose payload is arithmetic-headed. -/
private def compositeInsideBVHere? (e : Expr) : MetaM (Option Expr) := do

  if e.isAppOf ``BitVec.ofNat then
    let args := e.getAppArgs
    if let some t := args.back? then
      if isArithmeticHead t then
        return some e
  return none

private def isEqRecLike (e : Expr) : Bool :=
  e.isConstOf ``Eq.rec || e.isConstOf ``Eq.ndrec


/-- Find the first composite expression occurring inside `BitVec.ofNat`. -/
partial def firstCompositeInsideBV?
    (seen : HashSet UInt64) (e : Expr)
    : MetaM (Option Expr ) := do

  let e := e.consumeMData

  let h := e.hash
  if seen.contains h then
    return none
  if e.isFVar then return none
  let e := e.consumeMData
  match (← compositeInsideBVHere? e) with
  | some hit => return some hit
  | none =>
    match e with
    | .app f a =>
        if isEqRecLike f then
          return none
        match (← firstCompositeInsideBV? seen f) with
        | some hit => return some hit
        | none     => firstCompositeInsideBV? seen a
    | .mdata _ b => firstCompositeInsideBV? seen b
    | .proj _ _ b => firstCompositeInsideBV? seen b
    | _ =>
      pure none

/-- Repeatedly extract and translate composite `BitVec.ofNat` subterms until stable. -/
partial def loopUntilDone
    (flag : Bool)
    (hs : Array (TSyntax `ident))
    (count : Nat)
    (seen? : Option (Std.HashSet UInt64) := none)
    : TacticM (Std.HashSet UInt64) := do
  if count == 10 then
    return seen?.getD {}
  let g ← getMainGoal

  let t ← g.getType
  let mut seen : Std.HashSet UInt64 := seen?.getD {}

  let t2 <- instantiateMVars t
  let flagStx ←
  if flag then
    `(true)
  else
    `(false)
  let t2 ← withReducible <| whnf t2
  let res ← g.withContext do
      firstCompositeInsideBV? seen t2
  match res with
  | none =>
      return seen?.getD {}

  | some if_comp =>


        withMainContext do
          let big ← instantiateMVars if_comp
          let bigTy ← inferType big

          let g ← getMainGoal
          let g ← g.define `kc bigTy big
          let name := Name.mkSimple s!"k"
          let (kId, g)  <- g.intro name
          g.withContext do

            let kc' := mkFVar kId

            let eq <- mkEq kc' big


              let pf ← elabTerm (← `(by rfl)) eq
              let lemmaName := Name.mkSimple s!"hc"
              let newGoal ← g.assert lemmaName eq pf
              let lemmaName0 := Name.mkSimple s!"hc0"
              let (_, g')  <- newGoal.intro lemmaName0
              replaceMainGoal [g']


        withMainContext do
              let lctx ← getLCtx
              let some kcDecl := lctx.findFromUserName? `hc0
                  | throwError "hc0 missing"
              let hcIdent : TSyntax `ident := ⟨mkIdent `hc0⟩
              let hcTerm  : TSyntax `term  := ⟨mkIdent `hc0⟩

              let hcRw    : TSyntax `Lean.Parser.Tactic.rwRule := ⟨(← `(Lean.Parser.Tactic.rwRule| $hcTerm:term)).raw⟩
              let hcIdStx :  TSyntax `Lean.Parser.Tactic.simpStar:= ⟨ mkIdent `hc0 ⟩
              let hcLemma : TSyntax `Lean.Parser.Tactic.simpLemma :=
                  ⟨(← `(Lean.Parser.Tactic.simpLemma| $hcIdent:ident)).raw⟩

              evalTactic (← `(tactic| try simp [<- $hcIdent]))
              evalTactic (← `(tactic| translate_hypothesis $hcIdent [$hs,*] [] $flagStx ))
              evalTactic (← `(tactic| try simp [$hcLemma]))

              let lctx ← getLCtx
        let key : UInt64 := if_comp.hash

        seen := seen.insert key

        loopUntilDone flag hs (count + 1) (some seen)


@[tactic translateGoal]
elab_rules : tactic
| `(tactic| translate_goal [$ids,*] $[$b:term]? ) => withMainContext do
  /- Build simpArg array (empty if none provided). -/
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
  let mut circLoop := true
  while (circLoop) do
    try
        evalTactic (← `(tactic|  rw [map_f_to_bv_circ_spec]  ))
    catch _ =>
      circLoop := false
  evalTactic (← `(tactic| all_goals try unfold BVModEq.bool_to_bv ))
  evalTactic (← `(tactic| all_goals try unfold BVModEq.map_bv_to_f  ))
  evalTactic (← `(tactic| try unfold BVModEq.smtSignExtend ))
  evalTactic (← `(tactic| try unfold BVModEq.smtZeroExtend  ))
  evalTactic (← `(tactic| try unfold BVModEq.BitVec.mod  ))

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
  subLoop := true
  while (subLoop) do
    try
      evalTactic (← `(tactic| rw [<- zero_sub]))
    catch _ =>
      subLoop := false
  let mut mLoop := true
  evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_l]))
  while (mLoop) do
    try
      evalTactic (← `(tactic| rw [sub_add_right_recursive]))

    catch _ =>
      mLoop := false
  let mut g ← getMainGoal
  let mut t ← g.getType
  let i  ←  countMinusOps2 t
  let k := countOrs t + countAnds t

  evalTactic (← `(tactic| try simp (config := { maxSteps := 200000 }) only [BVModEq.ZMod.eq_if_val] ))
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]))
  evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
  evalTactic (← `(tactic| try rw [<-zero_sub] ))
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]))
  let mut goals <- getGoals
  if goals.isEmpty then
    logInfo m!"Goal solved during translation."
    return
  if k > 0 then
    subLoop := true
    while (subLoop) do
      try
        evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val] ))
      catch _ =>
        subLoop := false
    evalTactic (← `(tactic| try valify [$[$sargs],*] ) )
  evalTactic (← `(tactic| try rw [<-zero_sub] ))
  if i > 0 then
     evalTactic (← `(tactic|  try rw [<- sub_eq_add_neg]))
     evalTactic (← `(tactic| try rw [<-zero_sub] ))
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
            withMainContext  do
                evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ([g_one] ++ rest_rev)
              evalTactic (← `(tactic| try valify [$[$sargs],*]))
            else
              throwError "lemma application did not solve goal"

      catch e =>
        try
          evalTactic (← `(tactic| rw [ZMod.val_sub_strict]))
          evalTactic (← `(tactic| try valify [$[$sargs],*]))
        catch e =>
          progress := false

  evalTactic (← `(tactic| try simp   ) )


  let mut rmFailed := false
  /- Pull out composite `BitVec.ofNat` subterms and translate them recursively. -/
  let seen <- loopUntilDone flag ids (count+1)
  goals <- getGoals
  if goals.isEmpty then
    logInfo m!"Goal solved during translation."
    return
  let m <- withMainContext do  CalcBitWidth (<-goals[0]!.getType) ids
  let bitsize := ceilLog2 (Nat.max (m+1) 4)
  let bitsize_full := Nat.pow 2 bitsize
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  let bitsizeStx_full : TSyntax `num := Syntax.mkNumLit (toString bitsize_full)


  try
      evalTactic (← `(tactic| dbg_mod $bitsizeStx_full [$[$ids],*]))


  catch e =>
      pure ()

  /- Rewrite the goal from natural-number equalities into bitvector equalities. -/
  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))

  subLoop := true
  if k > 0 then do
    while (subLoop) do
      try
        evalTactic (← `(tactic| rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
        evalTactic (← `(tactic| try bvify [$[$sargs],*]))
      catch _ =>
        subLoop := false

  let mut modLeft := true
  subLoop := true
  while (subLoop ) do
      count :=count + 1
      try
        evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
        let cur_g ← getGoals
        match cur_g with
        | [] =>
            throwError "No goals after Nat.mod_eq_of_lt"
        | _ :: []  =>
            throwError "Unexpected number of goals after Nat.mod_eq_of_lt"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            withMainContext  do
                  evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ( [g_one ] ++ rest_rev )
              evalTactic (← `(tactic| try bvify [$[$sargs],*]))

            else
              throwError m! "try_apply failed {after}"
      catch e =>
        rmFailed := false
        try
          evalTactic (← `(tactic| rw [BitVec.ofNat_mod_move]))
          evalTactic (← `(tactic| try bvify [$[$sargs],*]))
        catch e =>
           try
             evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
             evalTactic (← `(tactic| try bvify [$[$sargs],*]))
            catch _ =>
              subLoop := false
  evalTactic (← `(tactic| try simp  ))
  let x <-loopUntilDone flag ids (count+1)


/-- Recognize an idempotent equality over `ZMod` terms. -/
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
    evalTactic (← `(tactic| try simp only [and_assoc] at $(mkIdent h.getId):ident ))
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hyp `{h.getId}` in context"

    let ty ← whnf decl.type
    let num := countAnds ty + 1
    if num == 1 then
      return #[h]

    let names : Array (TSyntax `ident) :=
      (List.range num).map (fun i => mkIdent (Name.mkSimple s!"{h.getId}_{i+1}")) |>.toArray
    evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident with ⟨$[$names],*⟩))
    return names

def smartTranslateOne
    (h : TSyntax `ident)
    (extraArgs :
      Array (TSyntax [`Lean.Parser.Tactic.simpStar,
                      `Lean.Parser.Tactic.simpErase,
                      `Lean.Parser.Tactic.simpLemma]))
                        (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident))): TacticM ( Option (TSyntax `ident) × Option (TSyntax `ident ) × Option (TSyntax `ident ) × Option (TSyntax `ident)) := do
    withMainContext do

    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hypothesis `{h.getId}` in local context"

    let hIdent : TSyntax `ident := mkIdent decl.userName
    let hType ← whnf decl.type
    match isZModIdemEq hType with
    | some _ => do
        evalTactic (← `(tactic| rw [BVModEq.square_eq_one_zero 257] at $(mkIdent h.getId):ident))
        let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
        let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
        evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $h2⟩))
        return (some h1, none, some h2, none)
    | none =>
        match getVarEq hType with
          | some rhsVarId => do

              try

                evalTactic (← `(tactic| rw [duplicate] at $(mkIdent h.getId):ident))

                let newName := mkIdent (Name.mkSimple s!"{h.getId}_new")

                evalTactic (← `(tactic|
                  rcases $(mkIdent h.getId):ident with ⟨$(mkIdent h.getId):ident, $newName⟩))

                evalTactic (← `(tactic| try rw [BVModEq.bool_to_bv] at $(mkIdent newName.getId):ident))


                let m ← varToHypRef.get
                if m.contains rhsVarId then
                  return (none ,none, none, some h)
                else
                  varToHypRef.modify fun m => m.insert rhsVarId newName

                  return (none ,none, some newName, some h)
              catch _ => pure ()
          | _ => --pure ()
          try
            evalTactic (← `(tactic| apply BVModEq.extract_bv_rel at $(mkIdent h.getId):ident))
            let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
            let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
            evalTactic (← `(tactic| rcases $(mkIdent h.getId):ident  with ⟨$h1, $h2⟩))
            return (some h1, some h2, none, none)
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
              evalTactic (← `(tactic| apply BVModEq.extract_bv_leq at $h1:ident))
              return (some newName, some h1, none, none)
            catch e =>
                pure ()


       return (none, none, none, some h)


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
  let mut replacement : Array (TSyntax `ident) := #[]
  let flagStx ←
  if flag then
    `(true)
  else
    `(false)
  for h in hs do

   let (k?, x?, h?, w?) ← smartTranslateOne h extraArgs varToHypRef

    match h? with
    | some h => replacement := replacement.push h
    | none   => pure ()


    match k? with
    | some k => picked := picked.push k
    | none   => pure ()

    match x? with
    | some x => changed := changed.push x
    | none   => pure ()


    match w? with
    | some w =>translate := translate.push w
    | none => pure ()
  for h in translate do
    evalTactic (← `(tactic| translate_hypothesis $h [$[$picked],*]  [$[$replacement],*] $flagStx ))

  return (picked++replacement,changed)

/-- One-shot orchestrator:
    intro h; split; smart-translate; translate_goal; bv_decide; try_apply_lemma_hyps [*_1 ...] -/
syntax (name := translateAll) "translate_all" ppSpace
  ("[" ident,* "]")?  (ppSpace term)? : tactic

@[tactic translateAll]
elab_rules : tactic
| `(tactic| translate_all $[[ $extraSimp,* ]]? $[$b:term]? ) => withMainContext do
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
  evalTactic (← `(tactic| try simp [-one_mul, -mul_one]))
  let gs ← getGoals
  if gs.isEmpty then
    logInfo "No goals remain after translation."
    return

  let name := Name.mkSimple s!"h"
  let g ← getMainGoal
  let hyps : List Name ← introAll
  let mut ids : Array (TSyntax `ident) := #[]
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
  let ( collected, changed) := (← smartTranslateMany ids sargs varToHypRef flag)

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
  let tgt ← (← getMainGoal).getType
  let tgt <- whnf tgt
  let (fn, args) := tgt.getAppFnArgs
  let mut bitblast :=
    match fn with
    | ``Eq  => true
    | ``Or => true
    | ``And => true
    | ``Iff => true
    | _ => false

  if bitblast then
      try
        evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
      catch _ =>

        let all := collected ++ changed
        evalTactic (← `(tactic| autoCastBits [$[$all],*]))
        let mut rw := true
        while (rw) do
          try
              evalTactic (← `(tactic| intro h))
              evalTactic (← `(tactic| try rw [h]))
              for hyp in ids ++ changed  do
                evalTactic (← `(tactic| try rw [h] at $(mkIdent hyp.getId):ident))
              evalTactic (← `(tactic| clear h))
          catch _ =>
            rw := false
        try
          evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
        catch _ =>
          pure ()

          try
            let mut index :=0
            let fv1T : TSyntax `term := (← termFor `fv1)
            let fv2T : TSyntax `term := (← termFor `fv2)
            while index < collected.size/2 do

              let idName  := Name.mkSimple s!"b0_{index}"

              let idSyn   : TSyntax `ident := mkIdent idName
              let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

              evalTactic (← `(tactic|
                set $idSyn := $fv1T[$idxSyn]
              ))
              index := index + 1
            index := 0
            while index < collected.size/2 do
              let idName  := Name.mkSimple s!"b1_{index}"

              let idSyn   : TSyntax `ident := mkIdent idName
              let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

              evalTactic (← `(tactic|
                set $idSyn := $fv2T[$idxSyn]
              ))
              index := index + 1
            evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
        catch _ =>
            evalTactic (← `(tactic| split_ands))


  withMainContext do
    evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))
  after ← getGoals

  if !after.isEmpty then
    while (!after.isEmpty) do
      let before ← getGoals

      withMainContext do
        evalTactic (← `(tactic| translate_goal [$[$collected],*] $flagStx))
      let tgt ← (← getMainGoal).getType
      let tgt <- whnf tgt
      let (fn, args) := tgt.getAppFnArgs
      bitblast :=
          match fn with
          | ``Eq  => true
          | ``Or => true
          | ``And => true
          | ``Iff => true
          | _ => false
      if bitblast then
          let g <- getMainGoal
          withMainContext do
            evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))

      withMainContext do
        evalTactic (← `(tactic| try_apply_lemma_hyps [$[$collected],*]))

      after ← getGoals
      if before == after then
        return

end BVModEq
