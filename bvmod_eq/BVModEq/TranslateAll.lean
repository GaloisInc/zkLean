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

syntax (name := translateHypothesis) "translate_hypothesis" ppSpace ident ("[" ident,* "]")?  ("[" ident,* "]")? (ppSpace term)? : tactic

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
  let e ← withReducible <| whnf e
  --logInfo m!"{e}"
  let fn  := e.getAppFn
  let args := e.getAppArgs
  if args.isEmpty then
    let ty ← inferType e >>= whnf
    match ty.getAppFnArgs with
    | (``BitVec , #[w]) =>
         --return (<- CalcBitWidth w hs)
        match (← whnf w) with
          | (Expr.lit (Literal.natVal n)) =>
             return 2^n
          | _ =>  logInfo m!"UGH"
    --         logInfo m!"BitVec width not a numeral: {w}"
    --         return 1
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
          return (<- CalcBitWidth args[args.size-1]! hs)
        throwError "wrong # args BitVec.toNat"
        --return 10
    | ``Or =>
       if  args.size ≥ 2 then
        return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
       throwError "wrong # args or {args}"
    | ``And =>
       if  args.size ≥ 2 then
        --logInfo m!"LHS {(<- CalcBitWidth args[args.size-2]! hs)}"
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
      logInfo m!"unsupported ap {name} with {args} and {args.size}"
      if  args.size ≥ 2 then
          return Nat.max (<- CalcBitWidth args[args.size-1]! hs)  (<- CalcBitWidth args[args.size-2]! hs)
      return 1
  | _ =>
      logInfo m!"unsupported op {fn} with {args}"
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


lemma sub_add_right_recursive_paren_l (a b c:ZMod p): (a-b) + c = a+c -b := by
  ring

lemma sub_add_right_recursive_paren_r (a b c:ZMod p): c + (a-b)  = a+c -b := by
  ring

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




def externalModulusOneSide? (ty : Expr) : MetaM (Option (Expr × Nat)) := do
    let ty ← instantiateMVars ty
    --let ty ← whnf ty
    let (fn, args) := ty.getAppFnArgs
    -- extract the two sides of a relation (we consistently take the last two args)
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
        -- get `% n` modulus if expression is `Nat.mod _ n` with numeral n
        let getModLit (e : Expr) :  MetaM (Option (Expr × Nat)) := do
          --let e ← whnf e

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
                   --pure (some 2)
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
       | _ => externalModulusOneSide? ty


syntax (name := dbg_mod_syn) "dbg_mod" num "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| dbg_mod $k:num [$ids:ident,*]) => do
      -- k : Syntax, ids : Array Syntax
  withMainContext do
    let k : Nat := k.getNat

    let g ← getMainGoal
    let goalTy ← g.getType
    let oldGoals ← getGoals

     match (← externalModulusOneSideWrapper? goalTy) with
    | none => pure ()
    | some (exp, n) =>
        if k < n then
        -- A : Prop := exp < k
          let A : Expr := mkApp2 (mkConst ``Nat.lt) exp (mkNatLit k)

          -- pr : ?m : A  (this will become the "prove A" subgoal)
          let pr ← g.withContext do mkFreshExprMVar (some A)

          -- add hypothesis hmod : A := pr to the original goal context
          let gWithHyp ← g.withContext do
            -- NOTE: in your Lean, `assert` is MetaM, so lift it:
            liftMetaM <| g.assert (Name.mkSimple "hmod") A pr

          -- prove A first, then solve original goal with hmod available
          let rest : List MVarId := oldGoals.erase g

    -- set goals = prove A first, then continue with hypothesis, then the rest
          setGoals (pr.mvarId! :: gWithHyp :: rest)

          evalTactic (← `(tactic| try simp) )
          evalTactic (← `(tactic| focus  try_apply_lemma_hyps [$[$ids],*] ))
          evalTactic (← `(tactic| try simp) )
          let g ← getMainGoal
          let name := Name.mkSimple s!"proof"
          let (kId, g')  <- g.intro name
          replaceMainGoal [g']
          let proofExpr := mkFVar kId
          --evalTactic (← `(tactic| intro proof) )
          g.withContext do
            evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt] ))
            evalTactic (← `(tactic| swap ))
            let hcTerm  : TSyntax `term  := ⟨mkIdent `proof⟩
            evalTactic (← `(tactic| apply lt_of_lt_of_le $hcTerm (by decide)))
            let bitsize := ceilLog2 k
            let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
            evalTactic (← `(tactic|  rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
            evalTactic (← `(tactic| swap ))
            evalTactic (← `(tactic| focus try_apply_lemma_hyps [$[$ids],*]))
            evalTactic (← `(tactic| swap ))
            evalTactic (← `(tactic| apply $hcTerm))
        else
          pure ()


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
  --logInfo m!"=== Groups after aggregation ==="
  --  for (fid, ws) in groups do
  --    logInfo m!"{fid}: widths = {ws}"

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
        --logInfo m!"{c}"
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


  logInfo "=== autoCastBits: finished ==="




lemma ZMod.val_neg_sub_zero {p : Nat} {x : ZMod p} : (-x : ZMod p) = (0 - x) := by
  simpa using (zero_sub x).symm









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
| `(tactic| translate_hypothesis $h:ident [$ids,*] [$non_v,*] $[$b:term]? ) => withMainContext do
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
  let mut circLoop := true
  while (circLoop) do
  try
    evalTactic (← `(tactic|  rw [map_f_to_bv_circ_spec] at $(mkIdent h.getId):ident) )
  catch _ =>
    circLoop := false
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
      evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_l] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_r] at $(mkIdent h.getId):ident))
      evalTactic (← `(tactic| rw [sub_add_right_recursive] at $(mkIdent h.getId):ident))
      catch _ =>
        mLoop := false
  evalTactic (← `(tactic| try simp (config := { maxSteps := 200000 }) only [BVModEq.ZMod.eq_if_val] at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [<- sub_eq_add_neg]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try rw [neg_add_to_sub]  at $(mkIdent h.getId):ident))
  evalTactic (← `(tactic| try valify [$[$sargs],*] at $(mkIdent h.getId):ident) )
  evalTactic (← `(tactic| try simp (config := { zeta := false, beta := false }) at $(mkIdent h.getId):ident) )
  for _ in [0:k] do

      evalTactic (← `(tactic| try rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
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
            --logInfo m!"LAST: {g_last}"
            -- let last := cur_g.getLast!
            -- let init := cur_g.dropLast
            -- focus only the last goal
            withMainContext  do
              evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$all],*]))
            let after ← getGoals
            --logInfo m!"CUR GOALS: {after}"
            if after.isEmpty then
              setGoals ( [g_one] ++ rest_rev)
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
  try
    evalTactic (← `(tactic| try simp (config := { zeta := false, beta := false }) at $(mkIdent h.getId):ident) )
    -- let i ← withMainContext do
    -- let lctx ← getLCtx
    -- let isTrue ← withMainContext do
    --   let lctx ← getLCtx
    --   let some decl := lctx.findFromUserName? h.getId
    --     | throwError m!"No hypothesis named {h.getId}"

    --   let ty ← instantiateMVars decl.type
    --   let ty ← whnf ty

    --   pure <| match ty with
    --     | Expr.const ``True _ => true
    --     | _ => false
    -- if isTrue then
    --   throwError m!"Simplified too much"
  catch _ => pure ()
  subLoop := true
  while (subLoop ) do
    try
      evalTactic (← `(tactic| rw [BVModEq.ZMod.eq_if_val]  at $(mkIdent h.getId):ident) )
      evalTactic (← `(tactic| try valify [$[$sargs],*]   at $(mkIdent h.getId):ident))
    catch _ =>
      subLoop  := false

  --- BEFORE WE CALC BIT WIDTH WE SHOULD REMOVE MOD?
  --- x % f < 2^N  /\ x < f --> x <
  --- ideally we only have to do x < 2^N /\
  let m ← withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"No hypothesis named {h.getId}"
    CalcBitWidth decl.type ids
 -- logInfo m!"FIRST  {m}"
  let bitsize := ceilLog2 (Nat.max (m+1) 4)
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  logInfo m!"{bitsize} with {m}"
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
        | [] => throwError "No goals after reorder"
        | _ :: [] => throwError "wrong number of goals"
        | g_one :: g_last :: rest_rev => do
            setGoals [g_last]
            withMainContext  do
             -- logInfo m!"{g_last}"
              evalTactic (← `(tactic| try focus try_apply_lemma_hyps [$[$all],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ([g_one] ++ rest_rev)
              evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
            else
              throwError m! "try_apply failed {after}"
      catch e =>
        --logInfo (Lean.Exception.toMessageData e)
        try
          evalTactic (← `(tactic| rw [BitVec.ofNat_mod_move] at $(mkIdent h.getId):ident) )
          evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
        catch _ =>
          try
            evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub] at $(mkIdent h.getId):ident) )
            evalTactic (← `(tactic| try bvify [$[$sargs],*] at $(mkIdent h.getId):ident) )
          catch _ =>
            subLoop := false
  try
      evalTactic (← `(tactic| try simp (config := { zeta := false, beta := false }) at $(mkIdent h.getId):ident) )
      -- let i ← withMainContext do
      -- let lctx ← getLCtx
      -- let isTrue ← withMainContext do
      --   let lctx ← getLCtx
      --   let some decl := lctx.findFromUserName? h.getId
      --     | throwError m!"No hypothesis named {h.getId}"

      --   let ty ← instantiateMVars decl.type
      --   let ty ← whnf ty

      --   pure <| match ty with
      --     | Expr.const ``True _ => true
      --     | _ => false
      -- if isTrue then
      --   throwError m!"Simplified too much"
  catch _ => pure ()

syntax (name := translateGoal)
  "translate_goal" ppSpace ("[" ident,* "]")? (ppSpace term)? : tactic

-- def noteRhs (rhs : Expr) : TacticM Name := do
--   let g ← getMainGoal
--   withMVarContext g do
--     let rhsName ← mkFreshUserName `rhs
--     let rhsTy ← inferType rhs  -- should be Bool if it’s an if-condition
--     let (fvarId, g') ← g.note rhsName rhsTy rhs
--     setMainGoal g'
--     return rhsName

partial def loopUntilDone (flag: Bool) (hs : Array (TSyntax `ident)) (count: Nat) : TacticM Unit := do
  if count == 10 then
    return
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

        logInfo m!"🔍 Found composite: {if_comp}"

        -- Turn Expr into Syntax so we can splice it

        withMainContext do
        -- 1) work with Expr directly (no delab)
          let big ← instantiateMVars if_comp
          let bigTy ← inferType big
          -- let (kId, g1) ← (← getMainGoal).note `k bigTy big
          -- replaceMainGoal [g1]
          -- logInfo m!"big = {big}"
          -- logInfo m!"bigTy = {bigTy}"
          -- logInfo m!"bigTy whnf = {(← whnf bigTy)}"
        -- let k := mkFVar kId
        -- let eq <- mkEq k big    -- EXACTLY: k = (BitVec.ofNat ...)[0]
        -- let g2 ← getMainGoal
        -- let pf ← elabTerm (← `(by rfl)) eq
        -- let lemmaName := Name.mkSimple s!"hc"
        -- let g' <- g2.assert lemmaName eq pf
        -- replaceMainGoal [g']

        -- define kc := big  (context local def, like `set`)
          let g ← getMainGoal
          let g ← g.define `kc bigTy big
          let name := Name.mkSimple s!"k"
          let (kId, g)  <- g.intro name
          g.withContext do
        --   replaceMainGoal [g]

        -- withMainContext do
        -- -- add hc : kc = big
          -- withMainContext do
            -- let big ← instantiateMVars if_comp
            -- let bigTy ← inferType big
            -- let lctx ← getLCtx
            -- let some kcDecl := lctx.findFromUserName? `k
              --   | throwError "kc missing"
            let kc' := mkFVar kId

            let eq <- mkEq kc' big

          --           --logInfo m!"Adding lemma {eq} for {baseName}: minW={minW}, maxW={maxW}"

          --           -- Build the proof by `simp`
              let pf ← elabTerm (← `(by rfl)) eq
          --           --let mut goal2 <- getMainGoal
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
              let hcIdStx :  TSyntax `Lean.Parser.Tactic.simpLemma:= ⟨ mkIdent `hc0 ⟩

              evalTactic (← `(tactic| rw [<- $hcIdent]))
              evalTactic (← `(tactic| translate_hypothesis $hcIdent [$hs,*] [] $flagStx ))
              let mut progress := true
              while (progress ) do
                try
                  evalTactic (← `(tactic|  rw [$hcRw ]))
                catch e  =>
                  --logInfo m!"{e.toMessageData}"
                  progress := false
              evalTactic (← `(tactic|  try simp [$hcIdStx]))
        loopUntilDone flag hs (count +1)

            --         goal := newGoal
            -- let hcPf <- mkEqRefl big
          -- let g ← getMainGoal
          -- let (k,g') ← g.note `hc hcTy hcPf
          --replaceMainGoal [newGoal]
        --evalTactic (← `(tactic| focus let kc := $(ifSyn) ))

      -- -- Call your custom tactic on it
      --   evalTactic (← `(tactic| translate_hypothesis hc [$hs,*] [] $flagStx ))

      -- --     -- -- Simplify the goal using this new equality
      --   evalTactic (← `(tactic|  try simp [hc]))

      --     -- -- Recurse on updated goal


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
  --evalTactic (← `(tactic| try rw [sub_add_right_recursive_paren_r] ))
  while (mLoop) do
    try
      evalTactic (← `(tactic| rw [sub_add_right_recursive]))

     --evalTactic (← `(tactic| rw [sub_add_right_recursive]))
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

            evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$ids],*]))
            let after ← getGoals
            if after.isEmpty then
              setGoals ([g_one] ++ rest_rev)
              evalTactic (← `(tactic| try valify [$[$sargs],*]))
            else
              throwError "lemma application did not solve goal"

      catch e =>
        --logInfo m!"{e.toMessageData}"
        try
          evalTactic (← `(tactic| rw [ZMod.val_sub_strict]))
          evalTactic (← `(tactic| try valify [$[$sargs],*]))
        catch e =>
         -- logInfo m!"{e.toMessageData}"
          progress := false
     -- evalTactic (← `(tactic| try valify [$[$sargs],*]))

  -- --l--ogInfo m! "HERE?"
  evalTactic (← `(tactic| try simp  ) )

  let goals <- getGoals
  if goals.isEmpty then
    logInfo m!"SOLVED"
    return
  -- --- FOR DEBUGGING REMOVE LATER PLEASE

  let m <- CalcBitWidth (<-goals[0]!.getType) ids
  --let bitsize :=  ceilLog2 (2^512)
  --logInfo m!"FIRST  {m}"
  let bitsize := ceilLog2 (Nat.max (m+1) 4)
  let bitsize_full := Nat.pow 2 bitsize
  let bitsizeStx : TSyntax `term := Syntax.mkNumLit (toString bitsize)
  let bitsizeStx_full : TSyntax `num := Syntax.mkNumLit (toString bitsize_full)

  logInfo m!"BIT SIZE {bitsize} with {m}"
  let mut rmFailed := false
  try
      evalTactic (← `(tactic| dbg_mod $bitsizeStx_full [$[$ids],*]))
      -- let hcTerm  : TSyntax `term  := ⟨mkIdent `proof⟩
      -- evalTactic (← `(tactic|  rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
      -- evalTactic (← `(tactic| swap ))
      -- evalTactic (← `(tactic| focus try_apply_lemma_hyps [$[$ids],*]))
      -- evalTactic (← `(tactic| swap ))
      -- evalTactic (← `(tactic| apply $hcTerm))

        -- evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt]))
        -- let cur_g ← getGoals
        -- match cur_g with
        -- | [] =>
        --     throwError "❌ No goals after Nat.mod_eq_of_lt"
        -- | _ :: []  =>
        --     throwError "❌ wrong number of goals left after Nat.mod_eq_of_lt"
        -- | g_one :: g_last :: rest_rev => do
        --     setGoals [g_last]
        --     evalTactic (← `(tactic| try try_apply_lemma_hyps [$[$ids],*]))
        --     let after ← getGoals
        --     if after.isEmpty then
        --       setGoals ( [g_one ] ++ rest_rev )
        --       evalTactic (← `(tactic| try bvify [$[$sargs],*]))

        --     else
        --       throwError m! "try_apply failed {after}"
  catch e =>
      --logInfo m!"{e.toMessageData}"
      pure ()
      --rmFailed := true


  evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
  evalTactic (← `(tactic| try bvify [$[$sargs],*]))
  loopUntilDone flag ids (count+1)
  -- --let n := countAnds t + k
  -- logInfo m!"ORS: k & MIN :i"
  for _ in [:k] do
      evalTactic (← `(tactic| try rw [BVModEq.BitVec_ofNat_eq_iff $bitsizeStx ]))
      evalTactic (← `(tactic| try bvify [$[$sargs],*]))

  let mut modLeft := true
  subLoop := true
  while (subLoop ) do
      count :=count + 1
      -- if rmFailed then
      --   throwError "We already tried removal"
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
           --logInfo m!"WHY {e.toMessageData}"
           try
             evalTactic (← `(tactic| rw  [Mathlib.Tactic.BVify.BitVec.ofNat_sub]))
             evalTactic (← `(tactic| try bvify [$[$sargs],*]))
            catch _ =>
              subLoop := false
  evalTactic (← `(tactic| try simp  ))









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
    evalTactic (← `(tactic| try simp only [and_assoc] at $(mkIdent h.getId):ident ))
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
                        (varToHypRef : IO.Ref (Std.HashMap FVarId (TSyntax `ident))): TacticM ( Option (TSyntax `ident) × Option (TSyntax `ident ) × Option (TSyntax `ident ) × Option (TSyntax `ident)) := do
    withMainContext do
    -- Retrieve hypothesis declaration safely

    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError m!"no hypothesis `{h.getId}` in local context"

    let hIdent : TSyntax `ident := mkIdent decl.userName
    --logInfo m! "We are here?"
    let hType ← whnf decl.type
    match isZModIdemEq hType with
    | some _ => do
        --logInfo m! "we are we not here..."
        evalTactic (← `(tactic| rw [BVModEq.square_eq_one_zero 256] at $(mkIdent h.getId):ident))
        -- name parts as h_1 / h_2
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


                --evalTactic (← `(tactic| translate_hypothesis $h))

                -- in-place update:
                let m ← varToHypRef.get
                if m.contains rhsVarId then
                  return (none ,none, none, some h)
                else
                  varToHypRef.modify fun m => m.insert rhsVarId newName
                  -- if extraArgs.isEmpty then
                  --   evalTactic (← `(tactic| translate_hypothesis $h))

                  -- else
                  --   evalTactic (← `(tactic| translate_hypothesis $h [$$extraArgs,*]))
                  return (none ,none, some newName, some h)
              catch _ => pure ()
          | _ => --pure ()
          try
            evalTactic (← `(tactic| rw [BVModEq.extract_bv_rel] at $(mkIdent h.getId):ident))
            -- evalTactic (← `(tactic|  rw [BVModEq.map_f_to_bv] at $(mkIdent h.getId):ident))
            let h1 := mkIdent (Name.mkSimple s!"{h.getId}_1")
            let h2 := mkIdent (Name.mkSimple s!"{h.getId}_2")
            --evalTactic (← `(tactic| simp at $(mkIdent h.getId):ident))
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
              evalTactic (← `(tactic| rw [BVModEq.extract_bv_leq] at $h1:ident))

              return (some newName, some h1, none, none)
            catch e =>
                pure ()
                --logInfo m!"{e.toMessageData}"


       return (none, none, none, some h)


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


-- If we got a k, push it
    match k? with
    | some k => picked := picked.push k
    | none   => pure ()

    match x? with
    | some x => changed := changed.push x
    | none   => pure ()


    -- If we got a w, translate the hypothesis
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
  evalTactic (← `(tactic| try simp [-one_mul, -mul_one]))
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
  let ( collected, changed) := (← smartTranslateMany ids sargs varToHypRef flag)

  --colected := collected ++ changed
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
  let bitblast :=
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
              -- evalTactic (← `(tactic| try simp only [BitVec.setWidth] at $(mkIdent hyp.getId):ident))
          catch _ =>
            rw := false
        try
          evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))
      -- else
      --   logInfo m!"NO BV DECIDE {fn}"
        catch _ =>

          --THIS IS NEEDED FOR JOLT BUT NOT CIRC WE SHOULD FIND A WAY TO ABSTRACT THIS
          let mut index :=0
          let fv1T : TSyntax `term := (← termFor `fv1)
          let fv2T : TSyntax `term := (← termFor `fv2)
          while index < collected.size/2 do

            -- names for the bound and its equality
            let idName  := Name.mkSimple s!"b0_{index}"

            -- identifiers/syntax nodes
            let idSyn   : TSyntax `ident := mkIdent idName
            let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

            -- safest access: .get! (parses reliably inside quotations)
            evalTactic (← `(tactic|
              set $idSyn := $fv1T[$idxSyn]
            ))
            index := index + 1
          index := 0
          while index < collected.size/2 do
            -- names for the bound and its equality
            let idName  := Name.mkSimple s!"b1_{index}"

            -- identifiers/syntax nodes
            let idSyn   : TSyntax `ident := mkIdent idName
            let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

            -- safest access: .get! (parses reliably inside quotations)
            evalTactic (← `(tactic|
              set $idSyn := $fv2T[$idxSyn]
            ))
            index := index + 1
          evalTactic (← `(tactic| bv_decide (config := {timeout := 300})))

    -- --logInfo m! "Collected {collected}"
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






-- MAYBE FIX IF YOU WANT TO
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (a : BitVec 11)
-- lemma correct :
-- ((((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ ((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (32 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (64 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (128 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (256 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (1024 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)))) ∧ ((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[6]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[7]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[8]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[9]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((if (((BVModEq.bool_to_bv 1 a[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 11  (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))[10]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))
--  := by
--    translate_all [] false
--    translate_hypothesis hc0 [] [] false
--    let j :BitVec 11 := BitVec.ofNat 11 (a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513)
--    have h :j = BitVec.ofNat 11 (a.toNat % 52435875175126190479447740508185965837690552500527637822603658699938581184513) := by sorry
--    simp [<-h]
--    rw [Nat.mod_eq_of_lt] at h
--    simp [h]
--    rw [Nat.mod_eq_of_lt]




-- lemma BitVec.ofNat_sub  {bw x y : ℕ}  (h : y ≥ x)  (h2: y < 2 ^ bw)  :
--   BitVec.ofNat bw (y - x) = (BitVec.ofNat bw y) - (BitVec.ofNat bw x) := by sorry


--   -- bv_decide (config := {timeout := 300})
--   focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1,
--   h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
--   h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
--   h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
--   h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
--   h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
--   h60_1, h61_1, h62_1, h63_1, h64_1]

--   focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1,
--   h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
--   h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
--   h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
--   h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
--   h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
--   h60_1, h61_1, h62_1, h63_1, h64_1]
  -- focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1,
  -- h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
  -- h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
  -- h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
  -- h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
  -- h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
  -- h60_1, h61_1, h62_1, h63_1, h64_1]

  -- rw [Nat.mod_eq_of_lt]
  -- swap
  -- sorry
  -- bvify [h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
  -- h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
  -- h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
  -- h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
  -- h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
  -- h60_1, h61_1, h62_1, h63_1, h64_1]
  -- simp

-- set_option maxRecDepth 1048576
-- set_option maxHeartbeats  20000000000000000000
-- set_option exponentiation.threshold 900
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- abbrev f := FF0

-- def VirtualAssertLTE_32 [Field f] : Subtable f 64 :=
--   subtableFromMLE (fun x => 0 + (1 - x[0])*x[1]*1 + (1 - x[2])*x[3]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1])) + (1 - x[4])*x[5]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3])) + (1 - x[6])*x[7]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5])) + (1 - x[8])*x[9]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7])) + (1 - x[10])*x[11]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9])) + (1 - x[12])*x[13]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11])) + (1 - x[14])*x[15]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13])) + (1 - x[16])*x[17]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15])) + (1 - x[18])*x[19]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17])) + (1 - x[20])*x[21]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19])) + (1 - x[22])*x[23]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21])) + (1 - x[24])*x[25]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23])) + (1 - x[26])*x[27]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25])) + (1 - x[28])*x[29]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27])) + (1 - x[30])*x[31]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29])) + (1 - x[32])*x[33]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31])) + (1 - x[34])*x[35]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33])) + (1 - x[36])*x[37]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35])) + (1 - x[38])*x[39]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37])) + (1 - x[40])*x[41]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39])) + (1 - x[42])*x[43]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41])) + (1 - x[44])*x[45]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43])) + (1 - x[46])*x[47]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45])) + (1 - x[48])*x[49]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47])) + (1 - x[50])*x[51]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49])) + (1 - x[52])*x[53]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51])) + (1 - x[54])*x[55]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53])) + (1 - x[56])*x[57]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55])) + (1 - x[58])*x[59]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57])) + (1 - x[60])*x[61]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59])) + (1 - x[62])*x[63]*1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61])) + 1*(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61]))*(x[62]*x[63] + (1 - x[62])*(1 - x[63])))


-- lemma assert_lte_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
--   some bvoutput = BVModEq.map_f_to_bv 32 foutput ->
--    some (BVModEq.bool_to_bv 32 bv1[31])  = BVModEq.map_f_to_bv 32 fv1[0]  ->
--    some (BVModEq.bool_to_bv 32 bv2[31]) = BVModEq.map_f_to_bv 32 fv1[1]  ->
--    some (BVModEq.bool_to_bv 32 bv1[30]) = BVModEq.map_f_to_bv 32 fv1[2]  ->
--    some (BVModEq.bool_to_bv 32 bv2[30]) = BVModEq.map_f_to_bv 32 fv1[3]  ->
--    some (BVModEq.bool_to_bv 32 bv1[29]) = BVModEq.map_f_to_bv 32 fv1[4]  ->
--    some (BVModEq.bool_to_bv 32 bv2[29]) = BVModEq.map_f_to_bv 32 fv1[5]  ->
--    some (BVModEq.bool_to_bv 32 bv1[28]) = BVModEq.map_f_to_bv 32 fv1[6]  ->
--    some (BVModEq.bool_to_bv 32 bv2[28]) = BVModEq.map_f_to_bv 32 fv1[7]  ->
--    some (BVModEq.bool_to_bv 32 bv1[27])  = BVModEq.map_f_to_bv 32 fv1[8]  ->
--    some (BVModEq.bool_to_bv 32 bv2[27]) = BVModEq.map_f_to_bv 32 fv1[9]  ->
--    some (BVModEq.bool_to_bv 32 bv1[26]) = BVModEq.map_f_to_bv 32 fv1[10]  ->
--    some (BVModEq.bool_to_bv 32 bv2[26]) = BVModEq.map_f_to_bv 32 fv1[11]  ->
--    some (BVModEq.bool_to_bv 32 bv1[25]) = BVModEq.map_f_to_bv 32 fv1[12]  ->
--    some (BVModEq.bool_to_bv 32 bv2[25]) = BVModEq.map_f_to_bv 32 fv1[13]  ->
--    some (BVModEq.bool_to_bv 32 bv1[24]) = BVModEq.map_f_to_bv 32 fv1[14]  ->
--    some (BVModEq.bool_to_bv 32 bv2[24]) = BVModEq.map_f_to_bv 32 fv1[15]  ->
--    some (BVModEq.bool_to_bv 32 bv1[23])  = BVModEq.map_f_to_bv 32 fv1[16]  ->
--    some (BVModEq.bool_to_bv 32 bv2[23]) = BVModEq.map_f_to_bv 32 fv1[17]  ->
--    some (BVModEq.bool_to_bv 32 bv1[22]) = BVModEq.map_f_to_bv 32 fv1[18]  ->
--    some (BVModEq.bool_to_bv 32 bv2[22]) = BVModEq.map_f_to_bv 32 fv1[19]  ->
--    some (BVModEq.bool_to_bv 32 bv1[21]) = BVModEq.map_f_to_bv 32 fv1[20]  ->
--    some (BVModEq.bool_to_bv 32 bv2[21]) = BVModEq.map_f_to_bv 32 fv1[21]  ->
--    some (BVModEq.bool_to_bv 32 bv1[20]) = BVModEq.map_f_to_bv 32 fv1[22]  ->
--    some (BVModEq.bool_to_bv 32 bv2[20]) = BVModEq.map_f_to_bv 32 fv1[23]  ->
--    some (BVModEq.bool_to_bv 32 bv1[19])  = BVModEq.map_f_to_bv 32 fv1[24]  ->
--    some (BVModEq.bool_to_bv 32 bv2[19]) = BVModEq.map_f_to_bv 32 fv1[25]  ->
--    some (BVModEq.bool_to_bv 32 bv1[18]) = BVModEq.map_f_to_bv 32 fv1[26]  ->
--    some (BVModEq.bool_to_bv 32 bv2[18]) = BVModEq.map_f_to_bv 32 fv1[27]  ->
--    some (BVModEq.bool_to_bv 32 bv1[17]) = BVModEq.map_f_to_bv 32 fv1[28]  ->
--    some (BVModEq.bool_to_bv 32 bv2[17]) = BVModEq.map_f_to_bv 32 fv1[29]  ->
--    some (BVModEq.bool_to_bv 32 bv1[16]) = BVModEq.map_f_to_bv 32 fv1[30]  ->
--    some (BVModEq.bool_to_bv 32 bv2[16]) = BVModEq.map_f_to_bv 32 fv1[31]  ->
--   some (BVModEq.bool_to_bv 32 bv1[15])  = BVModEq.map_f_to_bv 32 fv2[0]  ->
--    some (BVModEq.bool_to_bv 32 bv2[15]) = BVModEq.map_f_to_bv 32 fv2[1]  ->
--    some (BVModEq.bool_to_bv 32 bv1[14]) = BVModEq.map_f_to_bv 32 fv2[2]  ->
--    some (BVModEq.bool_to_bv 32 bv2[14]) = BVModEq.map_f_to_bv 32 fv2[3]  ->
--    some (BVModEq.bool_to_bv 32 bv1[13]) = BVModEq.map_f_to_bv 32 fv2[4]  ->
--    some (BVModEq.bool_to_bv 32 bv2[13]) = BVModEq.map_f_to_bv 32 fv2[5]  ->
--    some (BVModEq.bool_to_bv 32 bv1[12]) = BVModEq.map_f_to_bv 32 fv2[6]  ->
--    some (BVModEq.bool_to_bv 32 bv2[12]) = BVModEq.map_f_to_bv 32 fv2[7]  ->
--   some (BVModEq.bool_to_bv 32 bv1[11]) = BVModEq.map_f_to_bv 32 fv2[8]  ->
--   some (BVModEq.bool_to_bv 32 bv2[11]) = BVModEq.map_f_to_bv 32 fv2[9]  ->
--   some (BVModEq.bool_to_bv 32 bv1[10]) = BVModEq.map_f_to_bv 32  fv2[10]  ->
--   some (BVModEq.bool_to_bv 32 bv2[10]) = BVModEq.map_f_to_bv 32 fv2[11]  ->
--   some (BVModEq.bool_to_bv 32 bv1[9]) = BVModEq.map_f_to_bv 32 fv2[12]  ->
--   some (BVModEq.bool_to_bv 32 bv2[9]) = BVModEq.map_f_to_bv 32 fv2[13]  ->
--   some (BVModEq.bool_to_bv 32 bv1[8]) = BVModEq.map_f_to_bv 32 fv2[14]  ->
--   some (BVModEq.bool_to_bv 32 bv2[8]) = BVModEq.map_f_to_bv 32 fv2[15]  ->
--    some (BVModEq.bool_to_bv 32 bv1[7])  = BVModEq.map_f_to_bv 32 fv2[16]  ->
--    some (BVModEq.bool_to_bv 32 bv2[7]) = BVModEq.map_f_to_bv 32 fv2[17]  ->
--    some (BVModEq.bool_to_bv 32 bv1[6]) = BVModEq.map_f_to_bv 32 fv2[18]  ->
--    some (BVModEq.bool_to_bv 32 bv2[6]) = BVModEq.map_f_to_bv 32 fv2[19]  ->
--    some (BVModEq.bool_to_bv 32 bv1[5]) = BVModEq.map_f_to_bv 32 fv2[20]  ->
--    some (BVModEq.bool_to_bv 32 bv2[5]) = BVModEq.map_f_to_bv 32 fv2[21]  ->
--    some (BVModEq.bool_to_bv 32 bv1[4]) = BVModEq.map_f_to_bv 32 fv2[22]  ->
--    some (BVModEq.bool_to_bv 32 bv2[4]) = BVModEq.map_f_to_bv 32 fv2[23]  ->
--   some (BVModEq.bool_to_bv 32 bv1[3]) = BVModEq.map_f_to_bv 32 fv2[24]  ->
--   some (BVModEq.bool_to_bv 32 bv2[3]) = BVModEq.map_f_to_bv 32 fv2[25]  ->
--   some (BVModEq.bool_to_bv 32 bv1[2]) = BVModEq.map_f_to_bv 32  fv2[26]  ->
--   some (BVModEq.bool_to_bv 32 bv2[2]) = BVModEq.map_f_to_bv 32 fv2[27]  ->
--   some (BVModEq.bool_to_bv 32 bv1[1]) = BVModEq.map_f_to_bv 32 fv2[28]  ->
--   some (BVModEq.bool_to_bv 32 bv2[1]) = BVModEq.map_f_to_bv 32 fv2[29]  ->
--   some (BVModEq.bool_to_bv 32 bv1[0]) = BVModEq.map_f_to_bv 32 fv2[30]  ->
--   some (BVModEq.bool_to_bv 32 bv2[0]) = BVModEq.map_f_to_bv 32 fv2[31]  ->
--   (bvoutput = BVModEq.bool_to_bv 32 (bv1 <= bv2))
--   =
--   (foutput = evalSubtable VirtualAssertLTE_32 (Vector.append fv1 fv2))
-- := by
--   unfold VirtualAssertLTE_32
--   unfold evalSubtable
--   unfold subtableFromMLE
--   unfold Vector.append

--   translate_all false
--   rw [Nat.mod_eq_of_lt]
--   swap
--   focus try_apply_lemma_hyps [
--   h0_new,
--   h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1,
--   h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
--   h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
--   h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
--   h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
--   h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
--   h60_1, h61_1, h62_1, h63_1, h64_1
--   ]



-- set_option maxHeartbeats  20000000000000000000
-- set_option exponentiation.threshold 900
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- abbrev f := FF0
-- def OR_64 [Field f] : Subtable f 64 :=
--   subtableFromMLE (fun x => 0 + 2147483648*(x[0] + x[1] - x[0]*x[1]) + 1073741824*(x[2] + x[3] - x[2]*x[3]) + 536870912*(x[4] + x[5] - x[4]*x[5]) + 268435456*(x[6] + x[7] - x[6]*x[7]) + 134217728*(x[8] + x[9] - x[8]*x[9]) + 67108864*(x[10] + x[11] - x[10]*x[11]) + 33554432*(x[12] + x[13] - x[12]*x[13]) + 16777216*(x[14] + x[15] - x[14]*x[15]) + 8388608*(x[16] + x[17] - x[16]*x[17]) + 4194304*(x[18] + x[19] - x[18]*x[19]) + 2097152*(x[20] + x[21] - x[20]*x[21]) + 1048576*(x[22] + x[23] - x[22]*x[23]) + 524288*(x[24] + x[25] - x[24]*x[25]) + 262144*(x[26] + x[27] - x[26]*x[27]) + 131072*(x[28] + x[29] - x[28]*x[29]) + 65536*(x[30] + x[31] - x[30]*x[31]) + 32768*(x[32] + x[33] - x[32]*x[33]) + 16384*(x[34] + x[35] - x[34]*x[35]) + 8192*(x[36] + x[37] - x[36]*x[37]) + 4096*(x[38] + x[39] - x[38]*x[39]) + 2048*(x[40] + x[41] - x[40]*x[41]) + 1024*(x[42] + x[43] - x[42]*x[43]) + 512*(x[44] + x[45] - x[44]*x[45]) + 256*(x[46] + x[47] - x[46]*x[47]) + 128*(x[48] + x[49] - x[48]*x[49]) + 64*(x[50] + x[51] - x[50]*x[51]) + 32*(x[52] + x[53] - x[52]*x[53]) + 16*(x[54] + x[55] - x[54]*x[55]) + 8*(x[56] + x[57] - x[56]*x[57]) + 4*(x[58] + x[59] - x[58]*x[59]) + 2*(x[60] + x[61] - x[60]*x[61]) + 2^0*(x[62] + x[63] - x[62]*x[63]))

-- def OR_8  : Subtable FF0 16 :=
--   subtableFromMLE (fun x => 0+2^0*((x[15] + x[7] - x[15]*x[7])) + 2*(x[14] + x[6] - x[14]*x[6]) + 4*(x[13] + x[5] - x[13]*x[5]) + 8*(x[12] + x[4] - x[12]*x[4]) + 16*(x[11] + x[3] - x[11]*x[3]) + 32*(x[10] + x[2] - x[10]*x[2]) + 64*(x[9] + x[1] - x[9]*x[1]) + 128*(x[8] + x[0] - x[8]*x[0]))

-- lemma or_mle_8_chunk
--   (bv1 bv2 : BitVec 8)
--   (fv1 fv2 : Vector FF0 8) :
--   some bvoutput = BVModEq.map_f_to_bv 8 foutput ->
--   some (BVModEq.bool_to_bv 8 bv1[7]) = BVModEq.map_f_to_bv 8 fv1[0]  ->
--   some (BVModEq.bool_to_bv 8 bv1[6]) = BVModEq.map_f_to_bv 8 fv1[1]  ->
--   some (BVModEq.bool_to_bv 8 bv1[5]) = BVModEq.map_f_to_bv 8 fv1[2]  ->
--   some (BVModEq.bool_to_bv 8 bv1[4]) = BVModEq.map_f_to_bv 8 fv1[3]  ->
--   some (BVModEq.bool_to_bv 8 bv1[3]) = BVModEq.map_f_to_bv 8 fv1[4]  ->
--   some (BVModEq.bool_to_bv 8 bv1[2]) = BVModEq.map_f_to_bv 8 fv1[5]  ->
--   some (BVModEq.bool_to_bv 8 bv1[1]) = BVModEq.map_f_to_bv 8 fv1[6]  ->
--   some (BVModEq.bool_to_bv 8 bv1[0]) = BVModEq.map_f_to_bv 8 fv1[7]  ->
--   some (BVModEq.bool_to_bv 8 bv2[7]) = BVModEq.map_f_to_bv 8 fv2[0]  ->
--   some (BVModEq.bool_to_bv 8 bv2[6]) = BVModEq.map_f_to_bv 8 fv2[1]  ->
--   some (BVModEq.bool_to_bv 8 bv2[5]) = BVModEq.map_f_to_bv 8 fv2[2]  ->
--   some (BVModEq.bool_to_bv 8 bv2[4]) = BVModEq.map_f_to_bv 8 fv2[3]  ->
--   some (BVModEq.bool_to_bv 8 bv2[3]) = BVModEq.map_f_to_bv 8 fv2[4]  ->
--   some (BVModEq.bool_to_bv 8 bv2[2]) = BVModEq.map_f_to_bv 8 fv2[5]  ->
--   some (BVModEq.bool_to_bv 8 bv2[1]) = BVModEq.map_f_to_bv 8 fv2[6]  ->
--   some (BVModEq.bool_to_bv 8 bv2[0]) = BVModEq.map_f_to_bv 8 fv2[7]  ->
--   (bvoutput = (BitVec.or bv1 bv2))
--   =
--   (foutput = evalSubtable OR_8 (Vector.append fv1 fv2))
-- := by
--   unfold OR_8
--   unfold evalSubtable
--   unfold subtableFromMLE
--   unfold Vector.append
--   translate_all false



-- lemma or_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
--   some bvoutput = BVModEq.map_f_to_bv 32 foutput ->
--    some (BVModEq.bool_to_bv 32 bv1[31])  = BVModEq.map_f_to_bv 32 fv1[0]  ->
--    some (BVModEq.bool_to_bv 32 bv2[31]) = BVModEq.map_f_to_bv 32 fv1[1]  ->
--    some (BVModEq.bool_to_bv 32 bv1[30]) = BVModEq.map_f_to_bv 32 fv1[2]  ->
--    some (BVModEq.bool_to_bv 32 bv2[30]) = BVModEq.map_f_to_bv 32 fv1[3]  ->
--    some (BVModEq.bool_to_bv 32 bv1[29]) = BVModEq.map_f_to_bv 32 fv1[4]  ->
--    some (BVModEq.bool_to_bv 32 bv2[29]) = BVModEq.map_f_to_bv 32 fv1[5]  ->
--    some (BVModEq.bool_to_bv 32 bv1[28]) = BVModEq.map_f_to_bv 32 fv1[6]  ->
--    some (BVModEq.bool_to_bv 32 bv2[28]) = BVModEq.map_f_to_bv 32 fv1[7]  ->
--    some (BVModEq.bool_to_bv 32 bv1[27])  = BVModEq.map_f_to_bv 32 fv1[8]  ->
--    some (BVModEq.bool_to_bv 32 bv2[27]) = BVModEq.map_f_to_bv 32 fv1[9]  ->
--    some (BVModEq.bool_to_bv 32 bv1[26]) = BVModEq.map_f_to_bv 32 fv1[10]  ->
--    some (BVModEq.bool_to_bv 32 bv2[26]) = BVModEq.map_f_to_bv 32 fv1[11]  ->
--    some (BVModEq.bool_to_bv 32 bv1[25]) = BVModEq.map_f_to_bv 32 fv1[12]  ->
--    some (BVModEq.bool_to_bv 32 bv2[25]) = BVModEq.map_f_to_bv 32 fv1[13]  ->
--    some (BVModEq.bool_to_bv 32 bv1[24]) = BVModEq.map_f_to_bv 32 fv1[14]  ->
--    some (BVModEq.bool_to_bv 32 bv2[24]) = BVModEq.map_f_to_bv 32 fv1[15]  ->
--    some (BVModEq.bool_to_bv 32 bv1[23])  = BVModEq.map_f_to_bv 32 fv1[16]  ->
--    some (BVModEq.bool_to_bv 32 bv2[23]) = BVModEq.map_f_to_bv 32 fv1[17]  ->
--    some (BVModEq.bool_to_bv 32 bv1[22]) = BVModEq.map_f_to_bv 32 fv1[18]  ->
--    some (BVModEq.bool_to_bv 32 bv2[22]) = BVModEq.map_f_to_bv 32 fv1[19]  ->
--    some (BVModEq.bool_to_bv 32 bv1[21]) = BVModEq.map_f_to_bv 32 fv1[20]  ->
--    some (BVModEq.bool_to_bv 32 bv2[21]) = BVModEq.map_f_to_bv 32 fv1[21]  ->
--    some (BVModEq.bool_to_bv 32 bv1[20]) = BVModEq.map_f_to_bv 32 fv1[22]  ->
--    some (BVModEq.bool_to_bv 32 bv2[20]) = BVModEq.map_f_to_bv 32 fv1[23]  ->
--    some (BVModEq.bool_to_bv 32 bv1[19])  = BVModEq.map_f_to_bv 32 fv1[24]  ->
--    some (BVModEq.bool_to_bv 32 bv2[19]) = BVModEq.map_f_to_bv 32 fv1[25]  ->
--    some (BVModEq.bool_to_bv 32 bv1[18]) = BVModEq.map_f_to_bv 32 fv1[26]  ->
--    some (BVModEq.bool_to_bv 32 bv2[18]) = BVModEq.map_f_to_bv 32 fv1[27]  ->
--    some (BVModEq.bool_to_bv 32 bv1[17]) = BVModEq.map_f_to_bv 32 fv1[28]  ->
--    some (BVModEq.bool_to_bv 32 bv2[17]) = BVModEq.map_f_to_bv 32 fv1[29]  ->
--    some (BVModEq.bool_to_bv 32 bv1[16]) = BVModEq.map_f_to_bv 32 fv1[30]  ->
--    some (BVModEq.bool_to_bv 32 bv2[16]) = BVModEq.map_f_to_bv 32 fv1[31]  ->
--   some (BVModEq.bool_to_bv 32 bv1[15])  = BVModEq.map_f_to_bv 32 fv2[0]  ->
--    some (BVModEq.bool_to_bv 32 bv2[15]) = BVModEq.map_f_to_bv 32 fv2[1]  ->
--    some (BVModEq.bool_to_bv 32 bv1[14]) = BVModEq.map_f_to_bv 32 fv2[2]  ->
--    some (BVModEq.bool_to_bv 32 bv2[14]) = BVModEq.map_f_to_bv 32 fv2[3]  ->
--    some (BVModEq.bool_to_bv 32 bv1[13]) = BVModEq.map_f_to_bv 32 fv2[4]  ->
--    some (BVModEq.bool_to_bv 32 bv2[13]) = BVModEq.map_f_to_bv 32 fv2[5]  ->
--    some (BVModEq.bool_to_bv 32 bv1[12]) = BVModEq.map_f_to_bv 32 fv2[6]  ->
--    some (BVModEq.bool_to_bv 32 bv2[12]) = BVModEq.map_f_to_bv 32 fv2[7]  ->
--   some (BVModEq.bool_to_bv 32 bv1[11]) = BVModEq.map_f_to_bv 32 fv2[8]  ->
--   some (BVModEq.bool_to_bv 32 bv2[11]) = BVModEq.map_f_to_bv 32 fv2[9]  ->
--   some (BVModEq.bool_to_bv 32 bv1[10]) = BVModEq.map_f_to_bv 32  fv2[10]  ->
--   some (BVModEq.bool_to_bv 32 bv2[10]) = BVModEq.map_f_to_bv 32 fv2[11]  ->
--   some (BVModEq.bool_to_bv 32 bv1[9]) = BVModEq.map_f_to_bv 32 fv2[12]  ->
--   some (BVModEq.bool_to_bv 32 bv2[9]) = BVModEq.map_f_to_bv 32 fv2[13]  ->
--   some (BVModEq.bool_to_bv 32 bv1[8]) = BVModEq.map_f_to_bv 32 fv2[14]  ->
--   some (BVModEq.bool_to_bv 32 bv2[8]) = BVModEq.map_f_to_bv 32 fv2[15]  ->
--    some (BVModEq.bool_to_bv 32 bv1[7])  = BVModEq.map_f_to_bv 32 fv2[16]  ->
--    some (BVModEq.bool_to_bv 32 bv2[7]) = BVModEq.map_f_to_bv 32 fv2[17]  ->
--    some (BVModEq.bool_to_bv 32 bv1[6]) = BVModEq.map_f_to_bv 32 fv2[18]  ->
--    some (BVModEq.bool_to_bv 32 bv2[6]) = BVModEq.map_f_to_bv 32 fv2[19]  ->
--    some (BVModEq.bool_to_bv 32 bv1[5]) = BVModEq.map_f_to_bv 32 fv2[20]  ->
--    some (BVModEq.bool_to_bv 32 bv2[5]) = BVModEq.map_f_to_bv 32 fv2[21]  ->
--    some (BVModEq.bool_to_bv 32 bv1[4]) = BVModEq.map_f_to_bv 32 fv2[22]  ->
--    some (BVModEq.bool_to_bv 32 bv2[4]) = BVModEq.map_f_to_bv 32 fv2[23]  ->
--   some (BVModEq.bool_to_bv 32 bv1[3]) = BVModEq.map_f_to_bv 32 fv2[24]  ->
--   some (BVModEq.bool_to_bv 32 bv2[3]) = BVModEq.map_f_to_bv 32 fv2[25]  ->
--   some (BVModEq.bool_to_bv 32 bv1[2]) = BVModEq.map_f_to_bv 32  fv2[26]  ->
--   some (BVModEq.bool_to_bv 32 bv2[2]) = BVModEq.map_f_to_bv 32 fv2[27]  ->
--   some (BVModEq.bool_to_bv 32 bv1[1]) = BVModEq.map_f_to_bv 32 fv2[28]  ->
--   some (BVModEq.bool_to_bv 32 bv2[1]) = BVModEq.map_f_to_bv 32 fv2[29]  ->
--   some (BVModEq.bool_to_bv 32 bv1[0]) = BVModEq.map_f_to_bv 32 fv2[30]  ->
--   some (BVModEq.bool_to_bv 32 bv2[0]) = BVModEq.map_f_to_bv 32 fv2[31]  ->
--   (bvoutput = (BitVec.or bv1 bv2))
--   =
--   (foutput = evalSubtable OR_64 (Vector.append fv1 fv2))
-- := by
--   unfold OR_64
--   unfold evalSubtable
--   unfold subtableFromMLE
--   unfold Vector.append
--   translate_all false



   --simp

  --  swap
  --  valify [
  -- h0_new,
  -- h1_1, h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1,
  -- h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h18_1, h19_1,
  -- h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1,
  -- h30_1, h31_1, h32_1, h33_1, h34_1, h35_1, h36_1, h37_1, h38_1, h39_1,
  -- h40_1, h41_1, h42_1, h43_1, h44_1, h45_1, h46_1, h47_1, h48_1, h49_1,
  -- h50_1, h51_1, h52_1, h53_1, h54_1, h55_1, h56_1, h57_1, h58_1, h59_1,
  -- h60_1, h61_1, h62_1, h63_1, h64_1
  -- ]
  --  simp
  --  rw [Nat.mod_eq_of_lt]
  --  rw [Nat.mod_eq_of_lt]








  -- rw [Nat.mod_eq_of_lt] --focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1,h7_1,h8_1,h9_1,h10_1,h11_1,h12_1,h13_1,h14_1, h15_1, h16_1]
  -- focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1,h7_1,h8_1,h9_1,h10_1,h11_1,h12_1,h13_1,h14_1, h15_1, h16_1]
  -- focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1,h7_1,h8_1,h9_1,h10_1,h11_1,h12_1,h13_1,h14_1, h15_1, h16_1]

  --focus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1,h7_1,h8_1,h9_1,h10_1,h11_1,h12_1,h13_1,h14_1, h15_1, h16_1]
  --f--ocus try_apply_lemma_hyps [h0_new, h1_1, h2_1, h3_1, h4_1, h5_1, h6_1,h7_1,h8_1,h9_1,h10_1,h11_1,h12_1,h13_1,h14_1, h15_1, h16_1]




  -- focus try_apply_lemma_hyps [h0_new, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9,h1_10,h1_11,h1_12,h1_13,h1_14,h1_15,h1_16]

  -- all_goals sorry

--   --rw [map_f_to_bv_circ_spec]
--   simp
--   translate_goal [] false
--   let k := BitVec.ofNat 3
--       (((((if a[1] = true then 2 else 0) + if b[0] = true then 1 else 0) + 4) %
--             52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--           if a[0] = true then 1 else 0) -
--         if b[1] = true then 2 else 0)
--   have hc : k = BitVec.ofNat 3 (((((if a[1] = true then 2 else 0) + if b[0] = true then 1 else 0) + 4) %
--             52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--           if a[0] = true then 1 else 0) -
--         if b[1] = true then 2 else 0) := by rfl
--   simp [<- hc]
--   translate_hypothesis hc [] [] false
--   simp [hc]
--   rw [Nat.mod_eq_of_lt]
--   --sorry
--   swap
--   focus
--     try_apply_lemma_hyps []
--     split_ifs
--     all_goals simp


    --rw [Nat.mod_eq_of_lt]

--   focus try_apply_lemma_hyps []
--   sorry
--   focus try_apply_lemma_hyps []

--   by_cases h : (BitVec.ofNat 3
--                   (((((if a[1] = true then 2 else 0) + if b[0] = true then 1 else 0) + 4) %
--                         52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                       if a[0] = true then 1 else 0) -
--                     if b[1] = true then 2 else 0))[0] =
--               true
--   all_goals try simp [h]
--   all_goals by_cases h1: (BitVec.ofNat 3
--                   (((((if a[1] = true then 2 else 0) + if b[0] = true then 1 else 0) + 4) %
--                         52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                       if a[0] = true then 1 else 0) -
--                     if b[1] = true then 2 else 0))[1] =
--               true
--   all_goals try simp [h1]
--   all_goals by_cases h2: (BitVec.ofNat 3
--                 (((((if a[1] = true then 2 else 0) + if b[0] = true then 1 else 0) + 4) %
--                       52435875175126190479447740508185965837690552500527637822603658699938581184513 -
--                     if a[0] = true then 1 else 0) -
--                   if b[1] = true then 2 else 0))[2] =
--             true
--   all_goals try simp [h2]
--   focus try_apply_lemma_hyps []
--   focus try_apply_lemma_hyps []
--   focus try_apply_lemma_hyps []
--   focus try_apply_lemma_hyps []
--   translate_goal [] false
--   focus try_apply_lemma_hyps []
--   translate_goal [] false
--   focus try_apply_lemma_hyps []
--   translate_goal [] false
--   focus try_apply_lemma_hyps []
--   translate_goal [] false
--   focus try_apply_lemma_hyps []




--   set_option maxRecDepth 1048576
-- set_option maxHeartbeats  20000000000000000000
-- set_option exponentiation.threshold 900

-- def OR_4  : Subtable FF0 8 :=
--   subtableFromMLE (fun x => 1*(x[7] + x[3] - x[7]*x[3]) + 2*(x[6] + x[2] - x[6]*x[2]) + 4*(x[5] + x[1] - x[5]*x[1]) + 8*(x[4] + x[0] - x[4]*x[0]))

-- lemma or_mle_4_chunk
--   (bv1 bv2 : BitVec 4)
--   (fv1 fv2 : Vector FF0 4) :
--   some bvoutput = BVModEq.map_f_to_bv 4 foutput ->
--   some (BVModEq.bool_to_bv 4 bv1[3]) = BVModEq.map_f_to_bv 4 fv1[0]  ->
--   some (BVModEq.bool_to_bv 4 bv1[2]) = BVModEq.map_f_to_bv 4 fv1[1]  ->
--   some (BVModEq.bool_to_bv 4 bv1[1]) = BVModEq.map_f_to_bv 4 fv1[2]  ->
--   some (BVModEq.bool_to_bv 4 bv1[0]) = BVModEq.map_f_to_bv 4 fv1[3]  ->
--   some (BVModEq.bool_to_bv 4 bv2[3]) = BVModEq.map_f_to_bv 4 fv2[0]  ->
--   some (BVModEq.bool_to_bv 4 bv2[2]) = BVModEq.map_f_to_bv 4 fv2[1]  ->
--   some (BVModEq.bool_to_bv 4 bv2[1]) = BVModEq.map_f_to_bv 4 fv2[2]  ->
--   some (BVModEq.bool_to_bv 4 bv2[0]) = BVModEq.map_f_to_bv 4 fv2[3]  ->
--   (bvoutput = (BitVec.or bv1 bv2))
--   =
--   (foutput = evalSubtable OR_4 (Vector.append fv1 fv2))
-- := by
--   unfold OR_4
--   unfold evalSubtable
--   unfold subtableFromMLE
--   unfold Vector.append
--   translate_all false















  --translate_goal [] false
  --translate_goal [] false
  -- sorry
  -- focus try_apply_lemma_hyps []
  -- focus try_apply_lemma_hyps []
  -- focus try_apply_lemma_hyps []
  -- focus try_apply_lemma_hyps []
  -- focus try_apply_lemma_hyps []

  --translate_goal [] false



-- set_option maxRecDepth 1048576
-- set_option maxHeartbeats  20000000000000000000
-- set_option exponentiation.threshold 900
-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 4)
-- variable (a : BitVec 4)
-- lemma correct :
-- ((((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ ((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (if (((BVModEq.bool_to_bv 1 (BVModEq.map_f_to_bv_circ 5  (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 b[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (- ((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184505 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (15 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (BitVec.slt a b)))))))
--  := by
--     translate_goal [] false
--     translate_goal [] false
--     bv_decide



-- --   --rw [map_f_to_bv_circ_spec]
-- --   --split_ands
--  translate_goal [] false
--  have ht : k  =
--     (BitVec.ofNat 3
--       (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--               if d[1] = true then 1 else 0) +
--             if e[1] = true then 1 else 0) +
--           if f[1] = true then 1 else 0) %
--         52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] := by rfl
-- lemma small :(if
--               (BitVec.ofNat 3
--                     (((((((if a[0] = true then 1 else 0) + if b[0] = true then 1 else 0) +
--                               if c[0] = true then 1 else 0) +
--                             if d[0] = true then 1 else 0) +
--                           if e[0] = true then 1 else 0) +
--                         if f[0] = true then 1 else 0) %
--                       52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
--                 true then true else false) := by
--   translate_goal [] false
--   rw [<- hc0]
--   translate_hypothesis hc0 [] [] false
--   rw [hc0]


-- --  let k: Bool :=
-- --   (BitVec.ofNat 3
-- --       (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
-- --               if d[1] = true then 1 else 0) +
-- --             if e[1] = true then 1 else 0) +
-- --           if f[1] = true then 1 else 0) %
-- --         52435875175126190479447740508185965837690552500527637822603658699938581184513))[0];



-- --   split

-- lemma sos :
-- let kc :=
--   (BitVec.ofNat 3
--       (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--               if d[1] = true then 1 else 0) +
--             if e[1] = true then 1 else 0) +
--           if f[1] = true then 1 else 0) %
--         52435875175126190479447740508185965837690552500527637822603658699938581184513))[0];
-- (((((if
--               ((((((if a[0] = true then 1#3 else 0#3) + if b[0] = true then 1#3 else 0#3) +
--                           if c[0] = true then 1#3 else 0#3) +
--                         if d[0] = true then 1#3 else 0#3) +
--                       if e[0] = true then 1#3 else 0#3) +
--                     if f[0] = true then 1#3 else 0#3)[0] =
--                 true then
--             1#3
--           else 0#3) +
--           if
--               ((((((if a[0] = true then 1#3 else 0#3) + if b[0] = true then 1#3 else 0#3) +
--                           if c[0] = true then 1#3 else 0#3) +
--                         if d[0] = true then 1#3 else 0#3) +
--                       if e[0] = true then 1#3 else 0#3) +
--                     if f[0] = true then 1#3 else 0#3)[1] =
--                 true then
--             2#3
--           else 0#3) +
--         if
--             ((((((if a[0] = true then 1#3 else 0#3) + if b[0] = true then 1#3 else 0#3) +
--                         if c[0] = true then 1#3 else 0#3) +
--                       if d[0] = true then 1#3 else 0#3) +
--                     if e[0] = true then 1#3 else 0#3) +
--                   if f[0] = true then 1#3 else 0#3)[2] =
--               true then
--           4#3
--         else 0#3) =
--       (((((if a[0] = true then 1#3 else 0#3) + if b[0] = true then 1#3 else 0#3) + if c[0] = true then 1#3 else 0#3) +
--             if d[0] = true then 1#3 else 0#3) +
--           if e[0] = true then 1#3 else 0#3) +
--         if f[0] = true then 1#3 else 0#3) ∧
--     (((if
--               (BitVec.ofNat 3
--                     (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) +
--                               if c[1] = true then 1 else 0) +
--                             if d[1] = true then 1 else 0) +
--                           if e[1] = true then 1 else 0) +
--                         if f[1] = true then 1 else 0) %
--                       52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
--                 true then
--             1#3
--           else 0#3) +
--           if
--               (BitVec.ofNat 3
--                     (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) +
--                               if c[1] = true then 1 else 0) +
--                             if d[1] = true then 1 else 0) +
--                           if e[1] = true then 1 else 0) +
--                         if f[1] = true then 1 else 0) %
--                       52435875175126190479447740508185965837690552500527637822603658699938581184513))[1] =
--                 true then
--             2#3
--           else 0#3) +
--         if
--             (BitVec.ofNat 3
--                   (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--                           if d[1] = true then 1 else 0) +
--                         if e[1] = true then 1 else 0) +
--                       if f[1] = true then 1 else 0) %
--                     52435875175126190479447740508185965837690552500527637822603658699938581184513))[2] =
--               true then
--           4#3
--         else 0#3) =
--       (((((if a[1] = true then 1#3 else 0#3) + if b[1] = true then 1#3 else 0#3) + if c[1] = true then 1#3 else 0#3) +
--             if d[1] = true then 1#3 else 0#3) +
--           if e[1] = true then 1#3 else 0#3) +
--         if f[1] = true then 1#3 else 0#3) ∧
--   ((if a[0] = (b[0] != (c[0] != (d[0] != (e[0] != f[0])))) then 0#3 else 1#3) =
--       if
--           ((((((if a[0] = true then 1#3 else 0#3) + if b[0] = true then 1#3 else 0#3) +
--                       if c[0] = true then 1#3 else 0#3) +
--                     if d[0] = true then 1#3 else 0#3) +
--                   if e[0] = true then 1#3 else 0#3) +
--                 if f[0] = true then 1#3 else 0#3)[0] =
--             true then
--         1#3
--       else 0#3) ∧
--     (if a[1] = (b[1] != (c[1] != (d[1] != (e[1] != f[1])))) then 0#3 else 1#3) =
--       if
--           (BitVec.ofNat 3
--                 (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--                         if d[1] = true then 1 else 0) +
--                       if e[1] = true then 1 else 0) +
--                     if f[1] = true then 1 else 0) %
--                   52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
--             true then
--         1#3
--       else 0#3 := by
--  intro t
--  have ht : kc =
--     (BitVec.ofNat 3
--       (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--               if d[1] = true then 1 else 0) +
--             if e[1] = true then 1 else 0) +
--           if f[1] = true then 1 else 0) %
--         52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] := by rfl

--   simp
--  rw [ht]


--   -- let t  :=
--   --   (BitVec.ofNat 3
--   --     (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--   --             if d[1] = true then 1 else 0) +
--   --           if e[1] = true then 1 else 0) +
--   --         if f[1] = true then 1 else 0) %
--   --       52435875175126190479447740508185965837690552500527637822603658699938581184513))[0]

--   -- have ht : t =
--   --   (BitVec.ofNat 3
--   --     (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--   --             if d[1] = true then 1 else 0) +
--   --           if e[1] = true then 1 else 0) +
--   --         if f[1] = true then 1 else 0) %
--   --       52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] := by rfl
--   -- rw [<- ht]
--   -- translate_hypothesis ht [] [] false
--   -- rw [ht]


--   --             true (BitVec.ofNat 3
--   --                 (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--   --                         if d[1] = true then 1 else 0) +
--   --                       if e[1] = true then 1 else 0) +
--   --                     if f[1] = true then 1 else 0) %
--   --                   52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
--   --   all_goals simp [h]
--   --   all_goals translate_hypothesis h [] [] false
--   --   all_goals by_cases h1 : (BitVec.ofNat 3
--   --               (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--   --                       if d[1] = true then 1 else 0) +
--   --                     if e[1] = true then 1 else 0) +
--   --                   if f[1] = true then 1 else 0) %
--   --                 52435875175126190479447740508185965837690552500527637822603658699938581184513))[1] = true
--   --   all_goals try simp [h1]
--   --   all_goals try translate_hypothesis h1 [] [] false
--   --   all_goals by_cases h2: (BitVec.ofNat 3
--   --             (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
--   --                     if d[1] = true then 1 else 0) +
--   --                   if e[1] = true then 1 else 0) +
--   --                 if f[1] = true then 1 else 0) %
--   --               52435875175126190479447740508185965837690552500527637822603658699938581184513))[2] = true
--   --   all_goals try simp [h2]
--   --   translate_hypothesis h2 [] [] false
--   --   bv_decide
--   --   translate_hypothesis h2 [] [] false
--   --   bv_decide
--   --   translate_hypothesis h2 [] [] false
--   --   bv_decide
--   --   translate_hypothesis h2 [] [] false
--   --   bv_decide
--   --   translate_hypothesis h2 [] [] false
--   --   bv_decide
  --   translate_hypothesis h2 [] [] false
  --   bv_decide
  --   translate_hypothesis h2 [] [] false
  --   bv_decide
  --   translate_hypothesis h2 [] [] false
  --   bv_decide



  --bv_decide

  -- sorry
  -- translate_goal [] false
  -- set kc := BitVec.ofNat 3
  --               (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
  --                       if d[1] = true then 1 else 0) +
  --                     if e[1] = true then 1 else 0) +
  --                   if f[1] = true then 1 else 0) %
  --                 52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
  --           true
  -- translate_hypothesis hc

  --split_ifs

 -- translate_hypothesis hc [] [] false



  --bv_decide

  -- sorry
  -- translate_goal [] false
  -- set kc := BitVec.ofNat 3
  --               (((((((if a[1] = true then 1 else 0) + if b[1] = true then 1 else 0) + if c[1] = true then 1 else 0) +
  --                       if d[1] = true then 1 else 0) +
  --                     if e[1] = true then 1 else 0) +
  --                   if f[1] = true then 1 else 0) %
  --                 52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] =
  --           true
  -- translate_hypothesis hc

  --split_ifs

 -- translate_hypothesis hc [] [] false




-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry



-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (a : BitVec 2)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (! ((((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (! (((((((((if (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))) = (((- (if (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 (BitVec.neg a)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((((if (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (- (((- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (((- (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a)) + (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))))))))
--  := by
--  translate_goal [] false
--  have h := BitVec.ofNat 510 (ZMod.val smt_fresh_1) <  52435875175126190479447740508185965837690552500527637822603658699938581184513#510
--  have h := BitVec.ofNat 510 (ZMod.val smt_fresh_1) <  52435875175126190479447740508185965837690552500527637822603658699938581184513#510
--  split_ifs
--  translate_goal [] false
--  --constructor

--  bv_decide

  --rw [Math]
--  translate_hypothesis hc [] [] false
--  rw [hc]
-- --bvify at hc







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
-- ((((((((fresh_pf0_cmp_bit0) * (fresh_pf0_cmp_bit0))) = (fresh_pf0_cmp_bit0))) ∧ (((((fresh_pf1_cmp_bit1) * (fresh_pf1_cmp_bit1))) = (fresh_pf1_cmp_bit1))) ∧ (((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2))) ∧ ((((fresh_pf0_cmp_bit0) + (((fresh_pf1_cmp_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_cmp_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = ((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) + (- (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (52435875175126190479447740508185965837690552500527637822603658699938581184511 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) + (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) → (((((((fresh_pf2_cmp_bit2) * (fresh_pf2_cmp_bit2))) = (fresh_pf2_cmp_bit2))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (fresh_pf2_cmp_bit2))) = (BitVec.sle b a)))))))

--  :=by
--   translate_all [] false
--   bv_decide
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1 ]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]

--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]
--   focus try_apply_lemma_hyps [h0_1_1, h0_2_1 , h0_3_1]





-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : Bool)
-- variable (a : Bool)
-- lemma correct :
-- ((((((((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (- ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) * ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (- ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) = ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (- ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (- ((if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) = (((a) ^^ (b)))))))
--  := by -- translate_all
--  translate_goal [] false
--  bv_decide
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []
--  focus try_apply_lemma_hyps []

 --focus try_apply_lemma_hyps []

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry


-- #eval 5175126190479447740508185965837690552500527637822603658699938581184513
-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (! (((((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ ((((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (! (((((((((if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * ((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) = (((- (if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * ((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((((- (((- (if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (((- (if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (((- (if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (((- (if ((((((- (if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((- (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) <-> ((a) ∧ (b) ∧ (c)))))))))))
--  := by
--  translate_all [] false
--  bv_normalize
--  bv_decide




-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
--  ! (( (((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))
--  ∧ ((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))
--  ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))
--  ∧ (
--  ! (((((((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((a) ∨ (b) ∨ (c))))))))))))
--  := by
--   translate_goal [] false
--   have h : BitVec.ofNat 510 (ZMod.val smt_fresh_1) <  BitVec.ofNat 510  (52435875175126190479447740508185965837690552500527637822603658699938581184513) := by sorry
--   have h3 : BitVec.ofNat 510 (ZMod.val smt_fresh_2) <  BitVec.ofNat 510  (52435875175126190479447740508185965837690552500527637822603658699938581184513) := by sorry

--   bv_decide


-- #eval 28948022309329048855892746252171976963317496166410141009864396001978282409983 < 52435875175126190479447740508185965837690552500527637822603658699938581184513
--  --28948022309329048855892746252171976963317496166410141009864396001978282409983#510




  --simp
  --  set kc := (BitVec.ofNat 1
  --   (((if b[0] = true then
  --         (52435875175126190479447740508185965837690552500527637822603658699938581184513 -
  --             if a[0] = true then 1 else 0) %
  --           52435875175126190479447740508185965837690552500527637822603658699938581184513
  --       else 0) +
  --       if a[0] = true then 1 else 0) %
  --     52435875175126190479447740508185965837690552500527637822603658699938581184513))[0] with hc
  --  translate_hypothesis hc [] [] false
  --  simp [kc] at *

  -- rcases h1 with ⟨h1, h2⟩

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (fresh_pf0_shift_bit0 : FF0)
-- variable (b : BitVec 2)
-- variable (a : BitVec 2)
-- variable (fresh_pf1_shift_bit1 : FF0)
-- variable (fresh_pf2_shift_bit2 : FF0)
-- lemma correct :
-- ((((((((fresh_pf0_shift_bit0) * (fresh_pf0_shift_bit0))) = (fresh_pf0_shift_bit0))) ∧ (((((fresh_pf1_shift_bit1) * (fresh_pf1_shift_bit1))) = (fresh_pf1_shift_bit1))) ∧ (((((fresh_pf2_shift_bit2) * (fresh_pf2_shift_bit2))) = (fresh_pf2_shift_bit2))) ∧ ((((fresh_pf0_shift_bit0) + (((fresh_pf1_shift_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((fresh_pf2_shift_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) = (((((if (((BVModEq.bool_to_bv 1 b[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (3 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (- (((((((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (- (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))))) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (- (if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))))))) + (((((((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (- (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))))) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (((((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (- (if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))))) + (if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) + (52435875175126190479447740508185965837690552500527637822603658699938581184512 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))))))))) → (((((if (((BVModEq.bool_to_bv 1 (BitVec.sshiftRight' a b)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf1_shift_bit1))) ∧ (((if (((BVModEq.bool_to_bv 1 (BitVec.sshiftRight' a b)[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf0_shift_bit0)))))))
--  := by
--  translate_all [] false

--  rw [ZMod.val_sub] at h0_4
--  swap
--  focus try_apply_lemma_hyps [h0_1_1, h0_2_1, h0_3_1]
 --valify [h0_1_1, h0_2_1, h0_3_1] at h0_4
  --translate_all

-- theorem my_decide_eq_false_iff (p : Prop) [Decidable p] :
--    ¬ p  ↔ (decide p = false)  := by
--   by_cases hp : p <;> simp [hp]

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (! (((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ ((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (! (((((((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧
-- (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((a) ∨ (b) ∨ (c)))))))))))
--  := by
-- simp
--  simp only [my_decide_eq_false_iff]


  -- translate_all [] false
  -- set kc:=  1 = 1 - if (a = false ∧ b = false) ∧ c = false then 1 else 0 with hc
  -- have hc_iff : kc ↔ (1 = 1 - if (a = false ∧ b = false) ∧ c = false then 1 else 0) := by
  --    rw [hc]

  -- rw [ZMod.eq_if_val] at hc_iff





--  simp at h
--  unfold BVModEq.bool_to_bv at h
--  simp at h
--  simp [ZMod.eq_if_val] at h
--  valify at h
--  rw [BVModEq.BitVec_ofNat_eq_iff 3] at h
--  rw [ZMod.val_sub] at h
--  simp at h
--  rw [BVModEq.BitVec_ofNat_eq_iff 3] at h
--  rw [Nat.mod_eq_of_lt] at h
--  rw [Nat.mod_eq_of_lt] at h

--  bvify at h
--  simp at h
--  bv_decide
--  try_apply_lemma_hyps []

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (b : BitVec 1)
-- variable (a : BitVec 1)
-- variable (x_bit0 : FF0)
-- lemma correct :
-- (((((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 b[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit0))))) → (((a) = (b)))))
--  := by translate_all







-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ ((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (! (((((((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((a) ∨ (b) ∨ (c))))))))))
--  := by
--   translate_all [] false

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (a : BitVec 6)
-- variable (x_bit5 : FF0)
-- variable (x_bit4 : FF0)
-- variable (x_bit3 : FF0)
-- variable (x_bit2 : FF0)
-- variable (x_bit1 : FF0)
-- variable (x_bit0 : FF0)
-- lemma correct :
-- ((((((if (((BVModEq.bool_to_bv 1 a[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit0))) ∧ (((if (((BVModEq.bool_to_bv 1 a[1]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit1))) ∧ (((if (((BVModEq.bool_to_bv 1 a[2]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit2))) ∧ (((if (((BVModEq.bool_to_bv 1 a[3]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit3))) ∧ (((if (((BVModEq.bool_to_bv 1 a[4]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit4))) ∧ (((if (((BVModEq.bool_to_bv 1 a[5]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (x_bit5)))) → (((BVModEq.map_f_to_bv_circ 6  ((x_bit0) + (((x_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((x_bit2) * (4 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((x_bit3) * (8 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((x_bit4) * (16 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (((x_bit5) * (32 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (a)))))
--  := by
--   -- intro h
--   -- rw [map_f_to_bv_circ_spec]
--   -- valify
--   -- simp
--   -- rw [Nat.mod_eq_of_lt]
--   -- bvify


--   translate_all [] false

  --try_apply_lemma_hyps []


 --sorry
 --try_apply_lemma_hyps [h0_1_1,h0_2_1]

 --bv_decide

-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (fresh_pf0_sum_bit0 : FF0)
-- variable (b : BitVec 1)
-- variable (a : BitVec 1)
-- variable (fresh_pf1_sum_bit1 : FF0)
-- lemma correct :
-- ((((((((fresh_pf0_sum_bit0) * (fresh_pf0_sum_bit0))) = (fresh_pf0_sum_bit0))) ∧ (((((fresh_pf1_sum_bit1) * (fresh_pf1_sum_bit1))) = (fresh_pf1_sum_bit1))) ∧ (((((fresh_pf0_sum_bit0) + (((fresh_pf1_sum_bit1) * (2 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  a) * (BVModEq.map_bv_to_f 52435875175126190479447740508185965837690552500527637822603658699938581184513  b)))))) → (((if (((BVModEq.bool_to_bv 1 (BitVec.mul a b)[0]!) = (BitVec.ofNat 1 1))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) = (fresh_pf0_sum_bit0)))))
--  := by
--    translate_all [] false



  -- intro h
  -- simp at h
  -- rcases h with ⟨h1, h2⟩
  -- translate_hypothesis h1 [] false
  -- translate_hypothesis h2 [] false
  -- translate_goal [] false
  -- bv_decide


  --translate_all


-- abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- instance : Fact (Nat.Prime ffff0) := by sorry
-- instance : Fact (NeZero ffff0) := by sorry
-- instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry

-- abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
-- variable (c : Bool)
-- variable (b : Bool)
-- variable (a : Bool)
-- variable (smt_fresh_1 : FF0)
-- variable (smt_fresh_2 : FF0)
-- lemma correct :
-- (((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_1))) = (((- smt_fresh_2) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ ((((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (((((smt_fresh_1) * (smt_fresh_2))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) ∧ (! (((((((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else smt_fresh_1) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) * ((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((((((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) * (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) ∧ (((((1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) = (((- (if ((((if a then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if b then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513)) + (if c then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) = (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) then (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513) else (0 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))) + (1 : ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) = ((a) ∨ (b) ∨ (c))))))))))
--  := by translate_all


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
