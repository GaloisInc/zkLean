/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis

This file is adapted from `Mathlib.Tactic.Zify`.

It implements a `valify` tactic, which mirrors the structure of `zify`,
but specializes it for `ZMod.val` goals. Instead of rewriting into integers,
it rewrites expressions involving `ZMod n` into their `.val` form and
simplifies using `ZMod.val` lemmas.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Meta.Tactic.Simp.SimpTheorems

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Basic

import BVModEq.Lemmas

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace BVModEq

/-- `if` over Bool commutes with `ZMod.val`. -/
lemma ZMod.if_then_else_val {x y : ZMod n} {b : Bool} :
    (if b then x else y).val = if b then x.val else y.val := by
  split_ifs <;> simp

/-- `if` over Prop commutes with `ZMod.val`. -/
lemma ZMod.if_then_else_prop_val {x y : ZMod n} {b : Prop} [Decidable b] :
    (if b then x else y).val = if b then x.val else y.val := by
  split_ifs <;> simp

/-- Main `valify` tactic: simplifies goals into `.val`-normalized form. -/
syntax (name := valify) "valify" (simpArgs)? (location)? : tactic

macro_rules
  | `(tactic| valify $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic|
      simp [
        -zero_sub,
        -ZMod.val_eq_zero,
        ZMod.if_then_else_val,
        ZMod.if_then_else_prop_val,
        ZMod.val_sub,
        ZMod.val_add,
        ZMod.val_mul,
        ZMod.val_one,
        ZMod.val_zero,
        ZMod.val_ofNat,
        push_cast,
        $[$args],*
      ] $[at $location]?
    )

/-- Build the simp context used by `valify` (mirrors `zify`). -/
def mkValifyContext
    (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic|
      simp [
        -zero_sub,
        -ZMod.val_eq_zero,
        ZMod.if_then_else_val,
        ZMod.if_then_else_prop_val,
        ZMod.val_sub,
        ZMod.val_add,
        ZMod.val_mul,
        ZMod.val_one,
        ZMod.val_zero,
        ZMod.val_ofNat,
        push_cast,
        $[$args],*
      ]
    ))
    false

/--
Apply a simp result to a proposition without closing the goal.

This mirrors the helper used by `zify`, but is reused here for the
`.val`-normalization pass.
-/
def applySimpResultToProp' (proof prop : Expr) (r : Simp.Result) :
    MetaM (Expr × Expr) := do
  match r.proof? with
  | some eqProof =>
      return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
      if r.expr != prop then
        return (← mkExpectedTypeHint proof r.expr, r.expr)
      else
        return (proof, r.expr)

/-- Core transformation step: convert a proposition into `valify`-normalized form. -/
def valifyProof
    (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof prop : Expr) :
    TacticM (Expr × Expr) := do
  let ctxResult ← mkValifyContext simpArgs
  let (r, _) ← simp prop ctxResult.ctx
  applySimpResultToProp' proof prop r

end BVModEq
