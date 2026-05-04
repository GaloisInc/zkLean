/-
This file is adapted from `Mathlib.Tactic.Zify`.

It implements a `bvify` tactic, which mirrors the structure of `zify`,
but specializes it for BitVec goals. Instead of rewriting into integers,
it rewrites expressions into `BitVec.ofNat` form and simplifies using
bitvector-specific lemmas.
-/

import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand

import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Basic
import Std.Tactic.BVDecide

import BVModEq.Lemmas

namespace Mathlib.Tactic.BVify

open Fin
open Lean
open Lean.Elab.Tactic
open Lean.Meta
open Lean.Parser.Tactic

/-- Multiplication distributes through `BitVec.ofNat`. -/
lemma BitVec.ofNat_mul {w a b : ℕ} :
    BitVec.ofNat w (a * b) = BitVec.ofNat w a * BitVec.ofNat w b := by
  rw [BitVec.ofNat, BitVec.ofNat, BitVec.ofNat]
  rw [Fin.ofNat, Fin.ofNat, Fin.ofNat]
  apply congrArg
  simp_all
  apply Fin.eq_of_val_eq
  simp_all

/-- `if` over Bool commutes with `BitVec.ofNat`. -/
lemma BitVec.ofNat_if_then_else {bw x y : ℕ} {b : Bool} :
    BitVec.ofNat bw (if b then x else y)
      =
    if b then BitVec.ofNat bw x else BitVec.ofNat bw y := by
  split_ifs <;> simp

/-- `if` over Prop commutes with `BitVec.ofNat`. -/
lemma BitVec.ofNat_if_then_prop_else {bw x y : ℕ} {b : Prop} [Decidable b] :
    BitVec.ofNat bw (if b then x else y)
      =
    if b then BitVec.ofNat bw x else BitVec.ofNat bw y := by
  split_ifs <;> simp

/-- Subtraction distributes through `BitVec.ofNat` under bounds. -/
lemma BitVec.ofNat_sub {bw x y : ℕ} (h : y ≥ x) (h1 : y < 2 ^ bw) :
    BitVec.ofNat bw (y - x) = BitVec.ofNat bw y - BitVec.ofNat bw x := by
  unfold BitVec.ofNat
  rw [Fin.ofNat, Fin.ofNat, Fin.ofNat]
  apply congrArg
  simp_all
  apply Fin.eq_of_val_eq
  simp_all
  rw [← Nat.mod_sub_of_le]

  have pow_pos := Nat.two_pow_pos bw
  have hx : x % 2 ^ bw ≤ (y + 2 ^ bw) % 2 ^ bw := by
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt]
    rw [Nat.mod_eq_of_lt]
    apply h
    apply h1
    exact lt_of_le_of_lt h h1

  conv =>
    enter [2]
    simp
    rw [Nat.add_comm (2 ^ bw - x % 2 ^ bw) y]
    rw [← Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt x pow_pos))]
    rw [← Nat.mod_sub_of_le hx]
    rw [Nat.add_mod_right]

  nth_rewrite 3 [Nat.mod_eq_of_lt]
  simp
  exact lt_of_le_of_lt h h1
  rw [Nat.mod_eq_of_lt]
  apply h
  apply h1

/-- Main `bvify` tactic: simplifies goals into BitVec-normalized form. -/
syntax (name := bvify) "bvify" (simpArgs)? (location)? : tactic

macro_rules
  | `(tactic| bvify $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic|
      simp [
        BitVec.ofNat_if_then_else,
        BitVec.ofNat_if_then_prop_else,
        BitVec.ofNat_sub,
        BitVec.ofNat_add,
        BitVec.ofNat_mul,
        BitVec.ofNat_toNat,
        push_cast,
        $[$args],*
      ] $[at $location]?
    )

/-- Build the simp context used by `bvify` (mirrors `zify`). -/
def mkBVifyContext
    (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic|
      simp [
        BitVec.ofNat_if_then_else,
        BitVec.ofNat_if_then_prop_else,
        BitVec.ofNat_sub,
        BitVec.ofNat_add,
        BitVec.ofNat_mul,
        BitVec.ofNat_toNat,
        push_cast,
        $[$args],*
      ]
    ))
    false

/-- Apply simp result to a proposition without closing the goal. -/
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

/-- Core transformation step, analogous to `zifyProof`. -/
def bvifyProof
    (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof prop : Expr) :
    TacticM (Expr × Expr) := do
  let ctxResult ← mkBVifyContext simpArgs
  let (r, _) ← simp prop ctxResult.ctx
  applySimpResultToProp' proof prop r

end Mathlib.Tactic.BVify
