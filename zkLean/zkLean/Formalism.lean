import Cslib.Foundations.Control.Monad.Free
import Cslib.Foundations.Control.Monad.Free.Fold
import Mathlib.Control.Traversable.Basic
import Std.Do

import zkLean.AST
import zkLean.Builder
import zkLean.LookupTable
import zkLean.Semantics
import zkLean.SimpSets

attribute [simp_FreeM] bind
attribute [simp_FreeM] default
attribute [simp_FreeM] Cslib.FreeM.bind
attribute [simp_FreeM] Cslib.FreeM.foldFreeM

attribute [simp_Triple] Std.Do.Triple
attribute [simp_Triple] Std.Do.SPred.entails
attribute [simp_Triple] Std.Do.PredTrans.apply
attribute [simp_Triple] Std.Do.PredTrans.pure
attribute [simp_Triple] Std.Do.wp

/-- Run a circuit builder given the witness and then evaluate the resulting circuit. -/
@[simp_ZKSemantics]
def run_circuit [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  semantics circuit witness

/-- Evaluate a circuit given some witnesses and a builder final state. -/
@[simp_ZKSemantics]
def eval_circuit [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Prop :=
  semantics circuit witness

open Std.Do

/-- `ZKBuilder` admits a weakest‐precondition interpretation in terms of the
`MPL` predicate–transformer semantics.  A builder computation manipulates an
implicit `ZKBuilderState`; therefore its predicate shape is `PostShape.arg
(ZKBuilderState f) .pure`.

The interpretation simply executes the computation with `runFold_old` and feeds the
result to the post-condition. -/

def wpZKBuilder [ZKField f] (x : ZKBuilder f a)
  : PredTrans (.arg (ZKState f) (.except PUnit .pure)) a
  := PredTrans.pushArg (fun s => PredTrans.pushOption (.mk (.pure ((runZKBuilder x).run s))))

@[reducible, simp_ZKBuilder]
instance [ZKField f] : WP (ZKBuilder f) (.arg (ZKState f) (.except PUnit .pure)) where
  wp := wpZKBuilder

@[simp]
def runZKBuilder_liftBind [ZKField f] op (cont : a → ZKBuilder f b) s
  : runZKBuilder (.liftBind op cont) s = (ZKOpInterp op s).bind fun (r, s') => runZKBuilder (cont r) s'
  := by rfl

def runZKBuilder_bind [ZKField f] (lhs : ZKBuilder f a) (rhs : a → ZKBuilder f b) s
  : runZKBuilder (.bind lhs rhs) s =
    match runZKBuilder lhs s with
    | none => none
    | some (r, s') => runZKBuilder (rhs r) s'
  := by
  revert s
  induction lhs
  · simp [runZKBuilder, StateT.pure]
  · case liftBind op cont IH =>
    intro s
    unfold Cslib.FreeM.bind
    simp
    conv =>
      lhs
      rhs
      intro x
      rw [IH]
    cases ZKOpInterp op s
    · simp
    · simp

-- wp⟦ op ≫= (cont ≫= g) ⟧ = wp ⟦ (op ≫= cont) ⟧ ≫= (λ r ⇒ wp ⟦g r⟧)
def wpZKBuilder_liftBind_bind [ZKField f] (g : a → ZKBuilder f b) (cont : ι → ZKBuilder f a)
  : wpZKBuilder (.liftBind op fun x => (cont x).bind fun r => g r)
  = (wpZKBuilder (.liftBind op cont)).bind (fun r => wpZKBuilder (g r)) := by
  ext pc s
  unfold wpZKBuilder
  simp [PredTrans.pushArg_apply, OptionT.mk, StateT.run]
  conv =>
    lhs
    arg 1
    arg 2
    arg 2
    intro a
    rw [runZKBuilder_bind]
  simp [PredTrans.bind]
  cases (ZKOpInterp op s)
  · simp
  · case some res =>
    simp
    cases (runZKBuilder (cont res.1) res.2)
    · simp
    · rfl

instance [ZKField f] : WPMonad (ZKBuilder f) (.arg (ZKState f) (.except PUnit .pure)) where
  wp_pure a := by
    aesop
  wp_bind x f := by
    ext
    simp [simp_ZKBuilder]
    induction x
    · rfl
    · simp
      rw [wpZKBuilder_liftBind_bind]
      rfl

/--
The following machinery is not needed to prove properties about circuits in zkLean, but they may be useful to prove completeness and determinism.
-/
class CircuitInput (i: Type) (f: Type) where
  -- /-- Circuit representation of input i. For example, the circuit representation of `f` might be `ZKExpr f`. -/
  -- CircuitInputRepr : Type

  /-- Function that generates the extended witness from the input to a circuit. -/
  witness_generation : i → List f -- JP: Does a `Writer` make more sense?

/-- Proposition that states that a circuit is sound with respect to a specification. -/
def sound [ZKField f] (circuit: input_exprs → ZKBuilder f α) (specification : ZKState f → input_exprs → α → Prop) : input_exprs → Prop :=
  λ inputs =>
  ⦃ λ s => ⌜ true ⌝ ⦄
  circuit inputs
  ⦃ ⇓ output s => ⌜ specification s inputs output ⌝ ⦄
  -- semantics circuit extended_witness → specification inputs

/-- Proposition that states that a circuit is complete with respect to witness generation and given preconditions on the input. -/
def complete [ZKField f] [I: CircuitInput i f] (circuit: ZKBuilder f α) (preconditions : i → Prop) : i → Prop :=
  λ inputs =>
    let extended_witness := I.witness_generation inputs
    preconditions inputs → semantics circuit extended_witness

/-- Proposition that states that a circuit is deterministic and only has one satisfying assignment. -/
def deterministic [ZKField f] (circuit: ZKBuilder f α) : List f → List f → Prop :=
  λ extended_witness1 extended_witness2 =>
    semantics circuit extended_witness1 ∧ semantics circuit extended_witness2 →
    extended_witness1 = extended_witness2
