import Mathlib.Algebra.Field.Defs

import zkLean.LookupTable
import zkLean.SimpSets

/--
Type for expressions to define computation to be verified by a Zero-Knowledge protocol.

The expressions are parametrized by a field type `f`.
The construtors include the usual arithmetic operations.
-/
inductive ZKExpr (f : Type) where
  | Field : (element : f) -> ZKExpr f
  | Add : (lhs rhs : ZKExpr f) -> ZKExpr f
  | Sub : (lhs rhs : ZKExpr f) -> ZKExpr f
  | Neg : (arg : ZKExpr f) -> ZKExpr f
  | Mul : (lhs rhs : ZKExpr f) -> ZKExpr f

@[simp_ZKBuilder]
def ZKExpr.eval [HAdd f f f] [HSub f f f] [HMul f f f] [_root_.Neg f] (e: ZKExpr f) : f :=
  match e with
    | ZKExpr.Field f => f
    | ZKExpr.Add lhs rhs =>
        lhs.eval + rhs.eval
    | ZKExpr.Sub lhs rhs =>
        lhs.eval - rhs.eval
    | ZKExpr.Mul lhs rhs =>
        lhs.eval * rhs.eval
    | ZKExpr.Neg arg =>
        -(arg.eval)

instance [Inhabited f]: Inhabited (ZKExpr f) where
  default := ZKExpr.Field default

instance [OfNat f n] : OfNat (ZKExpr f) n where
  ofNat := ZKExpr.Field (OfNat.ofNat n)

instance [Zero f]: Zero (ZKExpr f) where
  zero := ZKExpr.Field 0

instance: HAdd (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hAdd := ZKExpr.Add

instance: Add (ZKExpr f) where
  add := ZKExpr.Add

instance: HSub (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hSub := ZKExpr.Sub

instance: Neg (ZKExpr f) where
  neg := ZKExpr.Neg

instance: HMul (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hMul := ZKExpr.Mul
