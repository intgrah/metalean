/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.Literal
public import Metalean.Syntax.Sig

@[expose] public section

namespace Metalean

@[reducible] protected def Nat.le.refl.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] protected def Nat.le.step.sig : CtorSig 1 where
  nfields := 1
  nrecFields := 1
  recursiveArity := ![0]
  recursiveTarget := ![0]

/-- `Nat.le (n : Nat) : Nat → Prop` -/
@[reducible] protected def Nat.le.sig : IndSig where
  nlevels := 0
  nparams := 1
  nsorts := 1
  nindices _ := 1
  nctors _ := 2
  ctors _
    | 0 => Nat.le.refl.sig
    | 1 => Nat.le.step.sig

@[reducible] protected def False.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 0
  ctors _ := Fin.elim0

@[reducible] protected def Decidable.isFalse.sig : CtorSig 1 where
  nfields := 1
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] protected def Decidable.isTrue.sig : CtorSig 1 where
  nfields := 1
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

/-- `Decidable (p : Prop)` with `isFalse` and `isTrue` -/
@[reducible] protected def Decidable.sig : IndSig where
  nlevels := 0
  nparams := 1
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _
    | 0 => Decidable.isFalse.sig
    | 1 => Decidable.isTrue.sig

@[reducible] protected def PSigma.mk.sig : CtorSig 1 where
  nfields := 2
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

/-- `PSigma.{u, v} (α : Sort u) (β : α → Sort v)` -/
@[reducible] protected def PSigma.sig : IndSig where
  nlevels := 2
  nparams := 2
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ _ := PSigma.mk.sig

namespace Expr

variable {ζ : Sigs} {ℓ n : Nat}

abbrev le (η : Head ζ (.inductive Nat.le.sig)) (a b : Expr ζ ℓ n) :
    Expr ζ ℓ n :=
  .ind η 0 ![] ![a] ![b]

abbrev false (η : Head ζ (.inductive False.sig)) : Expr ζ ℓ n :=
  .ind η 0 ![] ![] ![]

abbrev not (η : Head ζ (.inductive False.sig)) (p : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE p (Expr.false η)

abbrev eq (η : Head ζ (.inductive Eq.sig)) (l : Level ℓ) (α a b : Expr ζ ℓ n) :
    Expr ζ ℓ n :=
  .ind η 0 ![l] ![α, a] ![b]

abbrev eqRefl (η : Head ζ (.inductive Eq.sig)) (l : Level ℓ) (α a : Expr ζ ℓ n) :
    Expr ζ ℓ n :=
  .ctor η 0 0 ![l] ![α, a] ![] ![]

abbrev decidable (η : Head ζ (.inductive Decidable.sig)) (p : Expr ζ ℓ n) :
    Expr ζ ℓ n :=
  .ind η 0 ![] ![p] ![]

/-- `isFalse h` or `isTrue h` -/
@[simp] def ofBool (η : Head ζ (.inductive Decidable.sig)) (p h : Expr ζ ℓ n) :
    Bool → Expr ζ ℓ n
  | .false => .ctor η 0 0 ![] ![p] ![h] ![]
  | .true => .ctor η 0 1 ![] ![p] ![h] ![]

abbrev psigma (η : Head ζ (.inductive PSigma.sig)) (l₁ l₂ : Level ℓ)
    (α β : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ind η 0 ![l₁, l₂] ![α, β] ![]

abbrev psigmaMk (η : Head ζ (.inductive PSigma.sig)) (l₁ l₂ : Level ℓ)
    (α β a b : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 0 ![l₁, l₂] ![α, β] ![a, b] ![]

variable {kd : ConstKind}

/-- `dite.{1} α P d t e` -/
abbrev dite (ηDite : Head ζ (.const kd 1)) (α P d t e : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .appList (.const ηDite ![.succ .zero]) [α, P, d, t, e]

end Expr

end Metalean
