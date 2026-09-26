/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Base
public import Metalean.Frontend.Table

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open scoped FExpr

open Frontend (Failure Table)

namespace Decide

structure Consts where
  protected Nat_ : Nat
  protected dite : Nat
  protected Decidable_ : Nat
  protected Eq_ : Nat
  protected False_ : Nat

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    Nat_ := ← t.ind ``Nat
    dite := ← t.const ``dite
    Decidable_ := ← t.ind ``Decidable
    Eq_ := ← t.ind ``Eq
    False_ := ← t.ind ``False }

structure LeConsts extends toConsts : Consts where
  protected Nat_le_ : Nat
  protected Nat_decLe : Nat

instance : CoeOut LeConsts Consts := ⟨LeConsts.toConsts⟩

def LeConsts.resolve (t : Table) : Except Failure LeConsts := do
  pure {
    toConsts := ← Consts.resolve t
    Nat_le_ := ← t.ind ``Nat.le
    Nat_decLe := ← t.const ``Nat.decLe }

structure EqNatConsts extends toConsts : Consts where
  protected instDecidableEqNat : Nat

instance : CoeOut EqNatConsts Consts := ⟨EqNatConsts.toConsts⟩

structure BoolConsts extends toConsts : Consts where
  protected Bool_ : Nat

instance : CoeOut BoolConsts Consts := ⟨BoolConsts.toConsts⟩

structure EqBoolConsts extends toBoolConsts : BoolConsts where
  protected instDecidableEqBool : Nat

instance : CoeOut EqBoolConsts BoolConsts := ⟨EqBoolConsts.toBoolConsts⟩

structure DecideConsts extends toEqNatConsts : EqNatConsts, toBoolConsts : BoolConsts where
  protected Decidable_decide : Nat

instance : CoeOut DecideConsts EqNatConsts := ⟨DecideConsts.toEqNatConsts⟩

end Decide

namespace FExpr

section

variable (D : Decide.Consts)

/-- `False` -/
@[fexpr_unfold]
protected def False : FExpr :=
  .ind D.False_ 0 #[] #[] #[]

/-- `Not` -/
@[fexpr_unfold]
protected def Not (p : FExpr) : FExpr :=
  .forallE p (FExpr.False D)

/-- `Eq` at `Sort 1` -/
@[fexpr_unfold]
protected def Eq (α a b : FExpr) : FExpr :=
  .ind D.Eq_ 0 #[.succ .zero] #[α, a] #[b]

@[fexpr_unfold]
protected def Eq.refl (α a : FExpr) : FExpr :=
  .ctor D.Eq_ 0 0 #[.succ .zero] #[α, a] #[] #[]

@[fexpr_unfold]
protected def Decidable (p : FExpr) : FExpr :=
  .ind D.Decidable_ 0 #[] #[p] #[]

/-- `dite` at `Sort 1` -/
@[fexpr_unfold]
protected def dite (α p d onTrue onFalse : FExpr) : FExpr :=
  .appList (.const D.dite #[.succ .zero]) [α, p, d, onTrue, onFalse]

end

@[fexpr_unfold]
protected def Nat.le (D : Decide.LeConsts) (a b : FExpr) : FExpr :=
  .ind D.Nat_le_ 0 #[] #[a] #[b]

@[fexpr_unfold]
protected def Nat.decLe (D : Decide.LeConsts) (a b : FExpr) : FExpr :=
  op₂ D.Nat_decLe a b

@[fexpr_unfold]
protected def instDecidableEqNat (D : Decide.EqNatConsts) (a b : FExpr) : FExpr :=
  op₂ D.instDecidableEqNat a b

@[fexpr_unfold]
protected def instDecidableEqBool (D : Decide.EqBoolConsts) (a b : FExpr) : FExpr :=
  op₂ D.instDecidableEqBool a b

@[fexpr_unfold]
protected def Decidable.decide (D : Decide.DecideConsts) (p d : FExpr) : FExpr :=
  .appList (.const D.Decidable_decide #[]) [p, d]

end FExpr

namespace Decide

variable (F : FEnv)

def Consts.natSpec (D : Consts) : Except Failure (PLift (NatSpec F D.Nat_)) := do
  natAt F D.Nat_

def checkBools {P : Bool → Prop} (c : ∀ v, EIO Failure (PLift (P v))) :
    EIO Failure (PLift (∀ v, P v)) := do
  let ⟨hf⟩ ← c false
  let ⟨ht⟩ ← c true
  pure ⟨fun
    | false => hf
    | true => ht⟩

def boolLitType (b : Nat) (v : Bool) : Schema :=
  schema% ⊢ boolLit b v : bool b

def Reduces (D : Consts) (P d : FExpr) (holds : Bool) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
  FEnv.Denotes F E →
  EnvWF E →
  ∀ ⦃t e : FExpr⦄,
  FEq E t t (P ⟶ nat D.Nat_) →
  FEq E e e (FExpr.Not D P ⟶ nat D.Nat_) →
  ∃ h : FExpr, FEq E h h (cond holds P (FExpr.Not D P)) ∧
    FEq E (FExpr.dite D (nat D.Nat_) P d t e) (.app (cond holds t e) h) (nat D.Nat_)

def DecLe (D : LeConsts) : Prop :=
  ∀ b a : Nat,
  Reduces F D (FExpr.Nat.le D (.natLit D.Nat_ b) (.natLit D.Nat_ a))
    (FExpr.Nat.decLe D (.natLit D.Nat_ b) (.natLit D.Nat_ a)) (decide (b ≤ a))

def DecEqNat (D : EqNatConsts) : Prop :=
  ∀ a b : Nat,
  Reduces F D (FExpr.Eq D (nat D.Nat_) (.natLit D.Nat_ a) (.natLit D.Nat_ b))
    (FExpr.instDecidableEqNat D (.natLit D.Nat_ a) (.natLit D.Nat_ b)) (a == b)

def DecEqBool (D : EqBoolConsts) : Prop :=
  ∀ β γ : Bool,
  Reduces F D (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
    (FExpr.instDecidableEqBool D (boolLit D.Bool_ β) (boolLit D.Bool_ γ)) (β == γ)

def DecideEqNat (D : DecideConsts) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
  FEnv.Denotes F E →
  EnvWF E →
  ∀ a b : Nat,
  FEq E
    (FExpr.Decidable.decide D (FExpr.Eq D (nat D.Nat_) (.natLit D.Nat_ a) (.natLit D.Nat_ b))
      (FExpr.instDecidableEqNat D (.natLit D.Nat_ a) (.natLit D.Nat_ b)))
    (boolLit D.Bool_ (a == b)) (bool D.Bool_)

end Decide

end Metalean.Checker.Fast
