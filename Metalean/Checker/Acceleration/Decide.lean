/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.Prelude
public import Metalean.Checker.Acceleration.Rule

@[expose] public section

namespace Metalean.Checker.Acceleration.Decide

open Expr (natLit)

variable {ζ : Sigs} (E : Env ζ) (η : Head ζ (.inductive Nat.sig)) {kd : ConstKind}
  (ηDite : Head ζ (.const kd 1)) (ηFalse : Head ζ (.inductive False.sig))

/-- On literals, `dite P d t e` takes branch `v`, applied to a proof of that branch -/
def Reduces (P d : Expr ζ 0 0) (v : Bool) : Prop :=
  ∀ t e : Expr ζ 0 0,
  E[#t[]] ⊢ t : .forallE P (Expr.nat η) →
  E[#t[]] ⊢ e : .forallE (Expr.not ηFalse P) (Expr.nat η) →
  ∃ w, E[#t[]] ⊢ w : cond v P (Expr.not ηFalse P) ∧
    E[#t[]] ⊢ Expr.dite ηDite (Expr.nat η) P d t e ≡ .app (cond v t e) w : Expr.nat η

variable {kl : ConstKind} (ηLe : Head ζ (.inductive Nat.le.sig)) (ηDecLe : Head ζ (.const kl 0))

def DecLe : Prop :=
  ∀ b a : Nat, Reduces E η ηDite ηFalse (Expr.le ηLe (natLit η b) (natLit η a))
    (Expr.op₂ ηDecLe (natLit η b) (natLit η a)) (decide (b ≤ a))

variable (ηEq : Head ζ (.inductive Eq.sig)) {ki : ConstKind} (ηInst : Head ζ (.const ki 0))

def DecEqNat : Prop :=
  ∀ a b : Nat, Reduces E η ηDite ηFalse
    (Expr.eq ηEq (.succ .zero) (Expr.nat η) (natLit η a) (natLit η b))
    (Expr.op₂ ηInst (natLit η a) (natLit η b)) (a == b)

variable (ηBool : Head ζ (.inductive Bool.sig))

def DecEqBool : Prop :=
  ∀ β γ : Bool, Reduces E η ηDite ηFalse
    (Expr.eq ηEq (.succ .zero) (Expr.bool ηBool) (Expr.boolLit ηBool β) (Expr.boolLit ηBool γ))
    (Expr.op₂ ηInst (Expr.boolLit ηBool β) (Expr.boolLit ηBool γ)) (β == γ)

variable {kc : ConstKind} (ηDecide : Head ζ (.const kc 0))

/-- `decide (a = b) (instDecidableEqNat a b) ≡ (a == b)` -/
def DecideEqNat : Prop :=
  ∀ a b : Nat, E[(#t[] : Ctx ζ 0 0 0)] ⊢
    (.appList (.const ηDecide ![])
      [Expr.eq ηEq (.succ .zero) (Expr.nat η) (natLit η a) (natLit η b),
        Expr.op₂ ηInst (natLit η a) (natLit η b)]) ≡
    Expr.boolLit ηBool (a == b) : Expr.bool ηBool

end Metalean.Checker.Acceleration.Decide
