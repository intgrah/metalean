/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.LiteralTyping
import Metalean.Typing.Map
import Metalean.Typing.Context
import Metalean.Typing.InstLevel

@[expose] public section

namespace Metalean.Checker.Acceleration

open CategoryTheory

variable {ζ : Sigs}

def NatOpEq (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig)) {kind : ConstKind}
    (ηOp : Head ζ (.const kind 0)) (f : Nat → Nat → Nat) : Prop :=
  ∀ ⦃ℓ n : Nat⦄ (Γ : Ctx ζ ℓ 0 n) (a b : Nat),
  E[Γ] ⊢ Expr.op₂ ηOp (Expr.natLit ηNat a) (Expr.natLit ηNat b) ≡
    Expr.natLit ηNat (f a b) : Expr.nat ηNat

def BoolOpEq (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηBool : Head ζ (.inductive Bool.sig)) {kind : ConstKind}
    (ηOp : Head ζ (.const kind 0)) (f : Nat → Nat → Bool) : Prop :=
  ∀ ⦃ℓ n : Nat⦄ (Γ : Ctx ζ ℓ 0 n) (a b : Nat),
  E[Γ] ⊢ Expr.op₂ ηOp (Expr.natLit ηNat a) (Expr.natLit ηNat b) ≡
    Expr.boolLit ηBool (f a b) : Expr.bool ηBool

variable {E : Env ζ} {ηNat : Head ζ (.inductive Nat.sig)} {kind : ConstKind}
  {ηOp : Head ζ (.const kind 0)}

theorem NatOpEq.ofClosed {f : Nat → Nat → Nat}
    (h : ∀ a b : Nat, E[(#t[] : Ctx ζ 0 0 0)] ⊢
      Expr.op₂ ηOp (Expr.natLit ηNat a) (Expr.natLit ηNat b) ≡
        Expr.natLit ηNat (f a b) : Expr.nat ηNat) :
    NatOpEq E ηNat ηOp f := by
  intro ℓ n Γ a b
  simpa using ((h a b).instLevel (fun p : Param 0 => (p.elim0 : Level ℓ))).wkClosed (Γ := Γ)

theorem BoolOpEq.ofClosed {ηBool : Head ζ (.inductive Bool.sig)}
    {f : Nat → Nat → Bool}
    (h : ∀ a b : Nat, E[(#t[] : Ctx ζ 0 0 0)] ⊢
      Expr.op₂ ηOp (Expr.natLit ηNat a) (Expr.natLit ηNat b) ≡
        Expr.boolLit ηBool (f a b) : Expr.bool ηBool) :
    BoolOpEq E ηNat ηBool ηOp f := by
  intro ℓ n Γ a b
  simpa using ((h a b).instLevel (fun p : Param 0 => (p.elim0 : Level ℓ))).wkClosed (Γ := Γ)

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {kind : ConstKind}
  {ηNat : Head ζ₁ (.inductive Nat.sig)} {ηBool : Head ζ₁ (.inductive Bool.sig)}
  {ηOp : Head ζ₁ (.const kind 0)}

theorem NatOpEq.map (pre : E₁.as ⟶ E₂.as) {f : Nat → Nat → Nat} :
    NatOpEq E₁ ηNat ηOp f →
    NatOpEq E₂ (ηNat.map pre.sigs) (ηOp.map pre.sigs) f := by
  intro h ℓ n Γ a b
  simpa [Fin.fun_vecEmpty] using ((h (ℓ := ℓ) .nil a b).map pre).wkClosed (Γ := Γ)

theorem BoolOpEq.map (pre : E₁.as ⟶ E₂.as) {f : Nat → Nat → Bool} :
    BoolOpEq E₁ ηNat ηBool ηOp f →
    BoolOpEq E₂ (ηNat.map pre.sigs) (ηBool.map pre.sigs) (ηOp.map pre.sigs) f := by
  intro h ℓ n Γ a b
  simpa [Fin.fun_vecEmpty] using ((h (ℓ := ℓ) .nil a b).map pre).wkClosed (Γ := Γ)

end Metalean.Checker.Acceleration
