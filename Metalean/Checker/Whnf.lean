/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.DecEq
public import Metalean.Strong.Context
public import Metalean.Control
public import Metalean.Syntax.Reduction
import Metalean.Meta.IfRfl
import Metalean.Metatheory.SubjectReduction

@[expose] public section

namespace Metalean.Checker

open Relation
open Frontend (Failure)

variable {ζ : Sigs} (E : Env ζ) {ℓ : Nat}

def iotaStep {n : Nat} {ι : IndSig} (η₁ : Head ζ (.inductive ι)) (s₁ : Fin ι.nsorts)
    (ls₁ : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (ps₁ : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s₁) → Expr ζ ℓ n) :
    (maj : Expr ζ ℓ n) →
    Except Failure {e : Expr ζ ℓ n // E ⊢ .recr η₁ s₁ ls₁ l ps₁ ms mins is maj ⤳ e}
  | .ctor η₂ s₂ _ _ _ _ _ => do
    let ⟨rfl, rfl⟩ ← η₂.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s₂ = s₁) (.reject .notDefEq)
    pure ⟨_, .iota⟩
  | _ => throw (.reject .notDefEq)

def quotIotaStep {n : Nat} (η : Head ζ .quot) (l₁ l₂ : Level ℓ)
    (α r β f h : Expr ζ ℓ n) : (a : Expr ζ ℓ n) →
    Except Failure {e : Expr ζ ℓ n // E ⊢ .quotLift η l₁ l₂ α r β f h a ⤳ e}
  | .quotMk η' _ _ _ _ => do
    let ⟨rfl⟩ ← guardProofOr (η' = η) (.reject .notDefEq)
    pure ⟨_, .quotIota⟩
  | _ => throw (.reject .notDefEq)

def quotIndIotaStep {n : Nat} (η : Head ζ .quot) (l : Level ℓ)
    (α r β f : Expr ζ ℓ n) : (a : Expr ζ ℓ n) →
    Except Failure {e : Expr ζ ℓ n // E ⊢ .quotInd η l α r β f a ⤳ e}
  | .quotMk η' _ _ _ _ => do
    let ⟨rfl⟩ ← guardProofOr (η' = η) (.reject .notDefEq)
    pure ⟨_, .quotIndIota⟩
  | _ => throw (.reject .notDefEq)

partial def whnfCore {n : Nat} :
    (e₁ : Expr ζ ℓ n) → Except Failure {e₂ : Expr ζ ℓ n // E ⊢ e₁ ⤳* e₂}
  | .app f₁ a => do
    let ⟨f₂, hred₁⟩ ← whnfCore f₁
    match f₂, hred₁ with
    | .lam _ e', hred₁ => do
      let ⟨e₂, hred₂⟩ ← whnfCore (e'.inst a)
      pure ⟨e₂, (WHRedS.frame (.app a) hred₁).trans ((ReflTransGen.single .beta).trans hred₂)⟩
    | f₂, hred₁ => pure ⟨.app f₂ a, WHRedS.frame (.app a) hred₁⟩
  | .const (kind := .def) η ls => do
    let ⟨e₂, hred⟩ ← whnfCore ((E.get η).defValue.instL ls).wkClosed
    pure ⟨e₂, (ReflTransGen.single .delta).trans hred⟩
  | .recr η s ls l ps ms mins is maj₁ => do
    let ⟨maj₂, hred₁⟩ ← whnfCore maj₁
    match iotaStep E η s ls l ps ms mins is maj₂ with
    | .ok ⟨e₂, hiota⟩ => do
      let ⟨e₃, hred₂⟩ ← whnfCore e₂
      pure ⟨e₃, (WHRedS.frame (.recr η s ls l ps ms mins is) hred₁).trans
        ((ReflTransGen.single hiota).trans hred₂)⟩
    | .error _ =>
      pure ⟨.recr η s ls l ps ms mins is maj₂, WHRedS.frame (.recr η s ls l ps ms mins is) hred₁⟩
  | .letE _ v e' => do
    let ⟨e₂, hred⟩ ← whnfCore (e'.inst v)
    pure ⟨e₂, (ReflTransGen.single .zeta).trans hred⟩
  | .quotLift η l₁ l₂ α r β f h a₁ => do
    let ⟨a₂, hred₁⟩ ← whnfCore a₁
    match quotIotaStep E η l₁ l₂ α r β f h a₂ with
    | .ok ⟨e₂, hiota⟩ => do
      let ⟨e₃, hred₂⟩ ← whnfCore e₂
      pure ⟨e₃, (WHRedS.frame (.quotLift η l₁ l₂ α r β f h) hred₁).trans
        ((ReflTransGen.single hiota).trans hred₂)⟩
    | .error _ =>
      pure ⟨.quotLift η l₁ l₂ α r β f h a₂, WHRedS.frame (.quotLift η l₁ l₂ α r β f h) hred₁⟩
  | .quotInd η l α r β f a₁ => do
    let ⟨a₂, hred₁⟩ ← whnfCore a₁
    match quotIndIotaStep E η l α r β f a₂ with
    | .ok ⟨e₂, hiota⟩ => do
      let ⟨e₃, hred₂⟩ ← whnfCore e₂
      pure ⟨e₃, (WHRedS.frame (.quotInd η l α r β f) hred₁).trans
        ((ReflTransGen.single hiota).trans hred₂)⟩
    | .error _ =>
      pure ⟨.quotInd η l α r β f a₂, WHRedS.frame (.quotInd η l α r β f) hred₁⟩
  | e₁ => pure ⟨e₁, .refl⟩

end Metalean.Checker
