/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Context
public import Metalean.Typing.Env.Defs
import Metalean.Semantics.Inversion

@[expose] public section

namespace Metalean

open Relation

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem TypeEq.sort_inj (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {l₁ l₂ : Level ℓ}
    (h : E[Γ] ⊢ .sort l₁ ≡ .sort l₂ typ) : l₁ = l₂ :=
  TypeEq.sort_model_inj hE hΓ h

theorem TypeEq.forallE_inj
    {t₁ t₂ : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    EnvWF E →
    E[Γ] ⊢ ok →
    E[Γ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ →
    E[Γ] ⊢ t₁ ≡ t₂ typ ∧ E[Γ.snoc t₁] ⊢ t₁' ≡ t₂' typ :=
  fun hE hΓ h =>
    have ⟨h₁, h₂, _⟩ := TypeEq.forallE_model_inj hE hΓ h
    ⟨h₁, h₂⟩

theorem Defeq.ind_inj {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} :
    EnvWF E →
    E[Γ] ⊢ ok →
    E[Γ] ⊢ .ind η s ls₁ ps₁ is₁ ≡
      .ind η s ls₂ ps₂ is₂ :
        .sort ((E.get η).block.level.inst ls₁) →
    ls₁ = ls₂ ∧
      (∀ p, ∃ t : Expr ζ ℓ n, E[Γ] ⊢ ps₁ p ≡ ps₂ p : t) ∧
      ∀ index, ∃ t : Expr ζ ℓ n,
        E[Γ] ⊢ is₁ index ≡ is₂ index : t :=
  fun hE => ind_model_inv hE

theorem TypeEq.quot_inj
    {η : Head ζ .quot} {l₁ l₂ : Level ℓ} {α α' r r' : Expr ζ ℓ n} :
    EnvWF E →
    E[Γ] ⊢ ok →
    E[Γ] ⊢ .quot η l₁ α r ≡ .quot η l₂ α' r' typ →
    l₁ = l₂ ∧ E[Γ] ⊢ α ≡ α' typ ∧ E[Γ] ⊢ r ≡ r' : Quot.relType α :=
  fun hE hΓ h =>
    have ⟨hl, hα, hr⟩ := h.quot_model_inj hE hΓ
    ⟨hl, .ofDefEq hα, hr⟩

theorem TypeEq.forallE_congr {t : Expr ζ ℓ n} {l : Level ℓ}
    {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ t : .sort l →
    E[Γ.snoc t] ⊢ t₁' ≡ t₂' typ →
    E[Γ] ⊢ .forallE t t₁' ≡ .forallE t t₂' typ := by
  intro ht h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (.forallEDF ht h h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem TypeEq.instCongr {t v : Expr ζ ℓ n}
    {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ v : t →
    E[Γ.snoc t] ⊢ t₁' ≡ t₂' typ →
    E[Γ] ⊢ t₁'.inst v ≡ t₂'.inst v typ := by
  intro hΓ hv h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (h.substitution (SubstWF.inst hΓ hv))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Metalean
