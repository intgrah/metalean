/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Context
import Metalean.Strong.Strengthen
import Metalean.Semantics.Inversion

@[expose] public section

namespace Metalean

open Relation

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem IsTypeEq.sort_inj (ho : E.Ordered) (hΓ : E[Γ] ⊢ₛ ok) {l₁ l₂ : Level ℓ}
    (h : E[Γ] ⊢ₛ .sort l₁ ≡ .sort l₂ typ) : l₁ = l₂ :=
  IsTypeEq.sort_model_inj ho hΓ h

theorem IsTypeEq.forallE_inj (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ ∧ E[Γ.snoc t₁] ⊢ₛ t₁' ≡ t₂' typ :=
  fun hΓ h =>
    have ⟨h₁, h₂, _⟩ := IsTypeEq.forallE_model_inj ho hΓ h
    ⟨h₁, h₂⟩

theorem DefeqStrong.ind_inj (ho : E.Ordered)
    {ι : IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .ind η s ls₁ ps₁ is₁ ≡
      .ind η s ls₂ ps₂ is₂ :
        .sort ((E.get η).block.level.inst ls₁) →
    ls₁ = ls₂ ∧
      (∀ p, ∃ t : Expr ζ ℓ n, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : t) ∧
      ∀ index, ∃ t : Expr ζ ℓ n,
        E[Γ] ⊢ₛ is₁ index ≡ is₂ index : t :=
  ind_model_inv ho

theorem IsTypeEq.quot_inj (ho : E.Ordered)
    {η : Head ζ .quot} {l₁ l₂ : Level ℓ} {α α' r r' : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .quot η l₁ α r ≡ .quot η l₂ α' r' typ →
    l₁ = l₂ ∧ E[Γ] ⊢ₛ α ≡ α' typ ∧ E[Γ] ⊢ₛ r ≡ r' : Quot.relType α :=
  fun hΓ h =>
    have ⟨hl, hα, hr⟩ := h.quot_model_inj ho hΓ
    ⟨hl, .ofDefEq hα, hr⟩

theorem IsTypeEq.forallE_congr {t : Expr ζ ℓ n} {l : Level ℓ}
    {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ t : .sort l →
    E[Γ.snoc t] ⊢ₛ t₁' ≡ t₂' typ →
    E[Γ] ⊢ₛ .forallE t t₁' ≡ .forallE t t₂' typ := by
  intro ht h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (.forallEDF ht h h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem IsTypeEq.instCongr {t v : Expr ζ ℓ n}
    {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ v : t →
    E[Γ.snoc t] ⊢ₛ t₁' ≡ t₂' typ →
    E[Γ] ⊢ₛ t₁'.inst v ≡ t₂'.inst v typ := by
  intro hΓ hv h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (h.substitution (SubstWFStrong.inst hΓ hv))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Defeq.snocConv (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {l : Level ℓ}
    {e₁' e₂' t' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ t₁ ≡ t₂ : .sort l →
    E[Γ.snoc t₁] ⊢ e₁' ≡ e₂' : t' →
    E[Γ.snoc t₂] ⊢ e₁' ≡ e₂' : t' := by
  intro hΓ ht d
  have hS := ht.toStrongOrdered ho hΓ
  have dS := d.toStrongOrdered ho (hΓ.snoc ⟨l, hS.left⟩)
  exact (hS.snocConv dS).defeq

theorem IsTypeEq.snocConv (ho : E.Ordered)
    {e₁' e₂' t' : Expr ζ ℓ (n + 1)} {t₁ t₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    (E[Γ.snoc t₁] ⊢ e₁' ≡ e₂' : t' ↔ E[Γ.snoc t₂] ⊢ e₁' ≡ e₂' : t') := by
  intro hΓ h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact ⟨Defeq.snocConv ho hΓ h.defeq,
      Defeq.snocConv ho hΓ h.symm.defeq⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Metalean
