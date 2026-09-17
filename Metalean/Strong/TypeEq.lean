/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat} {Γ : Ctx ζ ℓ 0 n} {u : Level ℓ}

def IsTypeEq (E : Env ζ) {ℓ n : Nat} (Γ : Ctx ζ ℓ 0 n) :
    Expr ζ ℓ n → Expr ζ ℓ n → Prop :=
  Relation.TransGen fun t₁ t₂ => ∃ u, E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort u

notation:65 E "[" Γ "]" " ⊢ₛ " t₁:51 " ≡ " t₂:51 " typ" => IsTypeEq E Γ t₁ t₂

variable {e₁ e₂ t t₁ t₂ t₃ : Expr ζ ℓ n}

namespace IsTypeEq

theorem ofDefEq :
    E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort u →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ :=
  fun h => .single ⟨u, h⟩

theorem symm :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ] ⊢ₛ t₂ ≡ t₁ typ := by
  intro h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨u, h⟩ := h
    exact .single ⟨u, h.symm⟩
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem trans :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ] ⊢ₛ t₂ ≡ t₃ typ →
    E[Γ] ⊢ₛ t₁ ≡ t₃ typ :=
  Relation.TransGen.trans

theorem convStrong :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁ →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t₂ := by
  intro h
  suffices goal : E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁ ↔ E[Γ] ⊢ₛ e₁ ≡ e₂ : t₂ from goal.mp
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact ⟨.defeqDF h, .defeqDF h.symm⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem isType :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ] ⊢ₛ t₁ typ ∧ E[Γ] ⊢ₛ t₂ typ := by
  intro h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨l, h⟩ := h
    exact ⟨⟨l, h.left⟩, ⟨l, h.right⟩⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

end IsTypeEq

theorem IsTypeStrong.isTypeEq {t : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ t typ →
    E[Γ] ⊢ₛ t ≡ t typ :=
  fun h => have ⟨_, h⟩ := h; .ofDefEq h

theorem DefeqStrong.snocConvTy {t₁ t₂ : Expr ζ ℓ n} (h : E[Γ] ⊢ₛ t₁ ≡ t₂ typ)
    {e₁ e₂ t' : Expr ζ ℓ (n + 1)} :
    E[Γ.snoc t₁] ⊢ₛ e₁ ≡ e₂ : t' →
    E[Γ.snoc t₂] ⊢ₛ e₁ ≡ e₂ : t' := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h => have ⟨_, h⟩ := h; exact h.snocConv
  | trans _ _ ih₁ ih₂ => exact fun d => ih₂ (ih₁ d)

theorem IsTypeEq.snocConvTy {t₁ t₂ : Expr ζ ℓ n}
    {e₁ e₂ : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ₛ e₁ ≡ e₂ typ →
    E[Γ.snoc t₂] ⊢ₛ e₁ ≡ e₂ typ := by
  intro h he
  induction he using Relation.TransGen.trans_induction_on with
  | single he =>
    have ⟨_, he⟩ := he
    exact .ofDefEq (DefeqStrong.snocConvTy h he)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem IsTypeEq.inst_congr₂ {t e₁ e₂ : Expr ζ ℓ n}
    {e₁' e₂' : Expr ζ ℓ (n + 1)} :
    E[Γ.snoc t] ⊢ₛ e₁' ≡ e₂' typ →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁'.inst e₁ ≡ e₂'.inst e₂ typ := by
  intro h he₁
  induction h using Relation.TransGen.trans_induction_on generalizing e₁ with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (DefeqStrong.inst_congr₂ h he₁)
  | trans _ _ ih₁ ih₂ => exact (ih₁ he₁).trans (ih₂ he₁.right)

theorem IsTypeEq.forallE_dom {t₁ t₂ : Expr ζ ℓ n} {t' : Expr ζ ℓ (n + 1)} {v : Level ℓ}
    (h : E[Γ] ⊢ₛ t₁ ≡ t₂ typ) :
    E[Γ.snoc t₁] ⊢ₛ t' ≡ t' : .sort v →
    E[Γ] ⊢ₛ .forallE t₁ t' ≡ .forallE t₂ t' typ := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact fun hb => .ofDefEq (.forallEDF h hb (DefeqStrong.snocConvTy (.ofDefEq h) hb))
  | trans h₁ _ ih₁ ih₂ => exact fun hb => (ih₁ hb).trans (ih₂ (DefeqStrong.snocConvTy h₁ hb))

theorem IsTypeEq.lam_dom {t₁ t₂ : Expr ζ ℓ n} {t' e' : Expr ζ ℓ (n + 1)} {v : Level ℓ}
    (h : E[Γ] ⊢ₛ t₁ ≡ t₂ typ) :
    E[Γ.snoc t₁] ⊢ₛ t' : .sort v →
    E[Γ.snoc t₁] ⊢ₛ e' : t' →
    E[Γ] ⊢ₛ .lam t₁ e' ≡ .lam t₂ e' : .forallE t₁ t' := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact fun ht' he' => .lamDF h ht' (DefeqStrong.snocConvTy (.ofDefEq h) ht') he'
      (DefeqStrong.snocConvTy (.ofDefEq h) he')
  | trans h₁ _ ih₁ ih₂ =>
    exact fun ht' he' => (ih₁ ht' he').trans ((IsTypeEq.forallE_dom h₁ ht').symm.convStrong
      (ih₂ (DefeqStrong.snocConvTy h₁ ht') (DefeqStrong.snocConvTy h₁ he')))

theorem IsTypeEq.forallE_cod {t : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} {u : Level ℓ} :
    E[Γ] ⊢ₛ t : .sort u →
    E[Γ.snoc t] ⊢ₛ t₁' ≡ t₂' typ →
    E[Γ] ⊢ₛ .forallE t t₁' ≡ .forallE t t₂' typ := by
  intro ht h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (.forallEDF ht h h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem IsTypeStrong.snocConvTy {t₁ t₂ : Expr ζ ℓ n}
    {t' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ₛ t' typ →
    E[Γ.snoc t₂] ⊢ₛ t' typ :=
  fun h ht' =>
    have ⟨u, ht'⟩ := ht'
    ⟨u, DefeqStrong.snocConvTy h ht'⟩

section

variable {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}

theorem IsTypeEq.substitution {σ : Subst ζ ℓ n m} {t₁ t₂ : Expr ζ ℓ n} :
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₁] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ₂] ⊢ₛ t₁.subst σ ≡ t₂.subst σ typ := by
  intro hσ h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (h.substitution hσ)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem SubstWFStrong.snocConv {t₁ t₂ : Expr ζ ℓ m}
    {σ : Subst ζ ℓ n (m + 1)} :
    E[Γ₂] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ₂.snoc t₁] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₂.snoc t₂] ⊢ₛ σ ⊣ Γ₁ :=
  fun h hσ v => DefeqStrong.snocConvTy h (hσ v)

end

end Metalean
