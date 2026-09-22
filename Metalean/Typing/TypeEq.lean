/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat} {Γ : Ctx ζ ℓ 0 n} {u : Level ℓ}

def TypeEq (E : Env ζ) {ℓ n : Nat} (Γ : Ctx ζ ℓ 0 n) :
    Expr ζ ℓ n → Expr ζ ℓ n → Prop :=
  Relation.TransGen fun t₁ t₂ => ∃ u, E[Γ] ⊢ t₁ ≡ t₂ : .sort u

notation:65 E "[" Γ "]" " ⊢ " t₁:51 " ≡ " t₂:51 " typ" => TypeEq E Γ t₁ t₂

variable {e₁ e₂ t t₁ t₂ t₃ : Expr ζ ℓ n}

namespace TypeEq

theorem ofDefEq :
    E[Γ] ⊢ t₁ ≡ t₂ : .sort u →
    E[Γ] ⊢ t₁ ≡ t₂ typ :=
  fun h => .single ⟨u, h⟩

theorem symm :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ t₂ ≡ t₁ typ := by
  intro h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨u, h⟩ := h
    exact .single ⟨u, h.symm⟩
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem trans :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ t₂ ≡ t₃ typ →
    E[Γ] ⊢ t₁ ≡ t₃ typ :=
  Relation.TransGen.trans

theorem conv :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ e₁ ≡ e₂ : t₁ →
    E[Γ] ⊢ e₁ ≡ e₂ : t₂ := by
  intro h
  suffices goal : E[Γ] ⊢ e₁ ≡ e₂ : t₁ ↔ E[Γ] ⊢ e₁ ≡ e₂ : t₂ from goal.mp
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact ⟨.defeqDF h, .defeqDF h.symm⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem regularity :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ t₁ typ ∧ E[Γ] ⊢ t₂ typ := by
  intro h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨l, h⟩ := h
    exact ⟨⟨l, h.left⟩, ⟨l, h.right⟩⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.left, ih₂.right⟩

theorem left :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ t₁ typ :=
  fun h => h.regularity.left

theorem right :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ] ⊢ t₂ typ :=
  fun h => h.regularity.right

end TypeEq

theorem IsType.typeEq {t : Expr ζ ℓ n} :
    E[Γ] ⊢ t typ →
    E[Γ] ⊢ t ≡ t typ :=
  fun h => have ⟨_, h⟩ := h; .ofDefEq h

theorem Defeq.snocConvTy {t₁ t₂ : Expr ζ ℓ n} (h : E[Γ] ⊢ t₁ ≡ t₂ typ)
    {e₁ e₂ t' : Expr ζ ℓ (n + 1)} :
    E[Γ.snoc t₁] ⊢ e₁ ≡ e₂ : t' →
    E[Γ.snoc t₂] ⊢ e₁ ≡ e₂ : t' := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h => have ⟨_, h⟩ := h; exact h.snocConv
  | trans _ _ ih₁ ih₂ => exact fun d => ih₂ (ih₁ d)

theorem TypeEq.snocConvTy {t₁ t₂ : Expr ζ ℓ n}
    {e₁ e₂ : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ e₁ ≡ e₂ typ →
    E[Γ.snoc t₂] ⊢ e₁ ≡ e₂ typ := by
  intro h he
  induction he using Relation.TransGen.trans_induction_on with
  | single he =>
    have ⟨_, he⟩ := he
    exact .ofDefEq (Defeq.snocConvTy h he)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem TypeEq.inst_congr₂ {t e₁ e₂ : Expr ζ ℓ n}
    {e₁' e₂' : Expr ζ ℓ (n + 1)} :
    E[Γ.snoc t] ⊢ e₁' ≡ e₂' typ →
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₁'.inst e₁ ≡ e₂'.inst e₂ typ := by
  intro h he₁
  induction h using Relation.TransGen.trans_induction_on generalizing e₁ with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (Defeq.inst_congr₂ h he₁)
  | trans _ _ ih₁ ih₂ => exact (ih₁ he₁).trans (ih₂ he₁.right)

theorem TypeEq.forallE_dom {t₁ t₂ : Expr ζ ℓ n} {t' : Expr ζ ℓ (n + 1)} {v : Level ℓ}
    (h : E[Γ] ⊢ t₁ ≡ t₂ typ) :
    E[Γ.snoc t₁] ⊢ t' : .sort v →
    E[Γ] ⊢ .forallE t₁ t' ≡ .forallE t₂ t' typ := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact fun hb => .ofDefEq (.forallEDF h hb (Defeq.snocConvTy (.ofDefEq h) hb))
  | trans h₁ _ ih₁ ih₂ => exact fun hb => (ih₁ hb).trans (ih₂ (Defeq.snocConvTy h₁ hb))

theorem TypeEq.lam_dom {t₁ t₂ : Expr ζ ℓ n} {t' e' : Expr ζ ℓ (n + 1)} {v : Level ℓ}
    (h : E[Γ] ⊢ t₁ ≡ t₂ typ) :
    E[Γ.snoc t₁] ⊢ t' : .sort v →
    E[Γ.snoc t₁] ⊢ e' : t' →
    E[Γ] ⊢ .lam t₁ e' ≡ .lam t₂ e' : .forallE t₁ t' := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact fun ht' he' => .lamDF h ht' (Defeq.snocConvTy (.ofDefEq h) ht') he'
      (Defeq.snocConvTy (.ofDefEq h) he')
  | trans h₁ _ ih₁ ih₂ =>
    exact fun ht' he' => (ih₁ ht' he').trans ((TypeEq.forallE_dom h₁ ht').symm.conv
      (ih₂ (Defeq.snocConvTy h₁ ht') (Defeq.snocConvTy h₁ he')))

theorem TypeEq.forallE_cod {t : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} {u : Level ℓ} :
    E[Γ] ⊢ t : .sort u →
    E[Γ.snoc t] ⊢ t₁' ≡ t₂' typ →
    E[Γ] ⊢ .forallE t t₁' ≡ .forallE t t₂' typ := by
  intro ht h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (.forallEDF ht h h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section

variable {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}

theorem TypeEq.substitution {σ : Subst ζ ℓ n m} {t₁ t₂ : Expr ζ ℓ n} :
    E[Γ₂] ⊢ σ ⊣ Γ₁ →
    E[Γ₁] ⊢ t₁ ≡ t₂ typ →
    E[Γ₂] ⊢ t₁.subst σ ≡ t₂.subst σ typ := by
  intro hσ h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact .ofDefEq (h.substitution hσ)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem SubstWF.snocConv {t₁ t₂ : Expr ζ ℓ m} {σ : Subst ζ ℓ n (m + 1)} :
    E[Γ₂] ⊢ t₁ ≡ t₂ typ →
    E[Γ₂.snoc t₁] ⊢ σ ⊣ Γ₁ →
    E[Γ₂.snoc t₂] ⊢ σ ⊣ Γ₁ :=
  fun h hσ v => Defeq.snocConvTy h (hσ v)

end

end Metalean
