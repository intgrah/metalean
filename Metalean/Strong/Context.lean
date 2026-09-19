/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.TypeEq
public import Metalean.Typing.Context
public import Metalean.Syntax.Weakening
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {t : Expr ζ ℓ n}

theorem CtxWFStrong.toWF :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ ok := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc _ ht ih =>
    obtain ⟨u, ht⟩ := ht
    exact .snoc ih ⟨u, ht.defeq⟩

theorem IsTypeStrong.wk
    (t₁ : Expr ζ ℓ n) :
    E[Γ] ⊢ₛ t typ →
    E[Γ.snoc t₁] ⊢ₛ t.wk typ :=
  fun h =>
    have ⟨u, h⟩ := h
    ⟨u, h.wk t₁⟩

theorem DefeqStrong.wkClosed {e₁ e₂ t : Expr ζ ℓ 0} :
    E[#t[]] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁.wkClosed ≡ e₂.wkClosed : t.wkClosed := by
  intro h
  induction Γ with
  | nil => exact h
  | snoc Γ t₃ ih => exact ih.wk t₃

theorem CtxWFStrong.get
    (v : Var n) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ Γ.get v typ := by
  intro hΓ
  induction hΓ with
  | nil => exact Fin.elim0 v
  | @snoc n Γ t _ ht ih =>
    by_cases hv : v.val = n
    · rw [show Ctx.get v (Γ.snoc t) = t.wk by simp [Ctx.get, hv]]
      exact ht.wk t
    · rw [show Ctx.get v (Γ.snoc t) =
          (Ctx.get (v.castLT (by omega)) Γ).wk by simp [hv]]
      exact (ih (v.castLT (by omega))).wk t

theorem CtxWFStrong.var
    (v : Var n) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .var v ≡ .var v : Γ.get v :=
  fun hΓ =>
    have ⟨_, hv⟩ := hΓ.get v
    .var hv

theorem SubstWFStrong.inst
    {t e : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ e : t →
    E[Γ] ⊢ₛ Subst.id.extend e ⊣ Γ.snoc t := by
  intro hΓ he v
  cases v using Fin.lastCases with
  | last =>
    simpa [Expr.wk_subst_extend] using he
  | cast v =>
    rw [Γ.get_snoc t v.castSucc (Nat.ne_of_lt v.isLt), Subst.extend_castSucc]
    change E[Γ] ⊢ₛ .var v : (Γ.get v).wk.inst e
    rw [Expr.inst_wk]
    exact hΓ.var v

theorem CtxWFStrong.varLast :
    E[Γ.snoc t] ⊢ₛ ok →
    E[Γ.snoc t] ⊢ₛ .var (Fin.last n) : t.wk := by
  intro hΓ
  simpa using hΓ.var (Fin.last n)

theorem SubstWFStrong.id :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ Subst.id ⊣ Γ := by
  intro hΓ v
  rw [Expr.subst_id]
  exact hΓ.var v

theorem SubstWFStrong.wk (t : Expr ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    E[Γ.snoc t] ⊢ₛ Subst.wk ⊣ Γ := by
  intro hΓ v
  rw [Expr.subst_wk]
  have h := (hΓ.var v).wk t
  rw [Expr.var_wk] at h
  exact h

theorem DefeqStrong.lam_body {t' e₁' e₂' : Expr ζ ℓ (n + 1)}
    {u v : Level ℓ} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t : .sort u →
    E[Γ.snoc t] ⊢ₛ t' : .sort v →
    E[Γ.snoc t] ⊢ₛ e₁' : t' →
    E[Γ.snoc t] ⊢ₛ e₂' : t' →
    E[Γ] ⊢ₛ .lam t e₁' ≡ .lam t e₂' : .forallE t t' →
    E[Γ.snoc t] ⊢ₛ e₁' ≡ e₂' : t' := by
  intro hΓ ht ht' he₁ he₂ h
  have hwk := SubstWFStrong.wk t hΓ
  have hlift := SubstWFStrong.lift ⟨u, ht⟩ hwk
  have hx : E[Γ.snoc t] ⊢ₛ .var (Fin.last n) : t.subst Subst.wk := by
    rw [Expr.subst_wk]
    exact CtxWFStrong.varLast (Tele.Forall.snoc hΓ ⟨u, ht⟩)
  have htσ := ht.substitution hwk
  have ht'σ := ht'.substitution hlift
  have hres : E[Γ.snoc t] ⊢ₛ (t'.subst Subst.wk.lift).inst (.var (Fin.last n)) : .sort v := by
    rw [Expr.inst_subst_lift_wk_last]
    exact ht'
  have happ := DefeqStrong.appDF htσ ht'σ (h.substitution hwk) hx hres
  have hβ₁ := DefeqStrong.beta htσ ht'σ (he₁.substitution hlift) hx hres
    (by rw [Expr.inst_subst_lift_wk_last, Expr.inst_subst_lift_wk_last]; exact he₁)
  have hβ₂ := DefeqStrong.beta htσ ht'σ (he₂.substitution hlift) hx hres
    (by rw [Expr.inst_subst_lift_wk_last, Expr.inst_subst_lift_wk_last]; exact he₂)
  rw [Expr.inst_subst_lift_wk_last, Expr.inst_subst_lift_wk_last] at hβ₁ hβ₂
  rw [Expr.inst_subst_lift_wk_last] at happ
  exact hβ₁.symm.trans (happ.trans hβ₂)

end Metalean
