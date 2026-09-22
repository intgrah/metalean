/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.TypeEq
public import Metalean.Syntax.Weakening
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {t : Expr ζ ℓ n}

theorem IsType.wk (t₁ : Expr ζ ℓ n) :
    E[Γ] ⊢ t typ →
    E[Γ.snoc t₁] ⊢ t.wk typ :=
  fun h => have ⟨u, h⟩ := h; ⟨u, h.wk t₁⟩

theorem Defeq.wkClosed {e₁ e₂ t : Expr ζ ℓ 0} :
    E[#t[]] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₁.wkClosed ≡ e₂.wkClosed : t.wkClosed := by
  intro h
  induction Γ with
  | nil => exact h
  | snoc Γ t₃ ih => exact ih.wk t₃

theorem CtxWF.get (v : Var n) :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ Γ.get v typ := by
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

theorem CtxWF.var (v : Var n) :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ .var v : Γ.get v :=
  fun hΓ => have ⟨_, hv⟩ := hΓ.get v; .var hv

theorem SubstWF.inst {t e : Expr ζ ℓ n} :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ e : t →
    E[Γ] ⊢ Subst.id.extend e ⊣ Γ.snoc t := by
  intro hΓ he v
  cases v using Fin.lastCases with
  | last =>
    simpa [Expr.wk_subst_extend] using he
  | cast v =>
    rw [Γ.get_snoc t v.castSucc (Nat.ne_of_lt v.isLt), Subst.extend_castSucc]
    change E[Γ] ⊢ .var v : (Γ.get v).wk.inst e
    rw [Expr.inst_wk]
    exact hΓ.var v

theorem CtxWF.varLast :
    E[Γ.snoc t] ⊢ ok →
    E[Γ.snoc t] ⊢ .var (Fin.last n) : t.wk :=
  fun hΓ => by simpa using hΓ.var (Fin.last n)

theorem SubstWF.id :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ Subst.id ⊣ Γ :=
  fun hΓ v => by simp; exact hΓ.var v

theorem SubstWF.wk (t : Expr ζ ℓ n) :
    E[Γ] ⊢ ok →
    E[Γ.snoc t] ⊢ Subst.wk ⊣ Γ := by
  intro hΓ v
  rw [Expr.subst_wk]
  have h := (hΓ.var v).wk t
  rw [Expr.var_wk] at h
  exact h

end Metalean
