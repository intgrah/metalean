/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Telescope
import Metalean.Typing.Substitution
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat}
  {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ 0 m}
  {σ₁ σ₂ : Subst ζ ℓ m n}

theorem SubstEq.of_proof_or_eq :
    E[Δ] ⊢ ok →
    E[Γ] ⊢ σ₁ ⊣ Δ →
    E[Γ] ⊢ σ₂ ⊣ Δ →
    (∀ v,
      E[Γ] ⊢ (Δ.get v).subst σ₁ : .prop ∨
      E[Γ] ⊢ σ₁ v ≡ σ₂ v : (Δ.get v).subst σ₁) →
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Δ := by
  intro hΔ hσ₁ hσ₂ h
  induction hΔ with
  | nil => exact .nil
  | @snoc m Δ t hΔ ht ih =>
    have hσ := ih hσ₁.wk_comp hσ₂.wk_comp fun v => by simpa [Expr.wk_subst] using h v.castSucc
    intro v
    cases v using Fin.lastCases with
    | cast v => simpa [Expr.wk_subst] using hσ v
    | last =>
      rcases h (Fin.last m) with hp | hlast
      · have ⟨u, ht⟩ := ht
        have htypes : E[Γ] ⊢ (Ctx.get (Fin.last m) (Δ.snoc t)).subst σ₂ ≡
            (Ctx.get (Fin.last m) (Δ.snoc t)).subst σ₁ : .sort u := by
          simpa [Expr.wk_subst] using ((CtxWF.teleWF hΔ).substitution_congr hσ ht).symm
        exact .proofIrrel hp (hσ₁ _) (.defeqDF htypes (hσ₂ _))
      · exact hlast

theorem Ctx.pi_prop {k : Nat} (Θ : Ctx ζ ℓ n k) {p : Expr ζ ℓ k} :
    E[Γ ++ Θ] ⊢ ok →
    E[Γ ++ Θ] ⊢ p : .prop →
    E[Γ] ⊢ Θ.pi p : .prop := by
  intro hΓΘ hp
  induction Θ with
  | nil => exact hp
  | snoc Θ t ih =>
    have .snoc hΓΘ ⟨u, ht⟩ := hΓΘ
    have h := ht.forallEDF hp hp
    rw [Level.imax_zero] at h
    exact ih hΓΘ h

end Metalean
