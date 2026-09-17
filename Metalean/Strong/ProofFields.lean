/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Telescope
import Metalean.Strong.Substitution
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat}
  {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ 0 m}
  {σ₁ σ₂ : Subst ζ ℓ m n}

theorem SubstEqStrong.of_proof_or_eq :
    E[Δ] ⊢ₛ ok →
    E[Γ] ⊢ₛ σ₁ ⊣ Δ →
    E[Γ] ⊢ₛ σ₂ ⊣ Δ →
    (∀ v,
      E[Γ] ⊢ₛ (Δ.get v).subst σ₁ : .prop ∨
      E[Γ] ⊢ₛ σ₁ v ≡ σ₂ v : (Δ.get v).subst σ₁) →
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ Δ := by
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
        have htypes : E[Γ] ⊢ₛ (Ctx.get (Fin.last m) (Δ.snoc t)).subst σ₂ ≡
            (Ctx.get (Fin.last m) (Δ.snoc t)).subst σ₁ : .sort u := by
          simpa [Expr.wk_subst] using
            ((CtxWFStrong.wfTeleStrong hΔ).substitution_congr hσ ht).symm
        exact .proofIrrel hp (hσ₁ _) (.defeqDF htypes (hσ₂ _))
      · exact hlast

theorem Ctx.pi_propStrong {k : Nat} (Θ : Ctx ζ ℓ n k) {p : Expr ζ ℓ k} :
    E[Γ ++ Θ] ⊢ₛ ok →
    E[Γ ++ Θ] ⊢ₛ p : .prop →
    E[Γ] ⊢ₛ Θ.pi p : .prop := by
  intro hΓΘ hp
  induction Θ with
  | nil => exact hp
  | snoc Θ t ih =>
    have .snoc hΓΘ ⟨u, ht⟩ := hΓΘ
    have h := ht.forallEDF hp hp
    rw [Level.imax_zero] at h
    exact ih hΓΘ h

end Metalean
