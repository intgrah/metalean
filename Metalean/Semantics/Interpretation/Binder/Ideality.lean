/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Interpretation.Binder.Basic

@[expose] public section

namespace Metalean.CoherentShape.RawFamily

open CategoryTheory CodeAssignment Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ ΓA : CtxCat E ℓ}

theorem normalizedBodyAction_isIdealValued (hA : Comprehension (Ty E ℓ) Γ₁ ΓA)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hC : (C.app _ σ₁.op ρ).IsDirected)
    (hB : ∀ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (s : hA.Section (σ₂ ≫ σ₁) name)
      (J : Domain Γ₃),
      (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name J.val = J.val →
      (B.app _ s.hom.op ((ρ.pullback σ₂).push J.val)).IsDirected) :
    (normalizedBodyAction (piLimit E ℓ) hA C B σ₁ ρ).IsIdealValued := by
  intro Γ₃ σ₂ label I
  have hC' : (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected := by
    rw [op_comp, ← C.app_pullback]
    exact hC.pullback σ₂
  have hB' {Γ₄ : CtxCat E ℓ} (σ₃ : Γ₄ ⟶ Γ₃) (name : Tm_ Γ₄)
      (s : hA.Section (σ₃ ≫ σ₂ ≫ σ₁) name) (J : Domain Γ₄)
      (hfixed : (piLimit E ℓ).rawExtend
        (C.app _ (σ₃ ≫ σ₂ ≫ σ₁).op ((ρ.pullback σ₂).pullback σ₃)) name J.val = J.val) :
      (B.app _ s.hom.op (((ρ.pullback σ₂).pullback σ₃).push J.val)).IsDirected := by
    rw [RawValuation.pullback_comp] at hfixed ⊢
    have hB' := hB (σ₃ ≫ σ₂) name
    rw [Category.assoc] at hB'
    exact fun _ => hB' s J hfixed
  apply (bodySection hA B (σ₂ ≫ σ₁) (ρ.pullback σ₂) label _).isDirected
  intro Γ₄ σ₃ s
  have hC'' : (C.app _ (σ₃ ≫ σ₂ ≫ σ₁).op ((ρ.pullback σ₂).pullback σ₃)).IsDirected := by
    rw [op_comp, ← C.app_pullback]
    exact hC'.pullback σ₃
  change (B.app _ s.hom.op (((ρ.pullback σ₂).pullback σ₃).push
    (((piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) label I.val).pullback σ₃))).IsDirected
  rw [(piLimit E ℓ).pullback_rawExtend, C.app_pullback]
  exact hB' σ₃ ((Tm E ℓ).map σ₃.op label) s
    ⟨_, (piLimit E ℓ).rawExtend_isDirected _ hC'' (I.pullback σ₃).property⟩
    ((piLimit E ℓ).rawExtend_idempotent piLimit_isIdempotent _ hC'' (I.pullback σ₃).property)

end Metalean.CoherentShape.RawFamily
