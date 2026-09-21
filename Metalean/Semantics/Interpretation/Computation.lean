/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Interpretation
public import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Interpretation.Binder.Support

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}
  {t e : Expr ζ ℓ Γ₁.as.len} {e' : Expr ζ ℓ (Γ₁.as.len + 1)} {u : Level ℓ}

theorem rawInterpret_beta (D : CodeAssignment E ℓ)
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (he : E[Γ₁.as.ctx] ⊢ₛ e : t)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hF : (RawFamily.normalizedBodyAction D (CtxCat.rawComprehension ht) (rawInterpret D Γ₁ t)
      (rawInterpret D (CtxCat.extension Γ₁ ht) e') σ ρ).IsIdealValued)
    (hX : ((rawInterpret D Γ₁ e).app _ σ.op ρ).IsDirected)
    (iha : D.rawExtend ((rawInterpret D Γ₁ t).app _ σ.op ρ)
      ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he))
      ((rawInterpret D Γ₁ e).app _ σ.op ρ) = (rawInterpret D Γ₁ e).app _ σ.op ρ)
    (ihb : (rawInterpret D (CtxCat.extension Γ₁ ht) e').app _ (σ ≫ (Raw.ContextSection.ofTerm ht he).hom).op
        (ρ.push ((rawInterpret D Γ₁ e).app _ σ.op ρ)) =
      (rawInterpret D Γ₁ (e'.inst e)).app _ σ.op ρ) :
    (rawInterpret D Γ₁ (.app (.lam t e') e)).app _ σ.op ρ =
      (rawInterpret D Γ₁ (e'.inst e)).app _ σ.op ρ := by
  rw [rawInterpret_app, rawInterpret_lam D ht, ← ihb]
  conv_rhs => rw [← iha]
  refine (RawFamily.rawApplication_normalizedAbstraction_eq_value D (CtxCat.rawComprehension ht) _
    (rawInterpret_isFinitary D (Γ₁.extension ht) e') σ ρ hF (((rawInterpret D Γ₁ e).app _ σ.op ρ).toIdeal hX)
    _ _ (Set.mem_image_of_mem ((Tm E ℓ).map σ.op) (RawFamily.label_mem_sourceQuery he))
    fun {_} σ₂ _ hlabel hs => by
      rw [← Functor.map_comp_apply]
      exact RawFamily.sourceQuery_eq_of_section ht he (σ₂ ≫ σ) (by simpa using hlabel) hs).trans ?_
  exact RawFamily.sectionValue_eq_value (CtxCat.rawComprehension ht) _ σ ρ _ _
    ((Raw.ContextSection.ofTerm ht he).pullbackId σ)

end Metalean.CoherentShape
