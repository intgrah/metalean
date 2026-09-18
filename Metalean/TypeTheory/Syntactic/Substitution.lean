/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Comprehension

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Limits TypeTheory TypeTheory.NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {t : Expr ζ ℓ Γ₂.as.len} {t₁ t₂ : Expr ζ ℓ Γ₁.as.len} {u u₁ u₂ : Level ℓ}

namespace CtxCat

def extensionMap (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) :
    extension Γ₁ (ht.substitution σ.typed) ⟶ extension Γ₂ ht :=
  RawCtx.toCtx.map (σ.lift ⟨u, ht⟩)

theorem extensionMap_projection (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) :
    extensionMap ht σ ≫ rawProjection Γ₂ ht =
      rawProjection Γ₁ (ht.substitution σ.typed) ≫ RawCtx.toCtx.map σ := by
  change RawCtx.toCtx.map (σ.lift ⟨u, ht⟩) ≫ RawCtx.toCtx.map (projectionRaw Γ₂ ht) =
    RawCtx.toCtx.map (projectionRaw Γ₁ (ht.substitution σ.typed)) ≫ RawCtx.toCtx.map σ
  rw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_comp]
  congr 1
  apply RawCtx.Hom.ext
  funext v
  change σ.subst.lift v.castSucc = (σ.subst v).subst Subst.wk
  rw [Subst.lift_castSucc, Expr.subst_wk]

@[simp]
theorem map_extensionMap_binderVar (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) :
    (Tm E ℓ).map (extensionMap ht σ).op (Tm.rawBinderVar Γ₂.as ht) =
      Tm.rawBinderVar Γ₁.as (ht.substitution σ.typed) :=
  (Tm.map_varLabel (σ.lift ⟨u, ht⟩) _).trans (Tm.label_eq_var _ (Subst.lift_last σ.subst))

theorem extensionIsPullback (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) :
    IsPullback (extensionMap ht σ)
      (rawProjection Γ₁ (ht.substitution σ.typed))
      (rawProjection Γ₂ ht) (RawCtx.toCtx.map σ) := by
  apply IsPullback.of_map yoneda (extensionMap_projection ht σ)
  have hq : y (extensionMap ht σ) ≫ yonedaEquiv.symm (Tm.rawBinderVar Γ₂.as ht) =
      yonedaEquiv.symm (Tm.rawBinderVar Γ₁.as (ht.substitution σ.typed)) := by
    rw [yonedaEquiv_symm_naturality_left, map_extensionMap_binderVar]
  have hA : y (RawCtx.toCtx.map σ) ≫ yonedaEquiv.symm (Ty.ofTyping Γ₂.as ht) =
      yonedaEquiv.symm (Ty.ofTyping Γ₁.as (ht.substitution σ.typed)) := by
    rw [yonedaEquiv_symm_naturality_left, Ty.map_ofTyping]
  have h := rawExtensionIsRepresented (ht.substitution σ.typed)
  rw [← hq, ← hA] at h
  exact h.of_right (by simpa using congrArg yoneda.map (extensionMap_projection ht σ))
    (rawExtensionIsRepresented ht)

def contextConversionRaw (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ typ) (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u₁)
    (ht₂ : E[Γ₁.as.ctx] ⊢ₛ t₂ : .sort u₂) :
    (extension Γ₁ ht₂).as ⟶ (extension Γ₁ ht₁).as :=
  RawCtx.Hom.convert Γ₁.as h

def contextConversion (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ typ) (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u₁)
    (ht₂ : E[Γ₁.as.ctx] ⊢ₛ t₂ : .sort u₂) :
    extension Γ₁ ht₂ ⟶ extension Γ₁ ht₁ :=
  RawCtx.toCtx.map (contextConversionRaw h ht₁ ht₂)

instance contextConversion_isIso (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ typ)
    (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u₁) (ht₂ : E[Γ₁.as.ctx] ⊢ₛ t₂ : .sort u₂) :
    IsIso (contextConversion h ht₁ ht₂) :=
  let i : (extension Γ₁ ht₂).as ≅ (extension Γ₁ ht₁).as := {
    hom := contextConversionRaw h ht₁ ht₂
    inv := contextConversionRaw h.symm ht₂ ht₁
    hom_inv_id := RawCtx.Hom.ext rfl
    inv_hom_id := RawCtx.Hom.ext rfl }
  inferInstanceAs (IsIso (RawCtx.toCtx.mapIso i).hom)

@[simp]
theorem contextConversion_projection (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ typ)
    (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u₁) (ht₂ : E[Γ₁.as.ctx] ⊢ₛ t₂ : .sort u₂) :
    contextConversion h ht₁ ht₂ ≫ rawProjection Γ₁ ht₁ = rawProjection Γ₁ ht₂ := by
  change RawCtx.toCtx.map (contextConversionRaw h ht₁ ht₂) ≫
    RawCtx.toCtx.map (projectionRaw Γ₁ ht₁) =
      RawCtx.toCtx.map (projectionRaw Γ₁ ht₂)
  rw [← RawCtx.toCtx.map_comp]
  congr 1

@[simp]
theorem contextConversion_binderVar (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ typ)
    (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u₁) (ht₂ : E[Γ₁.as.ctx] ⊢ₛ t₂ : .sort u₂) :
    (Tm E ℓ).map (contextConversion h ht₁ ht₂).op (Tm.rawBinderVar Γ₁.as ht₁) =
      Tm.rawBinderVar Γ₁.as ht₂ :=
  (Tm.map_varLabel (contextConversionRaw h ht₁ ht₂) _).trans (Tm.label_eq_var _ rfl)

end CtxCat

namespace Ty.Repr

variable {X : (CtxCat E ℓ)ᵒᵖ ⥤ Type}

theorem eval_conversion (T₁ T₂ : Repr Γ₁) (h : E[Γ₁.as.ctx] ⊢ₛ T₁.term ≡ T₂.term typ)
    (A : y Γ₁ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ X)
    (h₁ : A = T₁.comprehension.type) (h₂ : A = T₂.comprehension.type) :
    T₂.comprehension.eval A B h₂ =
      X.map (RawCtx.toCtx.map (RawCtx.Hom.convert Γ₁.as h)).op (T₁.comprehension.eval A B h₁) :=
  have ⟨_, ht₁⟩ := T₁.wf
  have ⟨_, ht₂⟩ := T₂.wf
  (CtxCat.rawComprehension ht₁).eval_eq (CtxCat.rawComprehension ht₂)
    (CtxCat.contextConversion h ht₁ ht₂) (CtxCat.contextConversion_projection h ht₁ ht₂)
    (CtxCat.contextConversion_binderVar h ht₁ ht₂) A B h₁ h₂

theorem eval_reindex (T : Repr Γ₁) (σ : Γ₂.as ⟶ Γ₁.as)
    (A : y Γ₁ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ X)
    (hT : A = T.comprehension.type) :
    (T.reindex σ).comprehension.eval (y (RawCtx.toCtx.map σ) ≫ A)
        (fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B)
        (by rw [hT]; exact T.comprehension_type_reindex σ) =
      X.map (RawCtx.toCtx.map (σ.lift T.wf)).op (T.comprehension.eval A B hT) :=
  have ⟨_, ht⟩ := T.wf
  (CtxCat.rawComprehension ht).eval_reindex (CtxCat.rawComprehension (ht.substitution σ.typed))
    (RawCtx.toCtx.map σ) (CtxCat.extensionMap ht σ) (CtxCat.extensionMap_projection ht σ)
    (CtxCat.map_extensionMap_binderVar ht σ) A B hT _

end Ty.Repr

end Metalean
