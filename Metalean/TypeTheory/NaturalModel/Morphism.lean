/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Extension

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u v

variable {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
  (Ty : Cᵒᵖ ⥤ Type u) {Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  (Ty' : Dᵒᵖ ⥤ Type v) {Tm' : Dᵒᵖ ⥤ Type v} [ℳ' : NaturalModel Ty' Tm']

structure Morphism where
  onCtx : C ⥤ D
  onTy (Γ : C) : (y Γ ⟶ Ty) → (y (onCtx.obj Γ) ⟶ Ty')
  onTm (Γ : C) : Tm.obj (op Γ) → Tm'.obj (op (onCtx.obj Γ))
  onTm_typing (Γ : C) (t : Tm.obj (op Γ)) :
    ℳ'.typing.app (op (onCtx.obj Γ)) (onTm Γ t) =
      yonedaEquiv (onTy Γ (yonedaEquiv.symm (ℳ.typing.app (op Γ) t)))
  onTy_subst {Γ Δ : C} (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    onTy Δ (y σ ≫ A) = y (onCtx.map σ) ≫ onTy Γ A
  onTm_subst {Γ Δ : C} (σ : Δ ⟶ Γ) (t : Tm.obj (op Γ)) :
    onTm Δ (Tm.map σ.op t) = Tm'.map (onCtx.map σ).op (onTm Γ t)
  preservesExt {Γ : C} (A : y Γ ⟶ Ty) :
    IsIso (substTerm (onTy Γ A) (onCtx.map (disp A))
      (onTm _ (genericTerm A)) (by
        rw [onTm_typing, ← onTy_subst, genericTerm_typing, Equiv.symm_apply_apply]))

end Metalean.TypeTheory.NaturalModel
