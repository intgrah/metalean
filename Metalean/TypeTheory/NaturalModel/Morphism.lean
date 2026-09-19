/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Pi
public import Metalean.TypeTheory.NaturalModel.Sort

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

namespace Morphism

variable {Ty Ty'} (F : Morphism Ty Ty') {Γ : C}

def extComparison (A : y Γ ⟶ Ty) : F.onCtx.obj (ext A) ⟶ ext (F.onTy Γ A) :=
  substTerm (F.onTy Γ A) (F.onCtx.map (disp A)) (F.onTm _ (genericTerm A)) (by
    rw [F.onTm_typing, ← F.onTy_subst, genericTerm_typing, Equiv.symm_apply_apply])

instance isIso_extComparison (A : y Γ ⟶ Ty) : IsIso (F.extComparison A) :=
  F.preservesExt A

def extIso (A : y Γ ⟶ Ty) : F.onCtx.obj (ext A) ≅ ext (F.onTy Γ A) :=
  asIso (F.extComparison A)

variable {ℓ : Nat} [HasSorts Ty Tm ℓ] [HasSorts Ty' Tm' ℓ]

class PreservesSorts : Prop where
  onTy_sort {Γ : C} (v : Level ℓ) :
    F.onTy Γ (HasSorts.sort v Γ) = HasSorts.sort v (F.onCtx.obj Γ)
  onTy_el {Γ : C} (v : Level ℓ) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (HasSorts.sort v Γ)) :
    F.onTy Γ (HasSorts.el v t ht) =
      HasSorts.el v (F.onTm Γ t) (by
        rw [F.onTm_typing, ht, Equiv.symm_apply_apply, onTy_sort])

variable [HasPi Ty Tm] [HasPi Ty' Tm']

class PreservesPi : Prop where
  onTy_piCode {Γ : C} (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    F.onTy Γ (piCode A B) =
      piCode (F.onTy Γ A) (y (inv (F.extComparison A)) ≫ F.onTy (ext A) B)

end Morphism

end Metalean.TypeTheory.NaturalModel
