/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Sort

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {ℓ : Nat} {Γ : C}

def relFst (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty) : ext R ⟶ ext A :=
  disp R ≫ disp (y (disp A) ≫ A)

def relSnd (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty) : ext R ⟶ ext A :=
  disp R ≫ extMap (disp A) A

theorem relFst_disp (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty) :
    relFst A R ≫ disp A = relSnd A R ≫ disp A := by
  rw [relFst, relSnd, Category.assoc, Category.assoc, extMap_disp]

class HasQuot (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (ℓ : Nat) [HasSorts Ty Tm ℓ] where
  quot {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    y Γ ⟶ Ty
  isSort_quot {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) (v : Level ℓ) :
    HasSorts.IsSort A v →
    HasSorts.IsSort (quot A R hR) v
  toQuot {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    ext A ⟶ ext (quot A R hR)
  toQuot_disp {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    toQuot A R hR ≫ disp (quot A R hR) = disp A
  toQuot_epi {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    Epi (toQuot A R hR)
  sound {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    relFst A R ≫ toQuot A R hR = relSnd A R ≫ toQuot A R hR
  lift {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) (B : y Γ ⟶ Ty) (f : Sect (y (disp A) ≫ B))
    (hf : Tm.map (relFst A R).op f.term = Tm.map (relSnd A R).op f.term) :
    Sect (y (disp (quot A R hR)) ≫ B)
  lift_toQuot {Γ : C} (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) (B : y Γ ⟶ Ty) (f : Sect (y (disp A) ≫ B))
    (hf : Tm.map (relFst A R).op f.term = Tm.map (relSnd A R).op f.term) :
    Tm.map (toQuot A R hR).op (lift A R hR B f hf).term = f.term
  substRel {Γ Δ : C} (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    y (ext (y (disp (y σ ≫ A)) ≫ y σ ≫ A)) ⟶ Ty
  isSort_substRel {Γ Δ : C} (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    HasSorts.IsSort (substRel σ A R hR) (Level.zero : Level ℓ)
  subst_quot {Γ Δ : C} (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    y σ ≫ quot A R hR =
      quot (y σ ≫ A) (substRel σ A R hR) (isSort_substRel σ A R hR)

end Metalean.TypeTheory.NaturalModel
