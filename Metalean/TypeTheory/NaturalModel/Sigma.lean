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

universe u

variable {C : Type u} [SmallCategory C]

class HasSigma (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] where
  sigma {Γ : C} (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) : y Γ ⟶ Ty
  iso {Γ : C} (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    ext B ≅ ext (sigma A B)
  iso_disp {Γ : C} (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    (iso A B).hom ≫ disp (sigma A B) = disp B ≫ disp A
  subst_sigma {Γ Δ : C} (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty)
    (B : y (ext A) ⟶ Ty) :
    y σ ≫ sigma A B =
      sigma (y σ ≫ A) (y (extMap σ A) ≫ B)

variable {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm] [HasSigma Ty Tm]
  {Γ Δ : C}

def sigmaFst (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    ext (HasSigma.sigma A B) ⟶ ext A :=
  (HasSigma.iso A B).inv ≫ disp B

theorem sigmaFst_disp (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    sigmaFst A B ≫ disp A = disp (HasSigma.sigma A B) := by
  simp [sigmaFst, ← HasSigma.iso_disp A B]

def sigmaSnd (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    Tm.obj (op (ext (HasSigma.sigma A B))) :=
  termOfHom B (HasSigma.iso A B).inv

theorem sigmaSnd_typing (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    ℳ.typing.app _ (sigmaSnd A B) = yonedaEquiv (y (sigmaFst A B) ≫ B) := by
  rw [sigmaSnd, termOfHom_typing, sigmaFst]

def sigmaSect (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (f : Sect A)
    (g : Sect (y f.hom ≫ B)) : Sect (HasSigma.sigma A B) where
  hom := g.hom ≫ extMap f.hom B ≫ (HasSigma.iso A B).hom
  hom_disp := by
    rw [Category.assoc, Category.assoc, HasSigma.iso_disp, ← Category.assoc (extMap f.hom B)]
    simp [extMap_disp, f.hom_disp, g.hom_disp]

end Metalean.TypeTheory.NaturalModel
