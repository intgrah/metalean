/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Metalean.TypeTheory.NaturalModel.Defs

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm X Y : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {Γ Δ : C}

def fibreMap (A : X ⟶ Ty) (f : Y ⟶ X) :
    pullback (f ≫ A) ℳ.typing ⟶ pullback A ℳ.typing :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (by simpa using pullback.condition)

@[reassoc (attr := simp)] theorem fibreMap_fst (A : X ⟶ Ty) (f : Y ⟶ X) :
    fibreMap A f ≫ pullback.fst A ℳ.typing = pullback.fst (f ≫ A) ℳ.typing ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fibreMap_snd (A : X ⟶ Ty) (f : Y ⟶ X) :
    fibreMap A f ≫ pullback.snd A ℳ.typing = pullback.snd (f ≫ A) ℳ.typing :=
  pullback.lift_snd _ _ _

def fibreCast {A₁ A₂ : y Γ ⟶ Ty} (hA : A₁ = A₂) :
    pullback A₁ ℳ.typing ⟶ pullback A₂ ℳ.typing :=
  pullback.lift (pullback.fst A₁ ℳ.typing) (pullback.snd A₁ ℳ.typing)
    (by rw [← hA]; exact pullback.condition)

@[reassoc (attr := simp)] theorem fibreCast_fst {A₁ A₂ : y Γ ⟶ Ty} (hA : A₁ = A₂) :
    fibreCast hA ≫ pullback.fst A₂ ℳ.typing = pullback.fst A₁ ℳ.typing :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fibreCast_snd {A₁ A₂ : y Γ ⟶ Ty} (hA : A₁ = A₂) :
    fibreCast hA ≫ pullback.snd A₂ ℳ.typing = pullback.snd A₁ ℳ.typing :=
  pullback.lift_snd _ _ _

@[simp] theorem fibreCast_rfl (A : y Γ ⟶ Ty) : fibreCast (rfl : A = A) = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

theorem polynomial_ext {A₁ A₂ : y Γ ⟶ Ty} {B₁ : pullback A₁ ℳ.typing ⟶ X}
    {B₂ : pullback A₂ ℳ.typing ⟶ X} (hA : A₁ = A₂) (hB : B₁ = fibreCast hA ≫ B₂) :
    (⟨A₁, B₁⟩ : Σ A : y Γ ⟶ Ty, pullback A ℳ.typing ⟶ X) = ⟨A₂, B₂⟩ := by
  subst hA
  rw [hB, fibreCast_rfl, Category.id_comp]

@[implicit_reducible] def polynomial (Ty : Cᵒᵖ ⥤ Type u) {Tm : Cᵒᵖ ⥤ Type u}
    [ℳ : NaturalModel Ty Tm] : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u where
  obj X := {
    obj := fun ⟨Γ⟩ => Σ A : (y Γ : Cᵒᵖ ⥤ Type u) ⟶ Ty, pullback A ℳ.typing ⟶ X
    map σ := ↾fun ⟨A, B⟩ => ⟨y σ.unop ≫ A, fibreMap A (y σ.unop) ≫ B⟩
    map_id Γ := by
      apply ConcreteCategory.hom_ext
      intro ⟨A, B⟩
      exact polynomial_ext (by simp) (congrArg (· ≫ B) (pullback.hom_ext (by simp) (by simp)))
    map_comp σ₁ σ₂ := by
      apply ConcreteCategory.hom_ext
      intro ⟨A, B⟩
      refine polynomial_ext (by simp) ?_
      have key : fibreMap A (y (σ₁ ≫ σ₂).unop) =
          fibreCast (by simp) ≫ fibreMap (y σ₁.unop ≫ A) (y σ₂.unop) ≫ fibreMap A (y σ₁.unop) :=
        pullback.hom_ext (by simp) (by simp)
      exact (reassoc_of% key) B
  }
  map f := {
    app Γ := ↾fun ⟨A, B⟩ => ⟨A, B ≫ f⟩
    naturality _ _ _ := rfl
  }

@[simp] theorem polynomial_obj_map (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) :
    ((polynomial Ty).obj X).map σ.op ⟨A, B⟩ = ⟨y σ ≫ A, fibreMap A (y σ) ≫ B⟩ :=
  rfl

@[simp] theorem polynomial_map_app (f : X ⟶ Y) (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) :
    ((polynomial Ty).map f).app (op Γ) ⟨A, B⟩ = ⟨A, B ≫ f⟩ :=
  rfl

end Metalean.TypeTheory.NaturalModel
