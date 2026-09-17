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

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {Γ Δ : C}

def IsProp (A : y Γ ⟶ Ty) : Prop :=
  Mono (y (disp A))

theorem isProp_of_subsingleton {A : y Γ ⟶ Ty}
    (h : ∀ {Δ : C} (σ : Δ ⟶ Γ),
      {t : Tm.obj (op Δ) | ℳ.typing.app (op Δ) t = yonedaEquiv (y σ ≫ A)}.Subsingleton) :
    IsProp A := by
  constructor
  intro X f g hfg
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro x
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app hfg Δ) x
  refine Section.hom_eq (h := (comprehension A).isPullback)
    (σ := f.app Δ x ≫ disp A) (a := termOfHom A (f.app Δ x)) ⟨f.app Δ x, rfl, rfl⟩
    ⟨g.app Δ x, hcomp.symm, ?_⟩
  exact h (f.app Δ x ≫ disp A)
    ((termOfHom_typing A _).trans (congrArg (yonedaEquiv <| y · ≫ A) hcomp.symm))
    (termOfHom_typing A _)

theorem IsProp.subst (σ : Δ ⟶ Γ) {A : y Γ ⟶ Ty} (h : IsProp A) : IsProp (y σ ≫ A) := by
  have : Mono (y (disp A)) := h
  constructor
  intro X f g hfg
  refine (ext_isPullback (y σ ≫ A)).hom_ext ?_ hfg
  have hextMap : f ≫ y (extMap σ A) = g ≫ y (extMap σ A) := by
    rw [← cancel_mono (y (disp A)), Category.assoc, Category.assoc, ← Functor.map_comp,
      extMap_disp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hfg]
  rw [← extMap_var, ← Category.assoc, ← Category.assoc, hextMap]

end Metalean.TypeTheory.NaturalModel
