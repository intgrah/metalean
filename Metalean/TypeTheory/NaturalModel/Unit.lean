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

class HasUnit (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] where
  unit (Γ : C) :
    y Γ ⟶ Ty
  subst_unit {Γ Δ : C} (σ : Δ ⟶ Γ) :
    y σ ≫ unit Γ = unit Δ
  star (Γ : C) :
    Γ ⟶ ext (unit Γ)
  star_disp (Γ : C) :
    star Γ ≫ disp (unit Γ) = 𝟙 Γ
  disp_star (Γ : C) :
    disp (unit Γ) ≫ star Γ = 𝟙 (ext (unit Γ))

end Metalean.TypeTheory.NaturalModel
