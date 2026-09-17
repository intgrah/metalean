/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Metalean.TypeTheory.NaturalModel.Extension

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C]

class HasUniverse (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] where
  code : ⊤_ (Cᵒᵖ ⥤ Type u) ⟶ Ty
  el : pullback code ℳ.typing ⟶ Ty

class HasHierarchy (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (L : Type*) [Preorder L] [SuccOrder L] where
  level (i : L) : HasUniverse Ty Tm
  smallCode (i : L) : ⊤_ (Cᵒᵖ ⥤ Type u) ⟶ pullback (level (Order.succ i)).code ℳ.typing
  el_smallCode (i : L) :
    smallCode i ≫ (level (Order.succ i)).el = (level i).code

class HasCumulativity (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (L : Type*) [Preorder L] [SuccOrder L]
    [𝒰 : HasHierarchy Ty Tm L] where
  lift {i j : L} (h : i ≤ j) :
    pullback (𝒰.level i).code ℳ.typing ⟶ pullback (𝒰.level j).code ℳ.typing
  lift_refl (i : L) : lift (le_refl i) = 𝟙 _
  lift_trans {i j k : L} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    lift h₁ ≫ lift h₂ = lift (h₁.trans h₂)
  el_lift {i j : L} (h : i ≤ j) : lift h ≫ (𝒰.level j).el = (𝒰.level i).el

end Metalean.TypeTheory.NaturalModel
