/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Yoneda

public noncomputable section

namespace Metalean.TypeTheory

open CategoryTheory

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C]

/--
A natural model of type theory is a representable natural transformation
`typing` between presheaves `Tm Ty : Cᵒᵖ ⥤ Type u`, whose component on `Γ : C` is
interpreted to mean the typing of a term.
-/
structure NaturalModel (Ty Tm : Cᵒᵖ ⥤ Type u) where
  typing : Tm ⟶ Ty
  ext {Γ : C} (A : y Γ ⟶ Ty) : C
  disp {Γ : C} (A : y Γ ⟶ Ty) : ext A ⟶ Γ
  var {Γ : C} (A : y Γ ⟶ Ty) : y (ext A) ⟶ Tm
  isPullback {Γ : C} (A : y Γ ⟶ Ty) :
    IsPullback (var A) (y (disp A)) typing A

class HasEmptyCtx (C : Type u) [SmallCategory C] where
  empty : C
  isTerminal : Limits.IsTerminal empty

end Metalean.TypeTheory
