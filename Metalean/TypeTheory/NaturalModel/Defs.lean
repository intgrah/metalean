/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

public noncomputable section

namespace Metalean.TypeTheory

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C]

/--
A natural model of type theory is a representable natural transformation
`typing` between presheaves `Tm Ty : Cᵒᵖ ⥤ Type u`, whose component on `Γ : C` is
interpreted to mean the typing of a term.
-/
class NaturalModel (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u)) where
  typing : Tm ⟶ Ty
  representable : yoneda.relativelyRepresentable typing

end Metalean.TypeTheory
