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
  {ℓ : Nat} [HasSorts Ty Tm ℓ]

theorem genericTerm_sort_typing (v : Level ℓ) (Γ : C) :
    ℳ.typing.app _ (genericTerm (HasSorts.sort (Ty := Ty) v Γ)) =
      yonedaEquiv (HasSorts.sort v (ext (HasSorts.sort v Γ))) := by
  rw [genericTerm_typing, HasSorts.subst_sort]

variable [HasPi Ty Tm] {Γ : C}

variable (Ty ℓ) in
def falseType (Γ : C) : y Γ ⟶ Ty :=
  piCode (HasSorts.sort (Level.zero : Level ℓ) Γ)
    (HasSorts.el Level.zero _ (genericTerm_sort_typing Level.zero Γ))

theorem isEmpty_sect_falseType (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (HasSorts.sort (Level.zero : Level ℓ) Γ))
    (hempty : IsEmpty (Sect (HasSorts.el Level.zero t ht))) :
    IsEmpty (Sect (falseType Ty ℓ Γ)) := by
  refine ⟨fun s => hempty.elim (Sect.convert ?_ (Sect.pullbackAlong (Sect.ofTerm _ t ht).hom
    (Sect.ofTerm _ (appTerm _ _ s.term s.term_typing)
      (appTerm_typing _ _ s.term s.term_typing))))⟩
  rw [HasSorts.subst_el]
  exact HasSorts.el_congr (Sect.term_ofTerm _ t ht) _ _

end Metalean.TypeTheory.NaturalModel
