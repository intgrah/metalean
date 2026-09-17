/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Inductive
public import Metalean.TypeTheory.NaturalModel.Quotient

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]

class LeanModel (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (ℓ : Nat) extends
    HasSorts Ty Tm ℓ, HasPi Ty Tm, HasQuot Ty Tm ℓ where
  isSort_piCode {Γ : C} (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (v₁ v₂ : Level ℓ) :
    HasSorts.IsSort A v₁ →
    HasSorts.IsSort B v₂ →
    HasSorts.IsSort (piCode A B) (v₁.imax v₂)
  isProp_of_isSort_zero {Γ : C} (A : y Γ ⟶ Ty) :
    HasSorts.IsSort A (Level.zero : Level ℓ) →
    IsProp A
  empty : C
  emptyIsTerminal : IsTerminal empty
  Const : Type u
  constLevels (c : Const) : Nat
  constType (c : Const) (vs : Fin (constLevels c) → Level ℓ) :
    y empty ⟶ Ty
  constTerm (c : Const) (vs : Fin (constLevels c) → Level ℓ) :
    Sect (constType c vs)
  Ind : Type u
  indLevels (i : Ind) : Nat
  indSorts (i : Ind) : Nat
  indParams (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    Tele Ty empty
  indSpec (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    IndSpec Ty (indSorts i) (extTele (indParams i vs))
  indAlgebra (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    Algebra (indSpec i vs)
  indLevel (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    Level ℓ
  isSort_carrier (i : Ind) (vs : Fin (indLevels i) → Level ℓ) (s : Fin (indSorts i)) :
    HasSorts.IsSort ((indAlgebra i vs).carrier s) (indLevel i vs)
  indSmallElim (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    HasSmallElim (indAlgebra i vs)
  indLargeElim (i : Ind) (vs : Fin (indLevels i) → Level ℓ) :
    indLevel i vs ≠ Level.zero ∨ HasSingletonElim (indAlgebra i vs) →
    HasLargeElim (indAlgebra i vs)
  indEta (i : Ind) (vs : Fin (indLevels i) → Level ℓ) {s : Fin (indSorts i)}
    (c : Fin ((indSpec i vs).nctors s)) :
    (indSpec i vs).nctors s = 1 →
    (indSpec i vs).nrec c = 0 →
    (indSpec i vs).index s = .nil →
    HasEta (indAlgebra i vs) c

end Metalean.TypeTheory.NaturalModel
