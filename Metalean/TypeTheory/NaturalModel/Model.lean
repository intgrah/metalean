/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Order
public import Metalean.TypeTheory.NaturalModel.Inductive
public import Metalean.TypeTheory.NaturalModel.Quotient

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]

inductive Tele.Bounded {ℓ : Nat} [HasSorts Ty Tm ℓ] (v : Level ℓ) :
    {Γ : C} → Tele Ty Γ → Prop where
  | nil {Γ : C} :
    Bounded v (.nil : Tele Ty Γ)
  | cons {Γ : C} {A : y Γ ⟶ Ty} {Θ : Tele Ty (ext A)} (u : Level ℓ)
    (hA : HasSorts.IsSort A u) (hu : Level.imax u v ≤ v) :
    Bounded v Θ →
    Bounded v (.cons A Θ)

structure IndSpec.Bounded {ℓ : Nat} [HasSorts Ty Tm ℓ] [HasPi Ty Tm] {n : Nat} {Γ : C}
    (I : IndSpec Ty n Γ) (v : Level ℓ) : Prop where
  fields {s : Fin n} (c : Fin (I.nctors s)) :
    Tele.Bounded v (I.field c)
  arities {s : Fin n} (c : Fin (I.nctors s)) (k : Fin (I.nrec c)) :
    Tele.Bounded v (I.arity c k)

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
  algebra {n : Nat} {Γ : C} (I : IndSpec Ty n Γ) (v : Level ℓ) (hI : I.Bounded v) :
    Algebra I
  isSort_carrier {n : Nat} {Γ : C} (I : IndSpec Ty n Γ) (v : Level ℓ) (hI : I.Bounded v)
    (s : Fin n) :
    HasSorts.IsSort ((algebra I v hI).carrier s) v
  smallElim {n : Nat} {Γ : C} (I : IndSpec Ty n Γ) (v : Level ℓ) (hI : I.Bounded v) :
    HasSmallElim (algebra I v hI)
  largeElim {n : Nat} {Γ : C} (I : IndSpec Ty n Γ) (v : Level ℓ) (hI : I.Bounded v) :
    v ≠ Level.zero ∨ HasSingletonElim (algebra I v hI) →
    HasLargeElim (algebra I v hI)
  eta {n : Nat} {Γ : C} (I : IndSpec Ty n Γ) (v : Level ℓ) (hI : I.Bounded v) {s : Fin n}
    (c : Fin (I.nctors s)) :
    I.nctors s = 1 →
    I.nrec c = 0 →
    I.index s = .nil →
    HasEta (algebra I v hI) c

end Metalean.TypeTheory.NaturalModel
