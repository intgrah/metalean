/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Model

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {ℓ : Nat} [𝓛 : LeanModel Ty Tm ℓ] {Γ : C}

variable (Ty ℓ) in
structure IndArgs where
  {arity : Nat}
  {base : C}
  spec : IndSpec Ty arity base
  level : Level ℓ
  bounded : spec.Bounded level
  sort : Fin arity

variable (Ty ℓ) in
inductive Canonical (Γ : C) where
  | sort (v : Level ℓ)
  | pi (P : ((polynomial Ty).obj Ty).obj (op Γ))
  | quot (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ))
  | ind (a : IndArgs Ty ℓ)
    (σ : Γ ⟶ extTele (a.spec.index a.sort))

def Canonical.decode : Canonical Ty ℓ Γ → (y Γ ⟶ Ty)
  | .sort v => HasSorts.sort v Γ
  | .pi P => yonedaEquiv.symm (HasPi.pi.app (op Γ) P)
  | .quot A R hR => HasQuot.quot A R hR
  | .ind a σ => y σ ≫ (LeanModel.algebra a.spec a.level a.bounded).carrier a.sort

class Discriminating (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (ℓ : Nat) [𝓛 : LeanModel Ty Tm ℓ] : Prop where
  decode_injective (Γ : C) :
    Function.Injective (α := Canonical Ty ℓ Γ) Canonical.decode

namespace Discriminating

variable [Discriminating Ty Tm ℓ]

theorem decode_inj (c₁ c₂ : Canonical Ty ℓ Γ) (h : c₁.decode = c₂.decode) : c₁ = c₂ :=
  decode_injective Γ h

theorem sort_injective (v₁ v₂ : Level ℓ)
    (h : (HasSorts.sort v₁ Γ : y Γ ⟶ Ty) = HasSorts.sort v₂ Γ) : v₁ = v₂ :=
  Canonical.sort.inj (decode_inj (.sort v₁) (.sort v₂) h)

theorem piCode_injective {A₁ A₂ : y Γ ⟶ Ty} {B₁ : y (ext A₁) ⟶ Ty} {B₂ : y (ext A₂) ⟶ Ty}
    (h : piCode A₁ B₁ = piCode A₂ B₂) :
    (⟨A₁, B₁⟩ : Σ A : y Γ ⟶ Ty, y (ext A) ⟶ Ty) = ⟨A₂, B₂⟩ := by
  have hlabel := Canonical.pi.inj (decode_inj
    (.pi ((comprehension A₁).label (yonedaEquiv B₁)))
    (.pi ((comprehension A₂).label (yonedaEquiv B₂))) h)
  obtain rfl : A₁ = A₂ := congrArg Sigma.fst hlabel
  refine congrArg (Sigma.mk A₁) (yonedaEquiv.injective ?_)
  have heval := (comprehension A₁).eval_congr hlabel rfl rfl
  rwa [(comprehension A₁).eval_family, (comprehension A₁).eval_family] at heval

theorem quot_injective {A₁ A₂ : y Γ ⟶ Ty} {R₁ : y (ext (y (disp A₁) ≫ A₁)) ⟶ Ty}
    {R₂ : y (ext (y (disp A₂) ≫ A₂)) ⟶ Ty} {hR₁ : HasSorts.IsSort R₁ (Level.zero : Level ℓ)}
    {hR₂ : HasSorts.IsSort R₂ (Level.zero : Level ℓ)}
    (h : HasQuot.quot A₁ R₁ hR₁ = HasQuot.quot A₂ R₂ hR₂) :
    (⟨A₁, R₁⟩ : Σ A : y Γ ⟶ Ty, y (ext (y (disp A) ≫ A)) ⟶ Ty) = ⟨A₂, R₂⟩ := by
  obtain ⟨rfl, h⟩ := Canonical.quot.inj (decode_inj (.quot A₁ R₁ hR₁) (.quot A₂ R₂ hR₂) h)
  exact congrArg (Sigma.mk A₁) (eq_of_heq h)

theorem ind_injective {a₁ a₂ : IndArgs Ty ℓ}
    {σ₁ : Γ ⟶ extTele (a₁.spec.index a₁.sort)}
    {σ₂ : Γ ⟶ extTele (a₂.spec.index a₂.sort)}
    (h : y σ₁ ≫ (LeanModel.algebra a₁.spec a₁.level a₁.bounded).carrier a₁.sort =
      y σ₂ ≫ (LeanModel.algebra a₂.spec a₂.level a₂.bounded).carrier a₂.sort) :
    a₁ = a₂ ∧ σ₁ ≍ σ₂ :=
  Canonical.ind.inj (decode_inj (.ind a₁ σ₁) (.ind a₂ σ₂) h)

theorem sort_ne_piCode (v : Level ℓ) (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    (HasSorts.sort v Γ : y Γ ⟶ Ty) ≠ piCode A B := fun h => by
  cases decode_inj (.sort v) (.pi ((comprehension A).label (yonedaEquiv B))) h

theorem sort_ne_quot (v : Level ℓ) (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    (HasSorts.sort v Γ : y Γ ⟶ Ty) ≠ HasQuot.quot A R hR := fun h => by
  cases decode_inj (.sort v) (.quot A R hR) h

theorem sort_ne_ind (v : Level ℓ) (a : IndArgs Ty ℓ)
    (σ : Γ ⟶ extTele (a.spec.index a.sort)) :
    (HasSorts.sort v Γ : y Γ ⟶ Ty) ≠
      y σ ≫ (LeanModel.algebra a.spec a.level a.bounded).carrier a.sort := fun h => by
  cases decode_inj (.sort v) (.ind a σ) h

theorem piCode_ne_quot (A₁ : y Γ ⟶ Ty) (B : y (ext A₁) ⟶ Ty) (A₂ : y Γ ⟶ Ty)
    (R : y (ext (y (disp A₂) ≫ A₂)) ⟶ Ty) (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) :
    piCode A₁ B ≠ HasQuot.quot A₂ R hR := fun h => by
  cases decode_inj (.pi ((comprehension A₁).label (yonedaEquiv B))) (.quot A₂ R hR) h

theorem piCode_ne_ind (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (a : IndArgs Ty ℓ)
    (σ : Γ ⟶ extTele (a.spec.index a.sort)) :
    piCode A B ≠ y σ ≫ (LeanModel.algebra a.spec a.level a.bounded).carrier a.sort := fun h => by
  cases decode_inj (.pi ((comprehension A).label (yonedaEquiv B))) (.ind a σ) h

theorem quot_ne_ind (A : y Γ ⟶ Ty) (R : y (ext (y (disp A) ≫ A)) ⟶ Ty)
    (hR : HasSorts.IsSort R (Level.zero : Level ℓ)) (a : IndArgs Ty ℓ)
    (σ : Γ ⟶ extTele (a.spec.index a.sort)) :
    HasQuot.quot A R hR ≠ y σ ≫ (LeanModel.algebra a.spec a.level a.bounded).carrier a.sort :=
    fun h => by
  cases decode_inj (.quot A R hR) (.ind a σ) h

end Discriminating

end Metalean.TypeTheory.NaturalModel
