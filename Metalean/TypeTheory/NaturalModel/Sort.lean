/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Basic
public import Metalean.TypeTheory.NaturalModel.Pi
public import Metalean.TypeTheory.NaturalModel.Prop

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C]

class HasSorts (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] (ℓ : Nat) where
  sort (v : Level ℓ) (Γ : C) : y Γ ⟶ Ty
  subst_sort {Γ Δ : C} (σ : Δ ⟶ Γ) (v : Level ℓ) :
    y σ ≫ sort v Γ = sort v Δ
  el {Γ : C} (v : Level ℓ) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v Γ)) :
    y Γ ⟶ Ty
  subst_el {Γ Δ : C} (σ : Δ ⟶ Γ) (v : Level ℓ) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v Γ)) :
    y σ ≫ el v t ht =
      el v (Tm.map σ.op t)
        (by simp [ht, yonedaEquiv_naturality, subst_sort])
  exists_el {Γ : C} (A : y Γ ⟶ Ty) :
    ∃ (v : Level ℓ) (t : Tm.obj (op Γ))
      (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v Γ)), el v t ht = A
  exists_el_sort (v : Level ℓ) (Γ : C) :
    ∃ (t : Tm.obj (op Γ))
      (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v.succ Γ)), el v.succ t ht = sort v Γ

namespace HasSorts

variable {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm] {ℓ : Nat} [HasSorts Ty Tm ℓ]
  {Γ Δ : C}

def IsSort (A : y Γ ⟶ Ty) (v : Level ℓ) : Prop :=
  ∃ (t : Tm.obj (op Γ)) (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v Γ)), el v t ht = A

theorem isSort_el (v : Level ℓ) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (sort v Γ)) : IsSort (el v t ht) v :=
  ⟨t, ht, rfl⟩

theorem exists_isSort (A : y Γ ⟶ Ty) : ∃ v : Level ℓ, IsSort A v :=
  have ⟨v, t, ht, h⟩ := exists_el A
  ⟨v, t, ht, h⟩

theorem isSort_sort (v : Level ℓ) (Γ : C) : IsSort (Ty := Ty) (sort v Γ) v.succ :=
  exists_el_sort v Γ

theorem el_congr {v : Level ℓ} {t₁ t₂ : Tm.obj (op Γ)} (h : t₁ = t₂)
    (h₁ : ℳ.typing.app (op Γ) t₁ = yonedaEquiv (sort v Γ))
    (h₂ : ℳ.typing.app (op Γ) t₂ = yonedaEquiv (sort v Γ)) :
    el v t₁ h₁ = el v t₂ h₂ := by
  subst h
  rfl

theorem IsSort.subst (σ : Δ ⟶ Γ) {A : y Γ ⟶ Ty} {v : Level ℓ} (h : IsSort A v) :
    IsSort (y σ ≫ A) v :=
  have ⟨t, ht, he⟩ := h
  ⟨Tm.map σ.op t, _, (subst_el σ v t ht).symm.trans (congrArg (y σ ≫ ·) he)⟩

end HasSorts

end Metalean.TypeTheory.NaturalModel
