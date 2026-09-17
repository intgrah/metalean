/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Extension
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C]

class HasPi (Ty : Cᵒᵖ ⥤ Type u) (Tm : outParam (Cᵒᵖ ⥤ Type u))
    [ℳ : NaturalModel Ty Tm] where
  pi : (polynomial Ty).obj Ty ⟶ Ty
  lam : (polynomial Ty).obj Tm ⟶ Tm
  isPullback : IsPullback lam ((polynomial Ty).map ℳ.typing) ℳ.typing pi

variable {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm] [HasPi Ty Tm]
  {Γ Δ : C}

def piCode (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) : y Γ ⟶ Ty :=
  yonedaEquiv.symm (HasPi.pi.app (op Γ) ((comprehension A).label (yonedaEquiv B)))

variable (Ty) in
theorem pi_isPullback_app (Γ : C) :
    IsPullback (HasPi.lam.app (op Γ)) (((polynomial Ty).map ℳ.typing).app (op Γ))
      (ℳ.typing.app (op Γ)) (HasPi.pi.app (op Γ)) :=
  HasPi.isPullback.map ((evaluation Cᵒᵖ (Type u)).obj (op Γ))

def lamTerm (A : y Γ ⟶ Ty) (b : Tm.obj (op (ext A))) : Tm.obj (op Γ) :=
  HasPi.lam.app (op Γ) ((comprehension A).label b)

theorem lamTerm_typing (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (b : Tm.obj (op (ext A)))
    (hb : ℳ.typing.app _ b = yonedaEquiv B) :
    ℳ.typing.app (op Γ) (lamTerm A b) = yonedaEquiv (piCode A B) := by
  have hw := ConcreteCategory.congr_hom (NatTrans.congr_app HasPi.isPullback.w (op Γ))
    ((comprehension A).label b)
  simp at hw
  simp [piCode, lamTerm, hw, (comprehension A).map_label ℳ.typing b, hb]

theorem subst_piCode (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) :
    y σ ≫ piCode A B = piCode (y σ ≫ A) (y (extMap σ A) ≫ B) := by
  rw [piCode, piCode, yonedaEquiv_symm_naturality_left]
  refine congrArg yonedaEquiv.symm ?_
  rw [← NatTrans.naturality_apply HasPi.pi σ.op,
    (comprehension A).label_reindex (comprehension (y σ ≫ A)) σ (extMap σ A) (extMap_disp σ A)
      (extMap_genericTerm σ A) rfl (yonedaEquiv B), yonedaEquiv_naturality]

theorem exists_app (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (piCode A B)) :
    ∃ b : Tm.obj (op (ext A)), ℳ.typing.app _ b = yonedaEquiv B ∧ lamTerm A b = t := by
  obtain ⟨L, hlam, htyping⟩ :=
    ((Types.isPullback_iff _ _ _ _).mp (pi_isPullback_app Ty Γ)).2.2 t
      ((comprehension A).label (yonedaEquiv B)) (by simp [ht, piCode])
  obtain ⟨A', B'⟩ := L
  have hA : A' = (comprehension A).type := congrArg Sigma.fst htyping
  refine ⟨(comprehension A).eval A' B' hA, ?_, ?_⟩
  · rw [(comprehension A).map_eval ℳ.typing A' B' hA, (comprehension A).eval_congr htyping hA rfl]
    exact (comprehension A).eval_family (yonedaEquiv B)
  · rw [lamTerm, (comprehension A).label_eval A' B' hA]
    exact hlam

def appTerm (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (piCode A B)) : Tm.obj (op (ext A)) :=
  (exists_app A B t ht).choose

theorem appTerm_typing (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (piCode A B)) :
    ℳ.typing.app _ (appTerm A B t ht) = yonedaEquiv B :=
  (exists_app A B t ht).choose_spec.1

theorem lamTerm_appTerm (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (t : Tm.obj (op Γ))
    (ht : ℳ.typing.app (op Γ) t = yonedaEquiv (piCode A B)) :
    lamTerm A (appTerm A B t ht) = t :=
  (exists_app A B t ht).choose_spec.2

theorem lamTerm_injective (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (b₁ b₂ : Tm.obj (op (ext A)))
    (hb₁ : ℳ.typing.app _ b₁ = yonedaEquiv B) (hb₂ : ℳ.typing.app _ b₂ = yonedaEquiv B)
    (h : lamTerm A b₁ = lamTerm A b₂) : b₁ = b₂ := by
  have hlabel := ((Types.isPullback_iff _ _ _ _).mp (pi_isPullback_app Ty Γ)).2.1
    ((comprehension A).label b₁) ((comprehension A).label b₂)
    ⟨h, by rw [(comprehension A).map_label ℳ.typing b₁, (comprehension A).map_label ℳ.typing b₂, hb₁, hb₂]⟩
  have heval := (comprehension A).eval_congr hlabel rfl rfl
  rwa [(comprehension A).eval_family, (comprehension A).eval_family] at heval

theorem appTerm_lamTerm (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (b : Tm.obj (op (ext A)))
    (hb : ℳ.typing.app _ b = yonedaEquiv B) :
    appTerm A B (lamTerm A b) (lamTerm_typing A B b hb) = b :=
  lamTerm_injective A B _ b (appTerm_typing A B _ _) hb (lamTerm_appTerm A B _ _)

def lamSect (A : y Γ ⟶ Ty) (B : y (ext A) ⟶ Ty) (b : Sect B) : Sect (piCode A B) :=
  Sect.ofTerm _ (lamTerm A b.term) (lamTerm_typing A B b.term b.term_typing)

end Metalean.TypeTheory.NaturalModel
