/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Sort
public import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Strong

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Opposite TypeTheory TypeTheory.NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ} {v : Level ℓ}

namespace Ty

def sortRepr (Γ : CtxCat E ℓ) (v : Level ℓ) : Repr Γ :=
  ⟨.sort v, v.succ, .sortDF⟩

def sort (v : Level ℓ) (Γ : CtxCat E ℓ) : y Γ ⟶ Ty E ℓ :=
  yonedaEquiv.symm (ofRepr (sortRepr Γ v))

@[simp] theorem yonedaEquiv_sort (v : Level ℓ) (Γ : CtxCat E ℓ) :
    yonedaEquiv (sort v Γ) = ofRepr (sortRepr Γ v) :=
  Equiv.apply_symm_apply _ _

theorem subst_sort (σ : Γ₂ ⟶ Γ₁) (v : Level ℓ) : y σ ≫ sort v Γ₁ = sort v Γ₂ := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  rw [sort, yonedaEquiv_symm_naturality_left]
  exact congrArg yonedaEquiv.symm (congrArg ofRepr (Repr.ext rfl))

def el (v : Level ℓ) (t : Tm_ Γ) (ht : Tm.type t = yonedaEquiv (sort v Γ)) : Ty_ Γ :=
  Tm.elim t (sortRepr Γ v) (by rw [ht, yonedaEquiv_sort])
    (fun _ he => ofTyping Γ.as he)
    fun _ _ h₁ h₂ heq => (ofTyping_eq_iff Γ.as h₁ h₂).mpr (.ofDefEq heq)

theorem el_label (v : Level ℓ) {e : Expr ζ ℓ Γ.as.len} (he : E[Γ.as.ctx] ⊢ₛ e : .sort v)
    (ht : Tm.type (Tm.label Γ.as he) = yonedaEquiv (sort v Γ)) :
    el v (Tm.label Γ.as he) ht = ofTyping Γ.as he :=
  Tm.elim_eq _ _ _ _ _ he rfl

theorem type_label_sort {e : Expr ζ ℓ Γ.as.len} (he : E[Γ.as.ctx] ⊢ₛ e : .sort v) :
    Tm.type (Tm.label Γ.as he) = yonedaEquiv (sort v Γ) :=
  congrArg ofRepr (Repr.ext rfl)

theorem exists_el (A : Ty_ Γ) :
    ∃ (v : Level ℓ) (t : Tm_ Γ) (ht : Tm.type t = yonedaEquiv (sort v Γ)), el v t ht = A := by
  obtain ⟨T, rfl⟩ := exists_ofRepr A
  obtain ⟨v, hv⟩ := T.wf
  exact ⟨v, Tm.label Γ.as hv, type_label_sort hv, congrArg ofRepr (Repr.ext rfl)⟩

theorem exists_el_sort (v : Level ℓ) (Γ : CtxCat E ℓ) :
    ∃ (t : Tm_ Γ) (ht : Tm.type t = yonedaEquiv (sort v.succ Γ)),
      el v.succ t ht = yonedaEquiv (sort v Γ) :=
  ⟨Tm.label Γ.as (.sortDF (l := v)), type_label_sort .sortDF, congrArg ofRepr (Repr.ext rfl)⟩

theorem subst_el (σ : Γ₂ ⟶ Γ₁) (v : Level ℓ) (t : Tm_ Γ₁)
    (ht : Tm.type t = yonedaEquiv (sort v Γ₁))
    (ht' : Tm.type ((Tm E ℓ).map σ.op t) = yonedaEquiv (sort v Γ₂)) :
    (Ty E ℓ).map σ.op (el v t ht) = el v ((Tm E ℓ).map σ.op t) ht' := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  obtain ⟨_, _, rfl⟩ := Tm.exists_label t (sortRepr Γ₁ v) (by rw [ht, yonedaEquiv_sort])
  rfl

end Ty

instance : HasSorts (Ty E ℓ) (Tm E ℓ) ℓ where
  sort := Ty.sort
  subst_sort := Ty.subst_sort
  el v t ht := yonedaEquiv.symm (Ty.el v t ht)
  subst_el σ v t ht := by
    rw [yonedaEquiv_symm_naturality_left]
    exact congrArg yonedaEquiv.symm (Ty.subst_el σ v t ht _)
  exists_el A := by
    have ⟨v, t, ht, h⟩ := Ty.exists_el (yonedaEquiv A)
    exact ⟨v, t, ht, by rw [show Ty.el v t ht = yonedaEquiv A from h, Equiv.symm_apply_apply]⟩
  exists_el_sort v Γ := by
    have ⟨t, ht, h⟩ := Ty.exists_el_sort v Γ
    exact ⟨t, ht, by rw [show Ty.el v.succ t ht = yonedaEquiv (Ty.sort v Γ) from h,
      Equiv.symm_apply_apply]⟩

theorem Ty.isProp_of_isSort_zero (A : y Γ ⟶ Ty E ℓ)
    (h : HasSorts.IsSort A (Level.zero : Level ℓ)) : IsProp A := by
    obtain ⟨t, ht, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ :=
      Tm.exists_label t (Ty.sortRepr _ .zero) (ht.trans (Ty.yonedaEquiv_sort .zero _))
    have hel : Ty.el .zero (Tm.label _ he) ht = Ty.ofTyping _ he := Ty.el_label .zero he ht
    apply isProp_of_subsingleton
    intro Δ σ
    have hsub := Tm.subsingleton_of_prop he rfl σ
    have hA : yonedaEquiv (y σ ≫ HasSorts.el Level.zero (Tm.label _ he) ht) =
        (Ty E ℓ).map σ.op (Ty.el .zero (Tm.label _ he) ht) :=
      (yonedaEquiv_naturality _ σ).symm.trans
        (congrArg ((Ty E ℓ).map σ.op) (Equiv.apply_symm_apply yonedaEquiv _))
    exact fun n₁ h₁ n₂ h₂ => hsub (h₁.trans hA) (h₂.trans hA)

end Metalean
