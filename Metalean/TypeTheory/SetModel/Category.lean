/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Universe.Sort
public import Metalean.TypeTheory.NaturalModel.Defs
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite Limits ZFSet

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

instance : SmallCategory ZFSet.{u} where
  Hom Γ Δ := Γ → Δ
  id _ := _root_.id
  comp σ τ := τ ∘ σ

variable {Γ Δ : ZFSet.{u}}

structure Fam (Γ : ZFSet.{u}) : Type (u + 1) where
  obj (γ : Γ) : ZFSet.{u}
  bound : ∃ n : Nat, ∀ γ : Γ, obj γ ∈ S_ n

@[ext] theorem Fam.ext {A₁ A₂ : Fam Γ} (h : ∀ γ, A₁.obj γ = A₂.obj γ) : A₁ = A₂ := by
  cases A₁
  cases A₂
  congr 1
  exact funext h

structure Elt (Γ : ZFSet.{u}) : Type (u + 1) where
  type : Fam Γ
  obj (γ : Γ) : ZFSet.{u}
  obj_mem (γ : Γ) : obj γ ∈ type.obj γ

@[ext] theorem Elt.ext {t₁ t₂ : Elt Γ} (htype : t₁.type = t₂.type)
    (h : ∀ γ, t₁.obj γ = t₂.obj γ) : t₁ = t₂ := by
  cases t₁
  cases t₂
  cases htype
  congr 1
  exact funext h

def Fam.subst (σ : Δ ⟶ Γ) (A : Fam Γ) : Fam Δ where
  obj δ := A.obj (σ δ)
  bound := A.bound.imp fun _ h δ => h (σ δ)

def Elt.subst (σ : Δ ⟶ Γ) (t : Elt Γ) : Elt Δ where
  type := t.type.subst σ
  obj δ := t.obj (σ δ)
  obj_mem δ := t.obj_mem (σ δ)

def Ty : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj := fun ⟨Γ⟩ => Fam Γ
  map := fun ⟨σ⟩ => ↾Fam.subst σ

def Tm : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj := fun ⟨Γ⟩ => Elt Γ
  map := fun ⟨σ⟩ => ↾Elt.subst σ

def typing : Tm.{u} ⟶ Ty.{u} where
  app _ := ↾Elt.type

def ext (A : Fam Γ) : ZFSet.{u} :=
  range (α := (γ : Γ) × A.obj γ) fun ⟨γ, a⟩ => pair γ a

theorem pair_mem_ext {A : Fam Γ} (γ : Γ) (a : A.obj γ) : pair γ a ∈ ext A :=
  mem_range_self (f := fun p : (γ : Γ) × A.obj γ => pair p.1 p.2) ⟨γ, a⟩

theorem exists_pair_of_mem_ext {A : Fam Γ} {z : ZFSet.{u}} (hz : z ∈ ext A) :
    ∃ (γ : Γ) (a : A.obj γ), pair γ a = z := by
  have ⟨⟨γ, a⟩, hp⟩ := mem_range.mp hz
  exact ⟨γ, a, hp⟩

theorem fst_mem_of_mem_ext {A : Fam Γ} {z : ZFSet.{u}} (hz : z ∈ ext A) : fst z ∈ Γ := by
  obtain ⟨γ, a, rfl⟩ := exists_pair_of_mem_ext hz
  simp

theorem snd_mem_of_mem_ext {A : Fam Γ} {z : ZFSet.{u}} (hz : z ∈ ext A) :
    snd z ∈ A.obj ⟨fst z, fst_mem_of_mem_ext hz⟩ := by
  obtain ⟨γ, a, rfl⟩ := exists_pair_of_mem_ext hz
  simp

def disp (A : Fam Γ) : ext A ⟶ Γ :=
  fun z => ⟨fst z, fst_mem_of_mem_ext z.2⟩

def var (A : Fam Γ) : Elt (ext A) where
  type := A.subst (disp A)
  obj z := snd z
  obj_mem z := snd_mem_of_mem_ext z.2

theorem pair_fst_snd_of_mem_ext {A : Fam Γ} {z : ZFSet.{u}} (hz : z ∈ ext A) :
    ZFSet.pair (ZFSet.fst z) (ZFSet.snd z) = z := by
  obtain ⟨γ, a, rfl⟩ := exists_pair_of_mem_ext hz
  simp

def pairing (A : Fam Γ) (σ : Δ ⟶ Γ) (f : Δ → ZFSet.{u}) (hf : ∀ δ, f δ ∈ A.obj (σ δ)) :
    Δ ⟶ ext A :=
  fun δ => ⟨pair (σ δ) (f δ), pair_mem_ext (σ δ) ⟨f δ, hf δ⟩⟩

theorem isPullback_ext (A : Fam Γ) :
    IsPullback (yonedaEquiv.symm (var A)) (y (disp A)) typing (yonedaEquiv.symm A) := by
  apply IsPullback.of_forall_isPullback_app
  intro ⟨Δ⟩
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro h₁ h₂ ⟨hvar, hdisp⟩
    have hv : (var A).subst h₁ = (var A).subst h₂ := hvar
    have hd : ∀ δ : Δ, disp A (h₁ δ) = disp A (h₂ δ) := congrFun hdisp
    funext δ
    refine Subtype.ext ?_
    rw [← pair_fst_snd_of_mem_ext (h₁ δ).2, ← pair_fst_snd_of_mem_ext (h₂ δ).2,
      show ZFSet.fst (h₁ δ) = ZFSet.fst (h₂ δ) from congrArg Subtype.val (hd δ),
      show ZFSet.snd (h₁ δ) = ZFSet.snd (h₂ δ) from congrArg (fun t : Elt Δ => t.obj δ) hv]
  · intro t σ ht
    have ht' : t.type = A.subst σ := ht
    have hmem (δ : Δ) : t.obj δ ∈ A.obj (σ δ) := by
      have h := t.obj_mem δ
      rw [ht'] at h
      exact h
    have hdisp : pairing A σ t.obj hmem ≫ disp A = σ := by
      funext δ
      apply Subtype.ext
      change ZFSet.fst (ZFSet.pair (σ δ) (t.obj δ)) = σ δ
      simp
    refine ⟨pairing A σ t.obj hmem, Elt.ext ?_ fun δ => ?_, hdisp⟩
    · change A.subst (pairing A σ t.obj hmem ≫ disp A) = t.type
      rw [hdisp, ht']
    · change ZFSet.snd (ZFSet.pair (σ δ) (t.obj δ)) = t.obj δ
      simp

theorem typing_relativelyRepresentable :
    yoneda.relativelyRepresentable typing.{u} := by
  intro Γ A
  refine ⟨ext (yonedaEquiv A), disp _, yonedaEquiv.symm (var _), ?_⟩
  simpa using isPullback_ext (yonedaEquiv A)

instance : NaturalModel Ty.{u} Tm.{u} where
  typing := typing
  representable := typing_relativelyRepresentable

def ofFam (A : Fam Γ) : y Γ ⟶ Ty.{u} :=
  yonedaEquiv.symm A

def ofElt (t : Elt Γ) : y Γ ⟶ Tm.{u} :=
  yonedaEquiv.symm t

@[simp] theorem yonedaEquiv_ofFam (A : Fam Γ) : yonedaEquiv (ofFam A) = A :=
  Equiv.apply_symm_apply _ _

@[simp] theorem yonedaEquiv_ofElt (t : Elt Γ) : yonedaEquiv (ofElt t) = t :=
  Equiv.apply_symm_apply _ _

@[simp] theorem ofFam_yonedaEquiv (A : y Γ ⟶ Ty.{u}) : ofFam (yonedaEquiv A) = A :=
  Equiv.symm_apply_apply _ _

@[simp] theorem ofElt_yonedaEquiv (t : y Γ ⟶ Tm.{u}) : ofElt (yonedaEquiv t) = t :=
  Equiv.symm_apply_apply _ _

@[simp] theorem map_ofFam (σ : Δ ⟶ Γ) (A : Fam Γ) :
    y σ ≫ ofFam A = ofFam (A.subst σ) :=
  yonedaEquiv_symm_naturality_left σ Ty A

@[simp] theorem map_ofElt (σ : Δ ⟶ Γ) (t : Elt Γ) :
    y σ ≫ ofElt t = ofElt (t.subst σ) :=
  yonedaEquiv_symm_naturality_left σ Tm t

@[simp] theorem typing_app (t : Elt Γ) : typing.app (op Γ) t = t.type := rfl

@[simp] theorem Ty_map (σ : Δ ⟶ Γ) (A : Fam Γ) : Ty.map σ.op A = A.subst σ := rfl

@[simp] theorem Tm_map (σ : Δ ⟶ Γ) (t : Elt Γ) : Tm.map σ.op t = t.subst σ := rfl

end Metalean.TypeTheory.SetModel
