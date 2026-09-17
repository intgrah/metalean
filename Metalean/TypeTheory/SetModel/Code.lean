/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Prop
public import Metalean.TypeTheory.SetModel.Pi
public import Metalean.TypeTheory.SetModel.Sort

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite Limits ZFSet NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {ℓ : Nat} {Γ Δ : ZFSet.{u}}

theorem ofFam_injective {A₁ A₂ : Fam Γ} (h : ofFam A₁ = ofFam A₂) : A₁ = A₂ :=
  (yonedaEquiv_ofFam A₁).symm.trans ((congrArg yonedaEquiv h).trans (yonedaEquiv_ofFam A₂))

theorem isSort_ofFam_iff {A : Fam Γ} {v : Level ℓ} :
    HasSorts.IsSort (Ty := Ty.{u}) (ofFam A) v ↔ ∀ γ : Γ, A.obj γ ∈ S_ (value v) := by
  constructor
  · intro ⟨t, ht, he⟩ γ
    have hA : elFam v t (type_of_sort ht) = A := ofFam_injective he
    have hmem := t.obj_mem γ
    rw [type_of_sort ht] at hmem
    exact (congrArg (fun A : Fam Γ => A.obj γ) hA) ▸ hmem
  · exact fun h => ⟨code A v h, rfl, rfl⟩

theorem isProp_ofFam {A : Fam Γ} (h : ∀ γ : Γ, A.obj γ ∈ truth) : IsProp (ofFam A) := by
  refine isProp_of_subsingleton fun {Δ} σ t₁ ht₁ t₂ ht₂ => ?_
  have hA : ∀ t : Elt Δ, typing.app (op Δ) t = yonedaEquiv (y σ ≫ ofFam A) →
      t.type = A.subst σ := fun _ ht =>
    ht.trans ((congrArg yonedaEquiv (map_ofFam σ A)).trans (yonedaEquiv_ofFam (A.subst σ)))
  refine Elt.ext ((hA t₁ ht₁).trans (hA t₂ ht₂).symm) fun δ => ?_
  refine eq_of_mem_truth (h (σ δ)) ?_ ?_
  · exact (congrArg (fun B : Fam Δ => B.obj δ) (hA t₁ ht₁)) ▸ t₁.obj_mem δ
  · exact (congrArg (fun B : Fam Δ => B.obj δ) (hA t₂ ht₂)) ▸ t₂.obj_mem δ

theorem isProp_of_isSort_zero {A : y Γ ⟶ Ty.{u}}
    (h : HasSorts.IsSort A (Level.zero : Level ℓ)) : IsProp A := by
  rw [← ofFam_yonedaEquiv A] at h ⊢
  exact isProp_ofFam (isSort_ofFam_iff.mp h)

theorem var_typing (A : y Γ ⟶ Ty.{u}) :
    typing.app (op (ext (yonedaEquiv A))) (var (yonedaEquiv A)) =
      yonedaEquiv (y (disp (yonedaEquiv A)) ≫ A) :=
  (yonedaEquiv_comp (disp (yonedaEquiv A)) A).symm

def toExt (A : y Γ ⟶ Ty.{u}) : ext (yonedaEquiv A) ⟶ NaturalModel.ext A :=
  substTerm A (disp (yonedaEquiv A)) (var (yonedaEquiv A)) (var_typing A)

theorem toExt_disp (A : y Γ ⟶ Ty.{u}) :
    toExt A ≫ NaturalModel.disp A = disp (yonedaEquiv A) :=
  substTerm_disp A _ _ (var_typing A)

theorem toExt_generic (A : y Γ ⟶ Ty.{u}) :
    Tm.map (toExt A).op (genericTerm A) = var (yonedaEquiv A) :=
  map_substTerm_genericTerm A _ _ (var_typing A)

theorem evalPoly_family {X : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1)} (A : y Γ ⟶ Ty.{u})
    (b : X.obj (op (NaturalModel.ext A))) :
    evalPoly A ((comprehension A).family b) = X.map (toExt A).op b :=
  ((comprehension A).eval_eq (comp (yonedaEquiv A)) (toExt A) (toExt_disp A) (toExt_generic A)
      A ((comprehension A).family b) rfl (ofFam_yonedaEquiv A).symm).trans
    (congrArg (X.map (toExt A).op) ((comprehension A).eval_family b))

theorem piCode_eq (A : y Γ ⟶ Ty.{u}) (B : y (NaturalModel.ext A) ⟶ Ty.{u}) :
    piCode A B = ofFam (piFam (yonedaEquiv A) ((yonedaEquiv B).subst (toExt A))) :=
  congrArg (fun C : Fam (ext (yonedaEquiv A)) => ofFam (piFam (yonedaEquiv A) C))
    (evalPoly_family A (yonedaEquiv B))

theorem isSort_piCode {A : y Γ ⟶ Ty.{u}} {B : y (NaturalModel.ext A) ⟶ Ty.{u}} {v₁ v₂ : Level ℓ}
    (h₁ : HasSorts.IsSort A v₁) (h₂ : HasSorts.IsSort B v₂) :
    HasSorts.IsSort (piCode A B) (v₁.imax v₂) := by
  rw [← ofFam_yonedaEquiv A] at h₁
  rw [← ofFam_yonedaEquiv B] at h₂
  rw [piCode_eq]
  refine isSort_ofFam_iff.mpr fun γ => ?_
  have hv : value (v₁.imax v₂) = Nat.imax (value v₁) (value v₂) := by simp [value]
  rw [hv]
  refine pi_mem_sort_imax (isSort_ofFam_iff.mp h₁ γ) fun a ha => ?_
  rw [app_fibre _ _ γ ha]
  exact isSort_ofFam_iff.mp h₂ _

@[simp] theorem disp_pairing (A : Fam Γ) (σ : Δ ⟶ Γ) (f : Δ → ZFSet.{u})
    (hf : ∀ δ, f δ ∈ A.obj (σ δ)) (δ : Δ) : disp A (pairing A σ f hf δ) = σ δ :=
  Subtype.ext (fst_pair _ _)

@[simp] theorem snd_pairing (A : Fam Γ) (σ : Δ ⟶ Γ) (f : Δ → ZFSet.{u})
    (hf : ∀ δ, f δ ∈ A.obj (σ δ)) (δ : Δ) :
    ZFSet.snd (pairing A σ f hf δ) = f δ :=
  snd_pair _ _

theorem type_genericTerm (A : y Γ ⟶ Ty.{u}) :
    Elt.type (genericTerm A) = (yonedaEquiv A).subst (NaturalModel.disp A) :=
  (genericTerm_typing A).trans (yonedaEquiv_comp (NaturalModel.disp A) A)

theorem obj_genericTerm_mem (A : y Γ ⟶ Ty.{u}) (z : NaturalModel.ext (C := ZFSet.{u}) (Ty := Ty.{u}) A) :
    Elt.obj (genericTerm A) z ∈ (yonedaEquiv A).obj (NaturalModel.disp A z) :=
  (congrArg (fun B : Fam (NaturalModel.ext A) => B.obj z) (type_genericTerm A)) ▸
    Elt.obj_mem (genericTerm A) z

def fromExt (A : y Γ ⟶ Ty.{u}) : NaturalModel.ext A ⟶ ext (yonedaEquiv A) :=
  pairing (yonedaEquiv A) (NaturalModel.disp A) (Elt.obj (genericTerm A))
    (obj_genericTerm_mem A)

@[simp] theorem toExt_fromExt (A : y Γ ⟶ Ty.{u}) :
    toExt A ≫ fromExt A = 𝟙 (ext (yonedaEquiv A)) := by
  funext z
  refine Subtype.ext ?_
  change ZFSet.pair (NaturalModel.disp A (toExt A z)) (Elt.obj (genericTerm A) (toExt A z)) = z
  rw [show NaturalModel.disp A (toExt A z) = disp (yonedaEquiv A) z from
      congrFun (toExt_disp A) z,
    show Elt.obj (genericTerm A) (toExt A z) = ZFSet.snd z from
      congrArg (fun t : Elt (ext (yonedaEquiv A)) => t.obj z) (toExt_generic A)]
  exact pair_fst_snd_of_mem_ext z.2

theorem disp_toExt_fromExt (A : y Γ ⟶ Ty.{u})
    (z : NaturalModel.ext (C := ZFSet.{u}) (Ty := Ty.{u}) A) :
    NaturalModel.disp A (toExt A (fromExt A z)) = NaturalModel.disp A z :=
  (congrFun (toExt_disp A) (fromExt A z)).trans (disp_pairing _ _ _ _ z)

theorem obj_toExt_fromExt (A : y Γ ⟶ Ty.{u})
    (z : NaturalModel.ext (C := ZFSet.{u}) (Ty := Ty.{u}) A) :
    Elt.obj (genericTerm A) (toExt A (fromExt A z)) = Elt.obj (genericTerm A) z :=
  (congrArg (fun t : Elt (ext (yonedaEquiv A)) => t.obj (fromExt A z)) (toExt_generic A)).trans
    (snd_pairing _ _ _ _ z)

theorem fromExt_toExt (A : y Γ ⟶ Ty.{u}) :
    fromExt A ≫ toExt A = 𝟙 (NaturalModel.ext A) :=
  have htype : Elt.type (Elt.subst (fromExt A ≫ toExt A) (genericTerm A)) =
      Elt.type (genericTerm A) := by
    change (Elt.type (genericTerm A)).subst (fromExt A ≫ toExt A) = Elt.type (genericTerm A)
    rw [type_genericTerm]
    exact Fam.ext fun z => congrArg (yonedaEquiv A).obj (disp_toExt_fromExt A z)
  Section.hom_eq (h := (comprehension A).isPullback)
    (a := genericTerm A)
    ⟨fromExt A ≫ toExt A, funext (disp_toExt_fromExt A),
      Elt.ext htype (obj_toExt_fromExt A)⟩
    ⟨𝟙 _, Category.id_comp _, Elt.ext rfl fun _ => rfl⟩

instance isIso_toExt (A : y Γ ⟶ Ty.{u}) : IsIso (toExt A) :=
  ⟨fromExt A, toExt_fromExt A, fromExt_toExt A⟩

def emptyCtx : ZFSet.{u} := {∅}

def emptyCtx_isTerminal : IsTerminal emptyCtx.{u} :=
  IsTerminal.ofUniqueHom (fun _ _ => ⟨∅, by simp [emptyCtx]⟩)
    fun _ σ => funext fun γ => Subtype.ext (by simpa [emptyCtx] using (σ γ).2)

end Metalean.TypeTheory.SetModel
