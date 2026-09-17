/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.AczelUniverse
public import Metalean.TypeTheory.NaturalModel.Pi
public import Metalean.TypeTheory.SetModel.Category
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite Limits ZFSet NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {Γ Δ : ZFSet.{u}}

def point (A : Fam Γ) (γ : Γ) (a : A.obj γ) : ext A :=
  ⟨pair γ a, pair_mem_ext γ a⟩

@[simp] theorem disp_point (A : Fam Γ) (γ : Γ) (a : A.obj γ) : disp A (point A γ a) = γ :=
  Subtype.ext (fst_pair _ _)

@[simp] theorem snd_point (A : Fam Γ) (γ : Γ) (a : A.obj γ) :
    ZFSet.snd (point A γ a) = a :=
  snd_pair _ _

theorem snd_mem_disp (A : Fam Γ) (z : ext A) : ZFSet.snd z ∈ A.obj (disp A z) :=
  snd_mem_of_mem_ext z.2

theorem point_disp (A : Fam Γ) (z : ext A) :
    point A (disp A z) ⟨ZFSet.snd z, snd_mem_disp A z⟩ = z :=
  Subtype.ext (pair_fst_snd_of_mem_ext z.2)

def comp (A : Fam Γ) : Comprehension Ty.{u} Γ (ext A) where
  type := ofFam A
  disp := disp A
  generic := var A
  isPullback := isPullback_ext A

def fibre (A : Fam Γ) (B : Fam (ext A)) (γ : Γ) : ZFSet.{u} :=
  graph (A.obj γ) fun a => B.obj (point A γ a)

theorem app_fibre (A : Fam Γ) (B : Fam (ext A)) (γ : Γ) {a : ZFSet.{u}} (ha : a ∈ A.obj γ) :
    ZFSet.app (fibre A B γ) a = B.obj (point A γ ⟨a, ha⟩) :=
  app_graph ha

def piFam (A : Fam Γ) (B : Fam (ext A)) : Fam Γ where
  obj γ := Aczel.piMap (A.obj γ) (fibre A B γ)
  bound := by
    have ⟨n₁, h₁⟩ := A.bound
    have ⟨n₂, h₂⟩ := B.bound
    exact ⟨Nat.imax n₁ n₂, fun γ => pi_mem_sort_imax (h₁ γ) fun a ha => by
      rw [app_fibre A B γ ha]
      exact h₂ _⟩

def lamElt (A : Fam Γ) (b : Elt (ext A)) : Elt Γ where
  type := piFam A b.type
  obj γ := Aczel.lam (A.obj γ) (ZFSet.app (graph (A.obj γ) fun a => b.obj (point A γ a)))
  obj_mem γ := Aczel.lam_mem_piMap fun a ha => by
    rw [app_graph ha, app_fibre A b.type γ ha]
    exact b.obj_mem _

def appElt (A : Fam Γ) (B : Fam (ext A)) (t : Elt Γ) (ht : t.type = piFam A B) : Elt (ext A) where
  type := B
  obj z := Aczel.app (t.obj (disp A z)) (ZFSet.snd z)
  obj_mem z := by
    have hmem := t.obj_mem (disp A z)
    rw [ht] at hmem
    have h := Aczel.app_mem hmem (snd_mem_disp A z)
    rw [app_fibre A B (disp A z) (snd_mem_disp A z), point_disp] at h
    exact h

theorem app_lamElt (A : Fam Γ) (b : Elt (ext A)) (z : ext A) :
    Aczel.app ((lamElt A b).obj (disp A z)) (ZFSet.snd z) = b.obj z := by
  change Aczel.app (Aczel.lam (A.obj (disp A z))
      (ZFSet.app (graph (A.obj (disp A z)) fun a => b.obj (point A (disp A z) a))))
      (ZFSet.snd z) = b.obj z
  simp [Aczel.app_lam (snd_mem_disp A z), app_graph (snd_mem_disp A z), point_disp]

theorem appElt_lamElt (A : Fam Γ) (b : Elt (ext A)) :
    appElt A b.type (lamElt A b) rfl = b :=
  Elt.ext rfl (app_lamElt A b)

theorem lamElt_appElt (A : Fam Γ) (B : Fam (ext A)) (t : Elt Γ) (ht : t.type = piFam A B) :
    lamElt A (appElt A B t ht) = t := by
  refine Elt.ext ht.symm fun γ => ?_
  have hmem := t.obj_mem γ
  rw [ht] at hmem
  change Aczel.lam (A.obj γ) (ZFSet.app (graph (A.obj γ) fun a =>
      Aczel.app (t.obj (disp A (point A γ a))) (ZFSet.snd (point A γ a)))) = t.obj γ
  exact Eq.trans (Aczel.lam_congr fun a ha => by simp [app_graph ha]) (Aczel.lam_app hmem)

theorem subst_obj {A₁ : Fam Γ} {A₂ : Fam Δ} {σ : Δ ⟶ Γ} (h : A₂ = A₁.subst σ) (δ : Δ) :
    A₂.obj δ = A₁.obj (σ δ) :=
  congrArg (fun A : Fam Δ => A.obj δ) h

def extCongr {A₁ : Fam Γ} {A₂ : Fam Δ} (σ : Δ ⟶ Γ) (h : A₂ = A₁.subst σ) :
    ext A₂ ⟶ ext A₁ :=
  fun z => point A₁ (σ (disp A₂ z)) ⟨ZFSet.snd z, subst_obj h (disp A₂ z) ▸ snd_mem_disp A₂ z⟩

@[simp] theorem extCongr_point {A : Fam Γ} (σ : Δ ⟶ Γ) (δ : Δ) (a : (A.subst σ).obj δ) :
    extCongr σ rfl (point (A.subst σ) δ a) = point A (σ δ) a := by
  ext : 1
  change ZFSet.pair (σ (disp (A.subst σ) (point (A.subst σ) δ a)))
      (ZFSet.snd (point (A.subst σ) δ a)) = ZFSet.pair (σ δ) a
  simp

theorem subst_piFam {A₁ : Fam Γ} {A₂ : Fam Δ} (σ : Δ ⟶ Γ) (h : A₂ = A₁.subst σ)
    (B : Fam (ext A₁)) :
    (piFam A₁ B).subst σ = piFam A₂ (B.subst (extCongr σ h)) := by
  subst h
  refine Fam.ext fun δ => ?_
  refine congrArg (Aczel.piMap _) (congrArg (graph _) (funext fun a => ?_))
  exact congrArg B.obj (extCongr_point σ δ a).symm

theorem subst_lamElt {A₁ : Fam Γ} {A₂ : Fam Δ} (σ : Δ ⟶ Γ) (h : A₂ = A₁.subst σ)
    (b : Elt (ext A₁)) :
    (lamElt A₁ b).subst σ = lamElt A₂ (b.subst (extCongr σ h)) := by
  subst h
  refine Elt.ext (subst_piFam σ rfl b.type) fun δ => ?_
  refine congrArg (Aczel.lam _) (congrArg ZFSet.app (congrArg (graph _) (funext fun a => ?_)))
  exact congrArg b.obj (extCongr_point σ δ a).symm

theorem extCongr_disp {A₁ : Fam Γ} {A₂ : Fam Δ} (σ : Δ ⟶ Γ) (h : A₂ = A₁.subst σ) :
    extCongr σ h ≫ disp A₁ = disp A₂ ≫ σ :=
  funext fun z => disp_point A₁ (σ (disp A₂ z)) _

theorem extCongr_var {A₁ : Fam Γ} {A₂ : Fam Δ} (σ : Δ ⟶ Γ) (h : A₂ = A₁.subst σ) :
    (var A₁).subst (extCongr σ h) = var A₂ := by
  refine Elt.ext (Fam.ext fun z => ?_) fun z => ?_
  · change A₁.obj (disp A₁ (extCongr σ h z)) = A₂.obj (disp A₂ z)
    rw [show disp A₁ (extCongr σ h z) = σ (disp A₂ z) from disp_point _ _ _]
    exact (subst_obj h (disp A₂ z)).symm
  · exact snd_point A₁ (σ (disp A₂ z)) _

def evalPoly {Γ : ZFSet.{u}} {X : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1)} (A : y Γ ⟶ Ty.{u})
    (B : pullback A typing ⟶ X) : X.obj (op (ext (yonedaEquiv A))) :=
  (comp (yonedaEquiv A)).eval A B (ofFam_yonedaEquiv A).symm

theorem type_evalPoly {Γ : ZFSet.{u}} (A : y Γ ⟶ Ty.{u}) (b : pullback A typing ⟶ Tm.{u}) :
    (evalPoly A b).type = evalPoly A (b ≫ typing) :=
  (comp (yonedaEquiv A)).map_eval typing A b _

theorem label_evalPoly {Γ : ZFSet.{u}} {X : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1)} (A : y Γ ⟶ Ty.{u})
    (B : pullback A typing ⟶ X) :
    (comp (yonedaEquiv A)).label (evalPoly A B) = ⟨A, B⟩ :=
  (comp (yonedaEquiv A)).label_eval A B _

def piPoly {Γ : ZFSet.{u}} (P : ((polynomial Ty.{u}).obj Ty.{u}).obj (op Γ)) : Fam Γ :=
  piFam (yonedaEquiv P.1) (evalPoly P.1 P.2)

def lamPoly {Γ : ZFSet.{u}} (P : ((polynomial Ty.{u}).obj Tm.{u}).obj (op Γ)) : Elt Γ :=
  lamElt (yonedaEquiv P.1) (evalPoly P.1 P.2)

theorem yonedaEquiv_comp (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty.{u}) :
    yonedaEquiv (y σ ≫ A) = (yonedaEquiv A).subst σ :=
  (yonedaEquiv_naturality A σ).symm

theorem evalPoly_extCongr (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty.{u})
    {X : ZFSet.{u}ᵒᵖ ⥤ Type (u + 1)} (B : pullback A typing ⟶ X) :
    evalPoly (y σ ≫ A) (fibreMap A (y σ) ≫ B) =
      X.map (extCongr σ (yonedaEquiv_comp σ A)).op (evalPoly A B) :=
  (comp (yonedaEquiv A)).eval_reindex (comp (yonedaEquiv (y σ ≫ A))) σ
    (extCongr σ (yonedaEquiv_comp σ A))
    (extCongr_disp σ (yonedaEquiv_comp σ A))
    (extCongr_var σ (yonedaEquiv_comp σ A))
    A B (ofFam_yonedaEquiv A).symm (ofFam_yonedaEquiv _).symm

def piNat : (polynomial Ty.{u}).obj Ty.{u} ⟶ Ty.{u} where
  app := fun ⟨Γ⟩ => ↾fun P => piPoly P
  naturality := by
    intro ⟨Γ⟩ ⟨Δ⟩ ⟨σ⟩
    ext ⟨A, B⟩
    exact (congrArg (piFam _) (evalPoly_extCongr σ A B)).trans
      (subst_piFam σ (yonedaEquiv_comp σ A) _).symm

def lamNat : (polynomial Ty.{u}).obj Tm.{u} ⟶ Tm.{u} where
  app := fun ⟨Γ⟩ => ↾fun P => lamPoly P
  naturality := by
    intro ⟨Γ⟩ ⟨Δ⟩ ⟨σ⟩
    ext ⟨A, b⟩
    exact (congrArg (lamElt _) (evalPoly_extCongr σ A b)).trans
      (subst_lamElt σ (yonedaEquiv_comp σ A) _).symm

theorem lamElt_injective (A : Fam Γ) {b₁ b₂ : Elt (ext A)} (htype : b₁.type = b₂.type)
    (h : lamElt A b₁ = lamElt A b₂) : b₁ = b₂ := by
  refine Elt.ext htype fun z => ?_
  rw [← app_lamElt A b₁ z, ← app_lamElt A b₂ z, h]

instance : HasPi Ty.{u} Tm.{u} where
  pi := piNat
  lam := lamNat
  isPullback := by
    apply IsPullback.of_forall_isPullback_app
    intro ⟨Γ⟩
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro ⟨A₁, b₁⟩ ⟨A₂, b₂⟩ ⟨hlam, htyping⟩
      obtain rfl : A₁ = A₂ := congrArg Sigma.fst htyping
      injection htyping with _ hb
      refine (label_evalPoly A₁ b₁).symm.trans
        ((congrArg _ (lamElt_injective _ ?_ hlam)).trans (label_evalPoly A₁ b₂))
      exact (type_evalPoly A₁ b₁).trans
        ((congrArg (evalPoly A₁) hb).trans (type_evalPoly A₁ b₂).symm)
    · intro t ⟨A, B⟩ ht
      refine ⟨(comp (yonedaEquiv A)).label (appElt (yonedaEquiv A) (evalPoly A B) t ht), ?_, ?_⟩
      · exact (congrArg (lamElt (yonedaEquiv A)) ((comp (yonedaEquiv A)).eval_family _)).trans
          (lamElt_appElt _ _ t ht)
      · exact ((comp (yonedaEquiv A)).map_label typing _).trans (label_evalPoly A B)

end Metalean.TypeTheory.SetModel
