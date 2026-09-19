/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Polynomial

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm X Y : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {Γ Γ' ΓA ΓA' Δ Δ' ΔA : C} {A : y Γ ⟶ Ty} {π : ΓA ⟶ Γ} {q : Tm.obj (op ΓA)}

structure Section (h : IsPullback (yonedaEquiv.symm q) (y π) ℳ.typing A) (σ : Δ ⟶ Γ)
    (a : Tm.obj (op Δ)) where
  hom : Δ ⟶ ΓA
  over : hom ≫ π = σ
  generic : Tm.map hom.op q = a

namespace Section

variable {h : IsPullback (yonedaEquiv.symm q) (y π) ℳ.typing A} {σ : Δ ⟶ Γ}
  {a : Tm.obj (op Δ)}

@[ext] theorem ext {s t : Section h σ a} (heq : s.hom = t.hom) : s = t := by
  cases s; cases t; cases heq; rfl

theorem hom_eq (s t : Section h σ a) : s.hom = t.hom :=
  yoneda.map_injective <| h.hom_ext
    (by simp [yonedaEquiv_symm_naturality_left, generic])
    (by simpa using congrArg yoneda.map (s.over.trans t.over.symm))

instance : Subsingleton (Section h σ a) := ⟨fun s t => ext (hom_eq s t)⟩

def pullback (s : Section h σ a) (σ' : Δ' ⟶ Δ) : Section h (σ' ≫ σ) (Tm.map σ'.op a) where
  hom := σ' ≫ s.hom
  over := by simp [over]
  generic := by simp [generic]

def pullbackId {a : Tm.obj (op Γ)} (s : Section h (𝟙 Γ) a) (σ : Δ ⟶ Γ) :
    Section h σ (Tm.map σ.op a) where
  hom := σ ≫ s.hom
  over := by simp [over]
  generic := by simp [generic]

def ofTerm (h : IsPullback (yonedaEquiv.symm q) (y π) ℳ.typing A) (σ : Δ ⟶ Γ)
    (a : Tm.obj (op Δ)) (ha : yonedaEquiv.symm a ≫ ℳ.typing = y σ ≫ A) : Section h σ a where
  hom := yoneda.preimage (h.lift (yonedaEquiv.symm a) (y σ) ha)
  over := yoneda.map_injective (by simp)
  generic := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality_left]
    simp

theorem type_eq (s : Section h σ a) :
    ℳ.typing.app (op Δ) a = Ty.map σ.op (yonedaEquiv A) := by
  have hhom : yonedaEquiv.symm a ≫ ℳ.typing = y σ ≫ A := by
    rw [← s.generic, ← yonedaEquiv_symm_naturality_left, Category.assoc, h.w,
      ← Category.assoc, ← Functor.map_comp, s.over]
  simp [yonedaEquiv_naturality, ← hhom, yonedaEquiv_comp]

variable {A' : y Γ' ⟶ Ty} {π' : ΓA' ⟶ Γ'} {q' : Tm.obj (op ΓA')}
  {h' : IsPullback (yonedaEquiv.symm q') (y π') ℳ.typing A'} {σ' : Δ ⟶ Γ'}

def map (s : Section h σ a) (f : ΓA ⟶ ΓA') (hover : s.hom ≫ f ≫ π' = σ')
    (hq : Tm.map f.op q' = q) : Section h' σ' a where
  hom := s.hom ≫ f
  over := by simp [hover]
  generic := by simp [hq, generic]

def lift {f : ΓA' ⟶ ΓA} {g : Γ' ⟶ Γ} (hf : IsPullback f π' π g) (hq : Tm.map f.op q = q')
    (s : Section h (σ' ≫ g) a) : Section h' σ' a where
  hom := hf.lift s.hom σ' s.over
  over := hf.lift_snd _ _ _
  generic := by
    rw [← hq, ← Functor.map_comp_apply, ← op_comp, hf.lift_fst]
    exact s.generic

end Section

variable (Ty Γ ΓA) in
structure Comprehension where
  type : y Γ ⟶ Ty
  disp : ΓA ⟶ Γ
  generic : Tm.obj (op ΓA)
  isPullback : IsPullback (yonedaEquiv.symm generic) (y disp) ℳ.typing type

abbrev Comprehension.Section (K : Comprehension Ty Γ ΓA) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ)) :=
  Metalean.TypeTheory.NaturalModel.Section K.isPullback σ a

namespace Comprehension

variable (K : Comprehension Ty Γ ΓA)

def toFibre (A : y Γ ⟶ Ty) (hA : A = K.type) : y ΓA ⟶ pullback A ℳ.typing :=
  pullback.lift (y K.disp) (yonedaEquiv.symm K.generic)
    (by rw [hA]; exact K.isPullback.w.symm)

@[reassoc (attr := simp)] theorem toFibre_fst (A : y Γ ⟶ Ty) (hA : A = K.type) :
    K.toFibre A hA ≫ pullback.fst A ℳ.typing = yoneda.map K.disp :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem toFibre_snd (A : y Γ ⟶ Ty) (hA : A = K.type) :
    K.toFibre A hA ≫ pullback.snd A ℳ.typing = yonedaEquiv.symm K.generic :=
  pullback.lift_snd _ _ _

def fibreIso : y ΓA ≅ pullback K.type ℳ.typing :=
  K.isPullback.flip.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

def equiv (X : Cᵒᵖ ⥤ Type u) : (pullback K.type ℳ.typing ⟶ X) ≃ X.obj (op ΓA) :=
  K.fibreIso.homFromEquiv.symm.trans yonedaEquiv

def eval (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) (hA : A = K.type) : X.obj (op ΓA) :=
  yonedaEquiv (K.toFibre A hA ≫ B)

def family (b : X.obj (op ΓA)) : pullback K.type ℳ.typing ⟶ X :=
  (K.equiv X).symm b

def label (b : X.obj (op ΓA)) : Σ A : y Γ ⟶ Ty, pullback A ℳ.typing ⟶ X :=
  ⟨K.type, K.family b⟩

theorem toFibre_self : K.toFibre K.type rfl = K.fibreIso.hom :=
  pullback.hom_ext (by simp [fibreIso]) (by simp [fibreIso])

theorem eval_eq_equiv (B : pullback K.type ℳ.typing ⟶ X) :
    K.eval K.type B rfl = K.equiv X B := by
  rw [eval, toFibre_self]
  rfl

@[simp] theorem eval_family (b : X.obj (op ΓA)) : K.eval K.type (K.family b) rfl = b :=
  (K.eval_eq_equiv _).trans ((K.equiv X).apply_symm_apply b)

@[simp] theorem family_eval (B : pullback K.type ℳ.typing ⟶ X) :
    K.family (K.eval K.type B rfl) = B :=
  ((K.equiv X).symm_apply_eq).mpr (K.eval_eq_equiv B)

@[simp] theorem label_eval (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) (hA : A = K.type) :
    K.label (K.eval A B hA) = ⟨A, B⟩ := by
  subst hA
  exact congrArg (Sigma.mk K.type) (K.family_eval B)

theorem map_eval (f : X ⟶ Y) (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) (hA : A = K.type) :
    f.app (op ΓA) (K.eval A B hA) = K.eval A (B ≫ f) hA :=
  (yonedaEquiv_comp (K.toFibre A hA ≫ B) f).symm.trans
    (congrArg yonedaEquiv (Category.assoc _ _ _))

theorem eval_congr {A₁ A₂ : y Γ ⟶ Ty} {B₁ : pullback A₁ ℳ.typing ⟶ X}
    {B₂ : pullback A₂ ℳ.typing ⟶ X}
    (e : (⟨A₁, B₁⟩ : Σ A : y Γ ⟶ Ty, pullback A ℳ.typing ⟶ X) = ⟨A₂, B₂⟩)
    (h₁ : A₁ = K.type) (h₂ : A₂ = K.type) : K.eval A₁ B₁ h₁ = K.eval A₂ B₂ h₂ := by
  cases e
  rfl

theorem map_family (f : X ⟶ Y) (b : X.obj (op ΓA)) :
    K.family b ≫ f = K.family (f.app (op ΓA) b) :=
  (K.family_eval (K.family b ≫ f)).symm.trans (congrArg K.family
    ((K.map_eval f K.type (K.family b) rfl).symm.trans
      (congrArg (f.app (op ΓA)) (K.eval_family b))))

theorem map_label (f : X ⟶ Y) (b : X.obj (op ΓA)) :
    ((polynomial Ty).map f).app (op Γ) (K.label b) = K.label (f.app (op ΓA) b) :=
  congrArg (Sigma.mk K.type) (K.map_family f b)

theorem eval_eq (K' : Comprehension Ty Γ ΓA') (f : ΓA' ⟶ ΓA)
    (hf : f ≫ K.disp = K'.disp) (hq : Tm.map f.op K.generic = K'.generic)
    (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) (hA : A = K.type) (hA' : A = K'.type) :
    K'.eval A B hA' = X.map f.op (K.eval A B hA) := by
  have hto : K'.toFibre A hA' = y f ≫ K.toFibre A hA :=
    pullback.hom_ext
      (by simp [← Functor.map_comp, hf])
      (by simp [← hq, yonedaEquiv_symm_naturality_left])
  simp [eval, hto, ← yonedaEquiv_naturality]

theorem eval_reindex (K' : Comprehension Ty Δ ΔA) (σ : Δ ⟶ Γ) (f : ΔA ⟶ ΓA)
    (hf : f ≫ K.disp = K'.disp ≫ σ) (hq : Tm.map f.op K.generic = K'.generic)
    (A : y Γ ⟶ Ty) (B : pullback A ℳ.typing ⟶ X) (hA : A = K.type)
    (hA' : y σ ≫ A = K'.type) :
    K'.eval (y σ ≫ A) (fibreMap A (y σ) ≫ B) hA' = X.map f.op (K.eval A B hA) := by
  have hto : K'.toFibre (y σ ≫ A) hA' ≫ fibreMap A (y σ) = y f ≫ K.toFibre A hA :=
    pullback.hom_ext
      (by simp [← Functor.map_comp, hf])
      (by simp [← hq, yonedaEquiv_symm_naturality_left])
  rw [eval, ← Category.assoc, hto, Category.assoc, eval, ← yonedaEquiv_naturality]

theorem label_reindex (K' : Comprehension Ty Δ ΔA) (σ : Δ ⟶ Γ) (f : ΔA ⟶ ΓA)
    (hf : f ≫ K.disp = K'.disp ≫ σ) (hq : Tm.map f.op K.generic = K'.generic)
    (hA : y σ ≫ K.type = K'.type) (b : X.obj (op ΓA)) :
    ((polynomial Ty).obj X).map σ.op (K.label b) = K'.label (X.map f.op b) := by
  rw [label, polynomial_obj_map, ← K'.label_eval (y σ ≫ K.type)
    (fibreMap K.type (y σ) ≫ K.family b) hA,
    K.eval_reindex K' σ f hf hq K.type (K.family b) rfl hA, eval_family]

end Comprehension

end Metalean.TypeTheory.NaturalModel
