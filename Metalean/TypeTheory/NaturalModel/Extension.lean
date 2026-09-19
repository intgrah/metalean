/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Comprehension

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} (ℳ : NaturalModel Ty Tm)
  {Γ Δ : C}

def comprehension (A : y Γ ⟶ Ty) : Comprehension ℳ Γ (ℳ.ext A) where
  type := A
  disp := ℳ.disp A
  generic := yonedaEquiv (ℳ.var A)
  isPullback := by simp; exact ℳ.isPullback A

@[simp] theorem comprehension_type (A : y Γ ⟶ Ty) : (ℳ.comprehension A).type = A := rfl

def substTerm (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) : Δ ⟶ ℳ.ext A :=
  (Section.ofTerm (ℳ.comprehension A).isPullback σ a (by
    rw [ℳ.comprehension_type, yonedaEquiv_symm_naturality_right, ha, Equiv.symm_apply_apply])).hom

theorem substTerm_disp (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) :
    ℳ.substTerm A σ a ha ≫ ℳ.disp A = σ :=
  (Section.ofTerm (ℳ.comprehension A).isPullback σ a _).over

def extMap (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) : ℳ.ext (y σ ≫ A) ⟶ ℳ.ext A :=
  yoneda.preimage ((ℳ.isPullback A).lift (ℳ.var (y σ ≫ A)) (y (ℳ.disp (y σ ≫ A) ≫ σ))
    (by simp [(ℳ.isPullback (y σ ≫ A)).w]))

@[reassoc] theorem extMap_disp (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    ℳ.extMap σ A ≫ ℳ.disp A = ℳ.disp (y σ ≫ A) ≫ σ :=
  yoneda.map_injective (by simp [extMap])

theorem extMap_var (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    y (ℳ.extMap σ A) ≫ ℳ.var A = ℳ.var (y σ ≫ A) := by
  simp [extMap]

def genericTerm (A : y Γ ⟶ Ty) : Tm.obj (op (ℳ.ext A)) :=
  yonedaEquiv (ℳ.var A)

theorem genericTerm_typing (A : y Γ ⟶ Ty) :
    ℳ.typing.app _ (ℳ.genericTerm A) = yonedaEquiv (y (ℳ.disp A) ≫ A) := by
  rw [genericTerm, ← yonedaEquiv_comp, (ℳ.isPullback A).w]

theorem extMap_genericTerm (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    Tm.map (ℳ.extMap σ A).op (ℳ.genericTerm A) = ℳ.genericTerm (y σ ≫ A) := by
  simp [genericTerm, yonedaEquiv_naturality, ℳ.extMap_var]

theorem map_substTerm_genericTerm (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) :
    Tm.map (ℳ.substTerm A σ a ha).op (ℳ.genericTerm A) = a :=
  (Section.ofTerm (ℳ.comprehension A).isPullback σ a (by
    rw [ℳ.comprehension_type, yonedaEquiv_symm_naturality_right, ha,
      Equiv.symm_apply_apply])).generic

theorem map_term_typing (X : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (b : Tm.obj (op Γ))
    (hb : ℳ.typing.app (op Γ) b = yonedaEquiv X) :
    ℳ.typing.app (op Δ) (Tm.map σ.op b) = yonedaEquiv (y σ ≫ X) := by
  simp [hb, ← yonedaEquiv_naturality]

def termOfHom (A : y Γ ⟶ Ty) (s : Δ ⟶ ℳ.ext A) : Tm.obj (op Δ) :=
  Tm.map s.op (ℳ.genericTerm A)

theorem termOfHom_typing (A : y Γ ⟶ Ty) (s : Δ ⟶ ℳ.ext A) :
    ℳ.typing.app (op Δ) (ℳ.termOfHom A s) = yonedaEquiv (y (s ≫ ℳ.disp A) ≫ A) := by
  simp [termOfHom, ℳ.genericTerm_typing, ← yonedaEquiv_naturality]

structure Sect (B : y Γ ⟶ Ty) where
  hom : Γ ⟶ ℳ.ext B
  hom_disp : hom ≫ ℳ.disp B = 𝟙 Γ

section

variable {ℳ}

def Sect.term {A : y Γ ⟶ Ty} (f : Sect ℳ A) : Tm.obj (op Γ) :=
  ℳ.termOfHom A f.hom

theorem Sect.term_typing {A : y Γ ⟶ Ty} (f : Sect ℳ A) :
    ℳ.typing.app (op Γ) f.term = yonedaEquiv A := by
  simp [Sect.term, ℳ.termOfHom_typing, f.hom_disp]

def Sect.ofTerm (A : y Γ ⟶ Ty) (a : Tm.obj (op Γ))
    (ha : ℳ.typing.app (op Γ) a = yonedaEquiv A) : Sect ℳ A where
  hom := ℳ.substTerm A (𝟙 Γ) a (by simp [ha])
  hom_disp := ℳ.substTerm_disp _ _ _ _

@[simp] theorem Sect.term_ofTerm (A : y Γ ⟶ Ty) (a : Tm.obj (op Γ))
    (ha : ℳ.typing.app (op Γ) a = yonedaEquiv A) : (Sect.ofTerm A a ha).term = a :=
  (Section.ofTerm (ℳ.comprehension A).isPullback (𝟙 Γ) a _).generic

theorem Sect.ext_term {A : y Γ ⟶ Ty} {f g : Sect ℳ A} (h : f.term = g.term) : f = g := by
  have hhom : f.hom = g.hom :=
    Section.hom_eq (h := (ℳ.comprehension A).isPullback) (σ := 𝟙 Γ) (a := f.term)
      ⟨f.hom, f.hom_disp, rfl⟩ ⟨g.hom, g.hom_disp, h.symm⟩
  cases f
  cases g
  cases hhom
  rfl

def Sect.convert {A B : y Γ ⟶ Ty} (h : A = B) (f : Sect ℳ A) : Sect ℳ B :=
  Sect.ofTerm B f.term (by rw [f.term_typing, h])

def Sect.pullbackAlong {A : y Γ ⟶ Ty} (σ : Δ ⟶ Γ) (f : Sect ℳ A) : Sect ℳ (y σ ≫ A) :=
  Sect.ofTerm _ (Tm.map σ.op f.term) (ℳ.map_term_typing _ _ _ f.term_typing)

@[simp] theorem Sect.term_convert {A B : y Γ ⟶ Ty} (h : A = B) (f : Sect ℳ A) :
    (Sect.convert h f).term = f.term :=
  Sect.term_ofTerm _ _ _

@[simp] theorem Sect.term_pullbackAlong {A : y Γ ⟶ Ty} (σ : Δ ⟶ Γ) (f : Sect ℳ A) :
    (Sect.pullbackAlong σ f).term = Tm.map σ.op f.term :=
  Sect.term_ofTerm _ _ _

end

variable {ℳ} in
theorem Sect.hom_pullbackAlong {A : y Γ ⟶ Ty} (σ : Δ ⟶ Γ) (a : Sect ℳ A) :
    (Sect.pullbackAlong σ a).hom ≫ ℳ.extMap σ A = σ ≫ a.hom := by
  refine Section.hom_eq (h := (ℳ.comprehension A).isPullback) (σ := σ)
    (a := Tm.map σ.op a.term) ⟨_, ?_, ?_⟩ ⟨σ ≫ a.hom, ?_, ?_⟩
  · change ((Sect.pullbackAlong σ a).hom ≫ ℳ.extMap σ A) ≫ ℳ.disp A = σ
    rw [Category.assoc, ℳ.extMap_disp, ← Category.assoc, (Sect.pullbackAlong σ a).hom_disp,
      Category.id_comp]
  · simp
    change Tm.map (Sect.pullbackAlong σ a).hom.op (Tm.map (ℳ.extMap σ A).op (ℳ.genericTerm A)) = _
    rw [ℳ.extMap_genericTerm]
    exact Sect.term_ofTerm _ _ _
  · change (σ ≫ a.hom) ≫ ℳ.disp A = σ
    simp [a.hom_disp]
  · simp
    rfl

end Metalean.TypeTheory.NaturalModel
