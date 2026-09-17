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

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {Γ Δ : C}

def ext (A : y Γ ⟶ Ty) : C :=
  ℳ.representable.pullback A

def disp (A : y Γ ⟶ Ty) : ext A ⟶ Γ :=
  ℳ.representable.snd A

def var (A : y Γ ⟶ Ty) : y (ext A) ⟶ Tm :=
  ℳ.representable.fst A

theorem ext_isPullback (A : y Γ ⟶ Ty) :
    IsPullback (var A) (y (disp A)) ℳ.typing A :=
  ℳ.representable.isPullback A

def comprehension (A : y Γ ⟶ Ty) : Comprehension Ty Γ (ext A) where
  type := A
  disp := disp A
  generic := yonedaEquiv (var A)
  isPullback := by simp; exact ext_isPullback A

@[simp] theorem comprehension_type (A : y Γ ⟶ Ty) : (comprehension A).type = A := rfl

def substTerm (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) : Δ ⟶ ext A :=
  (Section.ofTerm (comprehension A).isPullback σ a (by
    rw [comprehension_type, yonedaEquiv_symm_naturality_right, ha, Equiv.symm_apply_apply])).hom

theorem substTerm_disp (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) :
    substTerm A σ a ha ≫ disp A = σ :=
  (Section.ofTerm (comprehension A).isPullback σ a _).over

def extMap (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) : ext (y σ ≫ A) ⟶ ext A :=
  yoneda.preimage ((ext_isPullback A).lift (var (y σ ≫ A)) (y (disp (y σ ≫ A) ≫ σ))
    (by simp [(ext_isPullback (y σ ≫ A)).w]))

@[reassoc] theorem extMap_disp (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    extMap σ A ≫ disp A = disp (y σ ≫ A) ≫ σ :=
  yoneda.map_injective (by simp [extMap])

theorem extMap_var (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    y (extMap σ A) ≫ var A = var (y σ ≫ A) := by
  simp [extMap]

def genericTerm (A : y Γ ⟶ Ty) : Tm.obj (op (ext A)) :=
  yonedaEquiv (var A)

theorem genericTerm_typing (A : y Γ ⟶ Ty) :
    ℳ.typing.app _ (genericTerm A) = yonedaEquiv (y (disp A) ≫ A) := by
  rw [genericTerm, ← yonedaEquiv_comp, (ext_isPullback A).w]

theorem extMap_genericTerm (σ : Δ ⟶ Γ) (A : y Γ ⟶ Ty) :
    Tm.map (extMap σ A).op (genericTerm A) = genericTerm (y σ ≫ A) := by
  simp [genericTerm, yonedaEquiv_naturality, extMap_var]

theorem map_substTerm_genericTerm (A : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (a : Tm.obj (op Δ))
    (ha : ℳ.typing.app (op Δ) a = yonedaEquiv (y σ ≫ A)) :
    Tm.map (substTerm A σ a ha).op (genericTerm A) = a :=
  (Section.ofTerm (comprehension A).isPullback σ a (by
    rw [comprehension_type, yonedaEquiv_symm_naturality_right, ha, Equiv.symm_apply_apply])).generic

theorem map_term_typing (X : y Γ ⟶ Ty) (σ : Δ ⟶ Γ) (b : Tm.obj (op Γ))
    (hb : ℳ.typing.app (op Γ) b = yonedaEquiv X) :
    ℳ.typing.app (op Δ) (Tm.map σ.op b) = yonedaEquiv (y σ ≫ X) := by
  simp [hb, ← yonedaEquiv_naturality]

def termOfHom (A : y Γ ⟶ Ty) (s : Δ ⟶ ext A) : Tm.obj (op Δ) :=
  Tm.map s.op (genericTerm A)

theorem termOfHom_typing (A : y Γ ⟶ Ty) (s : Δ ⟶ ext A) :
    ℳ.typing.app (op Δ) (termOfHom A s) = yonedaEquiv (y (s ≫ disp A) ≫ A) := by
  simp [termOfHom, genericTerm_typing, ← yonedaEquiv_naturality]

structure Sect (B : y Γ ⟶ Ty) where
  hom : Γ ⟶ ext B
  hom_disp : hom ≫ disp B = 𝟙 Γ

def Sect.term {A : y Γ ⟶ Ty} (f : Sect A) : Tm.obj (op Γ) :=
  termOfHom A f.hom

theorem Sect.term_typing {A : y Γ ⟶ Ty} (f : Sect A) :
    ℳ.typing.app (op Γ) f.term = yonedaEquiv A := by
  simp [Sect.term, termOfHom_typing, f.hom_disp]

def Sect.ofTerm (A : y Γ ⟶ Ty) (a : Tm.obj (op Γ))
    (ha : ℳ.typing.app (op Γ) a = yonedaEquiv A) : Sect A where
  hom := substTerm A (𝟙 Γ) a (by simp [ha])
  hom_disp := substTerm_disp _ _ _ _

@[simp] theorem Sect.term_ofTerm (A : y Γ ⟶ Ty) (a : Tm.obj (op Γ))
    (ha : ℳ.typing.app (op Γ) a = yonedaEquiv A) : (Sect.ofTerm A a ha).term = a :=
  (Section.ofTerm (comprehension A).isPullback (𝟙 Γ) a _).generic

def Sect.convert {A B : y Γ ⟶ Ty} (h : A = B) (f : Sect A) : Sect B :=
  Sect.ofTerm B f.term (by rw [f.term_typing, h])

def Sect.pullbackAlong {A : y Γ ⟶ Ty} (σ : Δ ⟶ Γ) (f : Sect A) : Sect (y σ ≫ A) :=
  Sect.ofTerm _ (Tm.map σ.op f.term) (map_term_typing _ _ _ f.term_typing)

end Metalean.TypeTheory.NaturalModel
