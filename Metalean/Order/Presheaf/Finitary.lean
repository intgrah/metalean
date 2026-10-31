/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Filter.Defs
public import Metalean.Order.Presheaf.Ideal
import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Bases.Finite

@[expose] public section

universe u v

namespace Metalean.Presheaf

open CategoryTheory MonoidalCategory Opposite Filter

variable {C : Type u} [Category.{v} C]
variable {R S T U : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {A A' : Cᵒᵖ ⥤ Type (max u v)} {X : C}

namespace ΩIdeal

def IsFinitary (f : ΩIdeal R X → ΩIdeal S X) : Prop :=
  ∀ I {y}, (y ∈ (f I).app (𝟙 X)) →
    ∃ x, (x ∈ I.app (𝟙 X)) ∧ (y ∈ (f (principal R x)).app (𝟙 X))

theorem IsFinitary.comp {f : ΩIdeal R X → ΩIdeal S X} {g : ΩIdeal S X → ΩIdeal T X}
    (hg : IsFinitary g) (hf : IsFinitary f) (hm : Monotone g) : IsFinitary (g ∘ f) := by
  intro I y hy
  have ⟨b, hb, hy⟩ := hg (f I) hy
  have ⟨a, ha, hb⟩ := hf I hb
  exact ⟨a, ha, hm (ΩLower.principal_le_iff.mpr hb) (𝟙 X) y hy⟩

theorem IsFinitary.comp₂ {f : ΩIdeal R X × ΩIdeal S X → ΩIdeal T X}
    (hf : Monotone f)
    (h₁ : ∀ J, IsFinitary fun I => f (I, J))
    (h₂ : ∀ I, IsFinitary fun J => f (I, J))
    {g : ΩIdeal U X → ΩIdeal R X} {h : ΩIdeal U X → ΩIdeal S X}
    (hg : IsFinitary g) (hh : IsFinitary h) (hgm : Monotone g) (hhm : Monotone h) :
    IsFinitary fun I => f (g I, h I) := by
  intro I y hy
  have ⟨a, ha, hy⟩ := h₁ (h I) (g I) hy
  have ⟨b, hb, hy⟩ := h₂ (principal R a) (h I) hy
  have ⟨c, hc, ha⟩ := hg I ha
  have ⟨d, hd, hb⟩ := hh I hb
  have ⟨e, he, hce, hde⟩ := I.property (𝟙 X) hc hd
  exact ⟨e, he, hf
    ⟨ΩLower.principal_le_iff.mpr (hgm (ΩLower.principal_mono hce) (𝟙 X) a ha),
      ΩLower.principal_le_iff.mpr (hhm (ΩLower.principal_mono hde) (𝟙 X) b hb)⟩ (𝟙 X) y hy⟩

def Finitary (F : Functor.HomObj (presheaf R) (presheaf S) A) : Prop :=
  ∀ (X : Cᵒᵖ) (a : A.obj X), IsFinitary (F.app X a)

theorem Finitary.map (f : A' ⟶ A)
    {F : Functor.HomObj (presheaf R) (presheaf S) A} (hF : Finitary F) : Finitary (F.map f) :=
  fun X a => hF X (f.app X a)

end ΩIdeal

namespace ΩLower

variable {X : C}

def approximations (I : ΩLower R X) : Filter (ΩLower R X) :=
  ⨅ x : {x // x ∈ I.app (𝟙 X)}, Filter.principal (Set.Ici (principal R x.val))

theorem exists_finset_of_eventually {I : ΩLower R X} {P : ΩLower R X → Prop}
    (h : ∀ᶠ J in I.approximations, P J) :
    ∃ s : Finset (R.obj (op X)), (∀ x ∈ s, x ∈ I.app (𝟙 X)) ∧ P (s.sup (principal R)) := by
  classical
  obtain ⟨s, hs, hP⟩ := (Filter.hasBasis_iInf_principal_finite _).eventually_iff.mp h
  refine ⟨hs.toFinset.image Subtype.val, ?_, hP ?_⟩
  · intro x hx
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
    exact x.property
  · simp only [Set.mem_iInter, Set.mem_Ici]
    intro x hx
    exact Finset.le_sup (f := principal R) (Finset.mem_image.mpr ⟨x, hs.mem_toFinset.mpr hx, rfl⟩)

theorem eventually_mem {I : ΩLower R X} {x : R.obj (op X)} (hx : x ∈ I.app (𝟙 X)) :
    ∀ᶠ J in I.approximations, x ∈ J.app (𝟙 X) :=
  Filter.mem_iInf_of_mem ⟨x, hx⟩ (Filter.mem_principal.mpr fun _ h => principal_le_iff.mp h)

theorem eventually_sup_le {α : Type*} {l : Filter α} {f : α → ΩLower R X}
    (s : Finset (R.obj (op X)))
    (h : ∀ x ∈ s, ∀ᶠ a in l, (x ∈ (f a).app (𝟙 X))) :
    ∀ᶠ a in l, s.sup (principal R) ≤ f a :=
  (s.eventually_all.mpr h).mono fun _ h =>
    Finset.sup_le (α := ΩLower R X) fun x hx => principal_le_iff.mpr (h x hx)

def IsFinitary (f : ΩLower R X → ΩLower S X) : Prop :=
  ∀ I {y}, (y ∈ (f I).app (𝟙 X)) →
    ∃ s : Finset (R.obj (op X)), (∀ x ∈ s, (x ∈ I.app (𝟙 X))) ∧
      (y ∈ (f (s.sup (principal R))).app (𝟙 X))

variable {α : Type*} {l : Filter α}

theorem bind₂_eventually
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X))
    {I : ΩLower R X} {J : ΩLower S X} {Is : α → ΩLower R X} {Js : α → ΩLower S X}
    (hI : ∀ {x}, (x ∈ I.app (𝟙 X)) → ∀ᶠ a in l, (x ∈ (Is a).app (𝟙 X)))
    (hJ : ∀ {y}, (y ∈ J.app (𝟙 X)) → ∀ᶠ a in l, (y ∈ (Js a).app (𝟙 X)))
    {z} (hz : (z ∈ (bind₂ I J F).app (𝟙 X))) : ∀ᶠ a in l, (z ∈ (bind₂ (Is a) (Js a) F).app (𝟙 X)) := by
  have ⟨x, y, hx, hy, hz⟩ := (mem_bind₂ ..).mp hz
  filter_upwards [hI hx, hJ hy] with a hx hy
  exact (mem_bind₂ ..).mpr ⟨x, y, hx, hy, hz⟩

theorem iSup_eventually {ι : Sort*} {F : ι → ΩLower R X} {Fs : α → ι → ΩLower R X}
    (hF : ∀ i {y}, (y ∈ (F i).app (𝟙 X)) → ∀ᶠ a in l, (y ∈ (Fs a i).app (𝟙 X)))
    {y} (hy : (y ∈ (⨆ i, F i).app (𝟙 X))) : ∀ᶠ a in l, (y ∈ (⨆ i, Fs a i).app (𝟙 X)) := by
  rcases (mem_iSup ..).mp hy with hy | ⟨i, hy⟩
  · exact Eventually.of_forall fun _ => (mem_iSup ..).mpr (.inl hy)
  · exact (hF i hy).mono fun _ hy => (mem_iSup ..).mpr (.inr ⟨i, hy⟩)

namespace IsFinitary

protected theorem id : IsFinitary fun I : ΩLower R X => I :=
  fun _ y hy => ⟨{y}, by simpa using hy, by simp⟩

protected theorem const (J : ΩLower S X) : IsFinitary fun _ : ΩLower R X => J :=
  fun _ _ hy => ⟨∅, by simp, hy⟩

theorem of_eventually {f : ΩLower R X → ΩLower S X}
    (h : ∀ I {y}, (y ∈ (f I).app (𝟙 X)) → ∀ᶠ J in I.approximations, (y ∈ (f J).app (𝟙 X))) :
    IsFinitary f := fun I _ hy => exists_finset_of_eventually (h I hy)

theorem eventually {f : ΩLower R X → ΩLower S X} (hf : IsFinitary f) (hm : Monotone f)
    {α : Type*} {l : Filter α} {I : ΩLower R X} {Is : α → ΩLower R X}
    (hI : ∀ {x}, (x ∈ I.app (𝟙 X)) → ∀ᶠ a in l, (x ∈ (Is a).app (𝟙 X)))
    {y} (hy : (y ∈ (f I).app (𝟙 X))) : ∀ᶠ a in l, (y ∈ (f (Is a)).app (𝟙 X)) :=
  have ⟨s, hs, hy⟩ := hf I hy
  (eventually_sup_le s fun x hx => hI (hs x hx)).mono fun _ h => hm h (𝟙 X) y hy

theorem comp {f : ΩLower R X → ΩLower S X} {g : ΩLower S X → ΩLower T X}
    (hg : IsFinitary g) (hf : IsFinitary f) (hgm : Monotone g) (hfm : Monotone f) :
    IsFinitary (g ∘ f) :=
  of_eventually fun _ _ hy => hg.eventually hgm (hf.eventually hfm eventually_mem) hy

theorem apply {f : ΩLower R X → ΩLower S X → ΩLower T X} {g : ΩLower R X → ΩLower S X}
    (hf : ∀ J, IsFinitary fun I => f I J) (harg : ∀ I, IsFinitary (f I))
    (hg : IsFinitary g) (hm : Monotone f) (hargm : ∀ I, Monotone (f I)) (hgm : Monotone g) :
    IsFinitary fun I => f I (g I) := by
  apply of_eventually
  intro I y hy
  have ⟨s, hs, hy⟩ := harg I (g I) hy
  filter_upwards
    [eventually_sup_le s fun x hx => hg.eventually hgm eventually_mem (hs x hx),
     (hf (s.sup (principal S))).eventually (fun _ _ h => hm h _) eventually_mem hy]
    with J harg hf
  exact hargm J harg (𝟙 X) y hf

theorem exists_principal {f : ΩLower R X → ΩLower S X} (hf : IsFinitary f) (hm : Monotone f)
    {I : ΩLower R X} (hI : I.IsDirected) {y} (hy : (y ∈ (f I).app (𝟙 X))) :
    ∃ x, (x ∈ I.app (𝟙 X)) ∧ (y ∈ (f (principal R x)).app (𝟙 X)) :=
  have ⟨s, hs, hy⟩ := hf I hy
  have ⟨x, hx, hsx⟩ := hI.exists_upper_fin (𝟙 X) (fun a : s => a.1) fun a => hs a.1 a.2
  ⟨x, hx, hm (Finset.sup_le (α := ΩLower R X) fun a ha => principal_mono (hsx ⟨a, ha⟩)) (𝟙 X) y hy⟩

end IsFinitary

end ΩLower

end Metalean.Presheaf
