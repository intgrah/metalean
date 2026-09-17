module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Metalean.Order.Category.CondSemilatSup.Basic
public import Metalean.Order.Category.Preord.Functor
import Mathlib.Data.Fintype.Order

@[expose] public section

universe u v w

namespace Metalean.Presheaf

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]

structure ΩLower (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (X : C) where
  mem {Y : C} : (Y ⟶ X) → R.obj (op Y) → Prop
  natural {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Y)) :
    mem f a → mem (g ≫ f) (R.map g.op a)
  bottom {Y : C} (f : Y ⟶ X) : mem f ⊥
  lower {Y : C} {a b : R.obj (op Y)} (f : Y ⟶ X) : a ≤ b → mem f b → mem f a

namespace ΩLower

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y Z : C} {ι : Sort*}

@[ext] theorem ext {L M : ΩLower R X}
    (h : ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)), L.mem f a ↔ M.mem f a) : L = M := by
  cases L
  cases M
  congr
  funext Y f a
  exact propext (h f a)

instance : PartialOrder (ΩLower R X) where
  le L M := ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)), L.mem f a → M.mem f a
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ h₁ h₂ := fun f a h => h₂ f a (h₁ f a h)
  le_antisymm _ _ h₁ h₂ := ext fun f a => ⟨h₁ f a, h₂ f a⟩

def pullback (L : ΩLower R X) (f : Y ⟶ X) : ΩLower R Y where
  mem g a := L.mem (g ≫ f) a
  natural g h a ha := (Category.assoc h g f).symm ▸ L.natural (g ≫ f) h a ha
  bottom _ := L.bottom _
  lower _ := L.lower _

@[simp↓] theorem presheaf_map_mem (L : ΩLower R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Z)) :
    (L.pullback f).mem g a ↔ L.mem (g ≫ f) a := Iff.rfl

@[implicit_reducible, simps! obj]
def presheaf (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : Cᵒᵖ ⥤ Preord.{max u v} where
  obj X := Preord.of (ΩLower R X.unop)
  map f := Preord.ofHom { toFun L := L.pullback f.unop, monotone' _ _ h := fun g => h (g ≫ f.unop) }
  map_id _ := Preord.ext fun L => ext fun g a => Iff.of_eq (congrArg (L.mem · a) (Category.comp_id g))
  map_comp f g := Preord.ext fun L => ext fun h a =>
    Iff.of_eq (congrArg (L.mem · a) (Category.assoc h g.unop f.unop).symm)

@[simp↓] theorem presheaf_map_eq_pullback {X Y : Cᵒᵖ} (g : X ⟶ Y) (L : ΩLower R X.unop) :
    (presheaf R).map g L = L.pullback g.unop := rfl

@[simp] theorem pullback_id (L : ΩLower R X) : L.pullback (𝟙 X) = L :=
  (presheaf R).map_id_apply _ L

@[simp] theorem pullback_pullback (L : ΩLower R X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (L.pullback f).pullback g = L.pullback (g ≫ f) :=
  ((presheaf R).map_comp_apply f.op g.op L).symm

theorem pullback_mono {L M : ΩLower R X} (h : L ≤ M) (f : Y ⟶ X) : L.pullback f ≤ M.pullback f :=
  fun g => h (g ≫ f)

theorem homObj_app_map_mem {F : Cᵒᵖ ⥤ Preord.{max u v}} {A : Cᵒᵖ ⥤ Type w}
    (G : Functor.HomObj F (presheaf R) A) {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.obj X) (x : F.obj X)
    (h : Z ⟶ Y.unop) (b : R.obj (op Z)) :
    (G.app Y (A.map g a) (F.map g x)).mem h b ↔ (G.app X a x).mem (h ≫ g.unop) b := by
  rw [G.naturality_apply]
  exact Iff.rfl

def principal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (a : R.obj (op X)) : ΩLower R X where
  mem f b := b ≤ R.map f.op a
  natural f g b hb := by simpa using map_rel (ConcreteCategory.hom (R.map g.op)) hb
  bottom _ := bot_le
  lower _ h hb := h.trans hb

@[simp] theorem mem_principal (a : R.obj (op X)) (f : Y ⟶ X) (b : R.obj (op Y)) :
    (principal R a).mem f b ↔ b ≤ R.map f.op a := Iff.rfl

instance : Bot (ΩLower R X) := ⟨principal R ⊥⟩

@[simp] theorem mem_bot (f : Y ⟶ X) (a : R.obj (op Y)) :
    (⊥ : ΩLower R X).mem f a ↔ a ≤ ⊥ := by
  change a ≤ R.map f.op ⊥ ↔ _
  simp

instance : SupSet (ΩLower R X) where
  sSup S := {
    mem f a := a ≤ ⊥ ∨ ∃ L ∈ S, L.mem f a
    natural f g a
      | .inl h => .inl ((R.map g.op).map_le_bot h)
      | .inr ⟨L, hL, h⟩ => .inr ⟨L, hL, L.natural f g a h⟩
    bottom _ := .inl le_rfl
    lower f h
      | .inl hb => .inl (h.trans hb)
      | .inr ⟨L, hL, hb⟩ => .inr ⟨L, hL, L.lower f h hb⟩ }

@[simp] theorem mem_sSup (S : Set (ΩLower R X)) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (sSup S).mem f a ↔ a ≤ ⊥ ∨ ∃ L ∈ S, L.mem f a := Iff.rfl

instance : CompleteLattice (ΩLower R X) where
  bot := ⊥
  bot_le L := fun f _ h => L.lower f (mem_bot _ _ |>.mp h) (L.bottom f)
  __ := completeLatticeOfSup (ΩLower R X) fun S => ⟨
    fun L hL _ f a ha => .inr ⟨L, hL, ha⟩,
    fun L hL _ f a ha => by
      rcases ha with ha | ⟨M, hM, ha⟩
      · exact L.lower f ha (L.bottom f)
      · exact hL hM f a ha⟩

instance (X : Cᵒᵖ) : CompleteLattice ((presheaf R).obj X) :=
  inferInstanceAs (CompleteLattice (ΩLower R X.unop))

@[simp]
theorem mem_iSup (L : ι → ΩLower R X) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (⨆ i, L i).mem f a ↔ a ≤ ⊥ ∨ ∃ i, (L i).mem f a := by
  change (sSup (Set.range L)).mem f a ↔ _
  simp

@[simp] theorem mem_iSup_of_nonempty [Nonempty ι]
    (L : ι → ΩLower R X) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (⨆ i, L i).mem f a ↔ ∃ i, (L i).mem f a := by
  rw [mem_iSup]
  exact or_iff_right_of_imp fun h => Nonempty.elim ‹_› fun i => ⟨i, (L i).lower f h ((L i).bottom f)⟩

@[simp↓] theorem presheaf_map_mem_id (L : ΩLower R X) (f : Y ⟶ X)
    (a : R.obj (op Y)) :
    (L.pullback f).mem (𝟙 Y) a ↔ L.mem f a := by simp

@[simp] theorem pullback_iSup (L : ι → ΩLower R X) (f : Y ⟶ X) :
    (⨆ i, L i).pullback f = ⨆ i, (L i).pullback f := by
  ext
  simp

@[simp] theorem presheaf_map_bot (f : Y ⟶ X) :
    (⊥ : ΩLower R X).pullback f = ⊥ := by
  ext
  simp

@[simp]
theorem mem_principal_id (a b : R.obj (op X)) :
    (principal R a).mem (𝟙 X) b ↔ b ≤ a := by
  simp

@[simp] theorem principal_le_iff {a : R.obj (op X)} {L : ΩLower R X} :
    principal R a ≤ L ↔ L.mem (𝟙 X) a := by
  constructor
  · exact fun h => h (𝟙 X) a ((mem_principal_id a a).mpr (le_refl a))
  · intro ha Y f b hb
    have ha' : L.mem f (R.map f.op a) := by
      simpa using L.natural (𝟙 X) f a ha
    exact L.lower f ((mem_principal a f b).mp hb) ha'

theorem principal_mono {a b : R.obj (op X)} (h : a ≤ b) :
    principal R a ≤ principal R b :=
  principal_le_iff.mpr ((mem_principal_id b a).mpr h)

@[simp]
theorem presheaf_map_principal (a : R.obj (op X)) (f : Y ⟶ X) :
    (principal R a).pullback f = principal R (R.map f.op a) := by
  ext
  simp

@[simp]
theorem principal_bottom : principal R (⊥ : R.obj (op X)) = ⊥ := rfl

def IsDirected (L : ΩLower R X) : Prop :=
  ∀ {Y : C} (f : Y ⟶ X) {a b : R.obj (op Y)},
    L.mem f a → L.mem f b → ∃ c : R.obj (op Y), L.mem f c ∧ a ≤ c ∧ b ≤ c

theorem IsDirected.pullback {L : ΩLower R X} (hL : L.IsDirected) (f : Y ⟶ X) :
    (L.pullback f).IsDirected := fun g => hL (g ≫ f)

def directedSubfunctor (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) :
    Subfunctor (presheaf R ⋙ forget Preord) where
  obj _ := {L | L.IsDirected}
  map f _ h := h.pullback f.unop

theorem isDirected_principal (a : R.obj (op X)) :
    (principal R a).IsDirected :=
  fun f => fun hb hc => ⟨R.map f.op a, (mem_principal _ _ _).mpr le_rfl,
    (mem_principal _ _ _).mp hb, (mem_principal _ _ _).mp hc⟩

theorem isDirected_bot : (⊥ : ΩLower R X).IsDirected := isDirected_principal ⊥

theorem IsDirected.iSup {ι : Sort*} [Nonempty ι] {L : ι → ΩLower R X}
    (hdir : Directed (· ≤ ·) L) (hL : ∀ i, (L i).IsDirected) : (⨆ i, L i).IsDirected := by
  intro Y f a b ha hb
  have ⟨i, ha⟩ := (mem_iSup_of_nonempty L f a).mp ha
  have ⟨j, hb⟩ := (mem_iSup_of_nonempty L f b).mp hb
  have ⟨k, hik, hjk⟩ := hdir i j
  have ⟨c, hc, hac, hbc⟩ := hL k f (hik f a ha) (hjk f b hb)
  exact ⟨c, (mem_iSup_of_nonempty L f c).mpr ⟨k, hc⟩, hac, hbc⟩

theorem IsDirected.exists_upper_fin {L : ΩLower R X} (hL : L.IsDirected) (f : Y ⟶ X)
    {κ : Type*} [Finite κ] (a : κ → R.obj (op Y)) (ha : ∀ i, L.mem f (a i)) :
    ∃ b, L.mem f b ∧ ∀ i, a i ≤ b := by
  have : Nonempty {a // L.mem f a} := ⟨(⊥ : R.obj (op Y)), L.bottom f⟩
  have hd : Directed (· ≤ ·) (Subtype.val : {a // L.mem f a} → R.obj (op Y)) :=
    fun a b => let ⟨c, hc, hac, hbc⟩ := hL f a.prop b.prop; ⟨⟨c, hc⟩, hac, hbc⟩
  have ⟨b, hb⟩ := hd.finite_le fun i => ⟨a i, ha i⟩
  exact ⟨b, b.property, hb⟩

section HomLattice

variable {F : Cᵒᵖ ⥤ Preord.{max u v}} {A : Cᵒᵖ ⥤ Type v}

instance : CompleteLattice (Functor.HomObj F (presheaf R) A) :=
  Functor.HomObj.completeLattice (G := presheaf R ⋙ forget Preord)
    (lattice := fun X => inferInstanceAs (CompleteLattice (ΩLower R X.unop)))
    (fun f => (presheaf R |>.map f).hom.monotone) (by
      intro X Y f S
      change (sSup S : ΩLower R X.unop).pullback f.unop = sSup ((pullback · f.unop) '' S)
      rw [sSup_image, sSup_eq_iSup]
      simp)

theorem homObj_sSup_app (S : Set (Functor.HomObj F (presheaf R) A)) (X : Cᵒᵖ) (a : A.obj X)
    (x : F.obj X) : (sSup S).app X a x = ⨆ α ∈ S, α.app X a x := by
  change (⨆ α ∈ S, (α.app X a).hom) x = _
  simp only [OrderHom.iSup_apply]

@[simp] theorem homObj_iSup_app (α : ι → Functor.HomObj F (presheaf R) A) (X : Cᵒᵖ)
    (a : A.obj X) (x : F.obj X) : (⨆ i, α i).app X a x = ⨆ i, (α i).app X a x := by
  change (sSup (Set.range α)).app X a x = _
  rw [homObj_sSup_app, iSup_range]

end HomLattice

@[simps! app_hom_coe] def principalNatTrans (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) :
    R ⋙ forget₂ CondSemilatSup Preord ⟶ presheaf R where
  app _ := Preord.ofHom { toFun := principal R, monotone' _ _ h := principal_mono h }
  naturality {_ _} f := Preord.ext fun x => (presheaf_map_principal x f.unop).symm

end ΩLower

end Metalean.Presheaf
