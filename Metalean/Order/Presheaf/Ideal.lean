/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Order.UpperLower.Prod
public import Metalean.Order.Category.CondSemilatSup.Cartesian
public import Metalean.Order.Category.Preord.Cartesian
public import Metalean.Order.Presheaf.Lower

@[expose] public section

universe u v

namespace Metalean.Presheaf

open CategoryTheory MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C]
  {R S T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y Z : C}

abbrev ΩIdeal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (X : C) :=
  {L : ΩLower R X // L.IsDirected}

@[implicit_reducible, simps! obj]
def ΩIdeal.presheaf (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : Cᵒᵖ ⥤ Preord.{max u v} where
  __ := (ΩLower.directedSubfunctor R).toPreord
  obj X := Preord.of (ΩIdeal R X.unop)

def ΩLower.toIdeal (L : ΩLower R X) (hL : L.IsDirected) : ΩIdeal R X := ⟨L, hL⟩

namespace ΩIdeal

instance (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (X : Cᵒᵖ) :
    PartialOrder ((presheaf R).obj X) := inferInstanceAs (PartialOrder (ΩIdeal R X.unop))

def pullback (I : ΩIdeal R X) (f : Y ⟶ X) : ΩIdeal R Y := (presheaf R).map f.op I

@[simp] theorem pullback_id (I : ΩIdeal R X) : I.pullback (𝟙 X) = I :=
  (presheaf R).map_id_apply _ I

@[simp] theorem pullback_pullback (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (I.pullback f).pullback g = I.pullback (g ≫ f) :=
  ((presheaf R).map_comp_apply f.op g.op I).symm

theorem pullback_mono {I J : ΩIdeal R X} (h : I ≤ J) (f : Y ⟶ X) : I.pullback f ≤ J.pullback f :=
  ((presheaf R).map f.op).hom.monotone h

@[implicit_reducible] def app (I : ΩIdeal R X) (f : Y ⟶ X) : Order.Ideal (R.obj (op Y)) where
  __ := I.val.app f
  nonempty' := ⟨⊥, I.val.bottom f⟩
  directed' _ ha _ hb := I.property f ha hb

theorem bottom (I : ΩIdeal R X) (f : Y ⟶ X) : (⊥ ∈ I.app f) := I.val.bottom f

theorem natural (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Y)) :
    (a ∈ I.app f) → ((R.map g.op a) ∈ I.app (g ≫ f)) := I.val.natural f g a

@[simp]
theorem mem_app (I : ΩIdeal R X) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (a ∈ I.app f) ↔ (a ∈ I.val.app f) := Iff.rfl

@[ext]
theorem ext {I J : ΩIdeal R X}
    (h : ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)),
      (a ∈ I.app f) ↔ (a ∈ J.app f)) : I = J :=
  Subtype.val_injective (ΩLower.ext h)

instance : OrderBot (ΩIdeal R X) where
  bot := ⟨⊥, ΩLower.isDirected_bot⟩
  bot_le I := @bot_le (ΩLower R X) _ _ I.val

@[simp]
theorem mem_bot (f : Y ⟶ X) (a : R.obj (op Y)) :
    (a ∈ (⊥ : ΩIdeal R X).app f) ↔ a ≤ ⊥ := ΩLower.mem_bot f a

@[simp↓] theorem presheaf_map_mem (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Z)) :
    (a ∈ (I.pullback f).app g) ↔ (a ∈ I.app (g ≫ f)) := Iff.rfl

@[simp↓] theorem presheaf_map_mem_id (I : ΩIdeal R X) (f : Y ⟶ X)
    (a : R.obj (op Y)) :
    (a ∈ (I.pullback f).app (𝟙 Y)) ↔ (a ∈ I.app f) := by simp

@[simp] theorem pullback_bot (f : Y ⟶ X) : (⊥ : ΩIdeal R X).pullback f = ⊥ :=
  Subtype.val_injective (ΩLower.presheaf_map_bot f)

def principal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (x : R.obj (op X)) : ΩIdeal R X where
  val := ΩLower.principal R x
  property := ΩLower.isDirected_principal x

@[simp] theorem principal_app (a : R.obj (op X)) (f : Y ⟶ X) :
    (principal R a).app f = Order.Ideal.principal (R.map f.op a) := rfl

@[simp]
theorem presheaf_map_principal (x : R.obj (op X)) (f : Y ⟶ X) :
    (principal R x).pullback f = principal R (R.map f.op x) :=
  Subtype.val_injective (ΩLower.presheaf_map_principal x f)

@[simp]
theorem val_principal (a : R.obj (op X)) :
    (principal R a).val = ΩLower.principal R a := rfl

@[simps! app_hom_coe] def principalNatTrans (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : R ⋙ forget₂ CondSemilatSup Preord ⟶ presheaf R where
  app _ := Preord.ofHom {
    toFun := principal R
    monotone' _ _ h := ΩLower.principal_mono h }
  naturality {_ _} f := Preord.ext fun x => (presheaf_map_principal x f.unop).symm

@[simps! app_hom_coe] def toLowerNatTrans (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) : presheaf R ⟶ ΩLower.presheaf R where
  app _ := Preord.ofHom (OrderEmbedding.subtype _).toOrderHom
  naturality {_ _} _ := rfl

end ΩIdeal

namespace ΩLower

def pair (I : ΩLower R X) (J : ΩLower S X) : ΩLower (R ⊗ S) X where
  app f := (I.app f).prod (J.app f)
  natural f g := fun (a, b) ⟨ha, hb⟩ => ⟨I.natural f g a ha, J.natural f g b hb⟩
  bottom f := ⟨I.bottom f, J.bottom f⟩

theorem IsDirected.pair {I : ΩLower R X} {J : ΩLower S X}
    (hI : I.IsDirected) (hJ : J.IsDirected) : (I.pair J).IsDirected := by
  intro Y f a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
  have ⟨c, hc, hac, hbc⟩ := hI f ha₁ hb₁
  have ⟨d, hd, had, hbd⟩ := hJ f ha₂ hb₂
  exact ⟨(c, d), ⟨hc, hd⟩, ⟨hac, had⟩, ⟨hbc, hbd⟩⟩

@[simps app] def bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) : ΩLower S X where
  app f := {
    carrier := {b | ∃ a, (a ∈ I.app f) ∧ (b ∈ (F.app _ ⟨f⟩ a).app (𝟙 _))}
    lower' := fun {_ _} h => fun ⟨a, ha, hb⟩ => ⟨a, ha, ((F.app _ ⟨f⟩ a).app _).lower h hb⟩ }
  natural f g b := fun ⟨a, ha, hb⟩ =>
    ⟨R.map g.op a, I.natural f g a ha, (homObj_app_map_mem F g.op ⟨f⟩ a (𝟙 _) _).mpr
      (by simpa using (F.app _ ⟨f⟩ a).natural (𝟙 _) g b hb)⟩
  bottom f := ⟨(⊥ : R.obj (op _)), I.bottom f, (F.app _ ⟨f⟩ (⊥ : R.obj (op _))).bottom _⟩

theorem IsDirected.bind {I : ΩLower R X} (hI : I.IsDirected)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) (hF : ∀ Y f a, (F.app Y f a).IsDirected) :
    (I.bind F).IsDirected := by
  intro Y f a b ⟨a₁, ha₁, ha⟩ ⟨a₂, ha₂, hb⟩
  have ⟨c, hc, h₁, h₂⟩ := hI f ha₁ ha₂
  have ⟨d, hd, had, hbd⟩ := hF (op Y) ⟨f⟩ c (𝟙 Y)
    ((F.app (op Y) ⟨f⟩).hom.monotone h₁ _ _ ha)
    ((F.app (op Y) ⟨f⟩).hom.monotone h₂ _ _ hb)
  exact ⟨d, ⟨c, hc, hd⟩, had, hbd⟩

theorem bind_mono {I I' : ΩLower R X}
    {F F' : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S) (uliftYoneda.{u}.obj X)}
    (hI : I ≤ I') (hF : ∀ Y f a, F.app Y f a ≤ F'.app Y f a) : I.bind F ≤ I'.bind F' :=
  fun {Y} f b ⟨a, ha, hb⟩ => ⟨a, hI f a ha, hF (op Y) ⟨f⟩ a (𝟙 Y) b hb⟩

@[simps! app] def bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : ΩLower T X :=
  (I.pair J).bind F

@[simp] theorem mem_bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (c : T.obj (op Y)) :
    (c ∈ (bind₂ I J F).app f) ↔ ∃ a b, (a ∈ I.app f) ∧ (b ∈ J.app f) ∧
      (c ∈ (F.app (op Y) ⟨f⟩ (a, b)).app (𝟙 Y)) :=
  ⟨fun ⟨(a, b), ⟨ha, hb⟩, hc⟩ => ⟨a, b, ha, hb, hc⟩,
    fun ⟨a, b, ha, hb, hc⟩ => ⟨(a, b), ⟨ha, hb⟩, hc⟩⟩

theorem IsDirected.bind₂ {I : ΩLower R X} {J : ΩLower S X} (hI : I.IsDirected) (hJ : J.IsDirected)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X))
    (hF : ∀ Y f p, (F.app Y f p).IsDirected) : (bind₂ I J F).IsDirected :=
  IsDirected.bind (IsDirected.pair hI hJ) F hF

theorem bind₂_mono {I I' : ΩLower R X} {J J' : ΩLower S X} (hI : I ≤ I') (hJ : J ≤ J')
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : bind₂ I J F ≤ bind₂ I' J' F :=
  bind_mono (show I.pair J ≤ I'.pair J' from fun f (_, _) ⟨ha, hb⟩ => ⟨hI f _ ha, hJ f _ hb⟩)
    fun _ _ _ {_} _ _ h => h

variable (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (S ⋙ forget₂ CondSemilatSup Preord)
    (uliftYoneda.{u}.obj X))

def map (I : ΩLower R X) : ΩLower S X where
  app f := {
    carrier := {b | ∃ a, (a ∈ I.app f) ∧ b ≤ F.app _ ⟨f⟩ a}
    lower' := fun {_ _} h => fun ⟨a, ha, hb⟩ => ⟨a, ha, h.trans hb⟩ }
  natural f g _ := fun ⟨a, ha, hb⟩ => ⟨R.map g.op a, I.natural f g a ha,
    (map_rel (ConcreteCategory.hom (S.map g.op)) hb).trans_eq (F.naturality_apply g.op ⟨f⟩ a).symm⟩
  bottom f := ⟨⊥, I.bottom f, bot_le⟩

@[simp] theorem mem_map (I : ΩLower R X) (f : Y ⟶ X) (b : S.obj (op Y)) :
    (b ∈ (I.map F).app f) ↔ ∃ a, (a ∈ I.app f) ∧ b ≤ F.app (op Y) ⟨f⟩ a := Iff.rfl

theorem IsDirected.map {I : ΩLower R X} (hI : I.IsDirected) : (I.map F).IsDirected := by
  intro Y f _ _ ⟨a, ha, hya⟩ ⟨b, hb, hzb⟩
  have ⟨c, hc, hac, hbc⟩ := hI f ha hb
  exact ⟨_, ⟨c, hc, le_rfl⟩, hya.trans ((F.app _ ⟨f⟩).hom.monotone hac),
    hzb.trans ((F.app _ ⟨f⟩).hom.monotone hbc)⟩

@[simp]
theorem pullback_map (I : ΩLower R X) (f : Y ⟶ X) :
    (I.map F).pullback f = (I.pullback f).map (F.map (uliftYoneda.map f)) :=
  ext fun _ _ => Iff.rfl

theorem map_principal (a : R.obj (op X)) :
    (principal R a).map F = principal S (F.app (op X) ⟨𝟙 X⟩ a) := by
  ext Y f b
  have h : S.map f.op (F.app (op X) ⟨𝟙 X⟩ a) = F.app (op Y) ⟨f⟩ (R.map f.op a) := by
    simpa using (F.naturality_apply f.op ⟨𝟙 X⟩ a).symm
  simpa [h] using ⟨fun ⟨c, hc, hb⟩ => hb.trans ((F.app (op Y) ⟨f⟩).hom.monotone hc),
    fun hb => ⟨_, le_rfl, hb⟩⟩

@[simp] theorem map_map (I : ΩLower R X)
    (G : Functor.HomObj (S ⋙ forget₂ CondSemilatSup Preord)
      (T ⋙ forget₂ CondSemilatSup Preord) (uliftYoneda.{u}.obj X)) :
    (I.map F).map G = I.map (F.comp G) :=
  ext fun f _ => ⟨fun ⟨_, ⟨a, ha, hab⟩, hbc⟩ => ⟨a, ha, hbc.trans ((G.app _ ⟨f⟩).hom.monotone hab)⟩,
    fun ⟨a, ha, hac⟩ => ⟨_, ⟨a, ha, le_rfl⟩, hac⟩⟩

end ΩLower

namespace ΩIdeal

def bind₂ (I : ΩIdeal R X) (J : ΩIdeal S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : ΩIdeal T X where
  val := ΩLower.bind₂ I.val J.val (F.comp (.ofNatTrans (toLowerNatTrans T)))
  property := ΩLower.IsDirected.bind₂ I.property J.property _ fun Y f p => (F.app Y f p).property

@[simp] theorem mem_bind₂ (I : ΩIdeal R X) (J : ΩIdeal S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (c : T.obj (op Y)) :
    (c ∈ (bind₂ I J F).app f) ↔ ∃ a b, (a ∈ I.app f) ∧ (b ∈ J.app f) ∧
      (c ∈ (F.app (op Y) ⟨f⟩ (a, b)).app (𝟙 Y)) :=
  ΩLower.mem_bind₂ _ _ _ f c

end ΩIdeal

end Metalean.Presheaf
