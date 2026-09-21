/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Ideal
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

@[simp↓] theorem presheaf_map_eq_pullback {X Y : Cᵒᵖ} (g : X ⟶ Y) (I : ΩIdeal R X.unop) :
    (presheaf R).map g I = I.pullback g.unop := rfl

@[simp] theorem pullback_id (I : ΩIdeal R X) : I.pullback (𝟙 X) = I :=
  (presheaf R).map_id_apply _ I

@[simp] theorem pullback_pullback (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (I.pullback f).pullback g = I.pullback (g ≫ f) :=
  ((presheaf R).map_comp_apply f.op g.op I).symm

theorem pullback_mono {I J : ΩIdeal R X} (h : I ≤ J) (f : Y ⟶ X) : I.pullback f ≤ J.pullback f :=
  ((presheaf R).map f.op).hom.monotone h

@[simp]
theorem val_presheaf_map (I : ΩIdeal R X) (f : Y ⟶ X) :
    (I.pullback f).val = I.val.pullback f := rfl

abbrev mem (I : ΩIdeal R X) (f : Y ⟶ X) (a : R.obj (op Y)) := I.val.mem f a

theorem bottom (I : ΩIdeal R X) (f : Y ⟶ X) : I.mem f ⊥ := I.val.bottom f

theorem lower (I : ΩIdeal R X) (f : Y ⟶ X) {a b : R.obj (op Y)}
    (h : a ≤ b) : I.mem f b → I.mem f a := I.val.lower f h

theorem natural (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Y)) :
    I.mem f a → I.mem (g ≫ f) (R.map g.op a) := I.val.natural f g a

@[simp]
theorem val_mem (I : ΩIdeal R X) (f : Y ⟶ X) (a : R.obj (op Y)) :
    I.val.mem f a ↔ I.mem f a := Iff.rfl

@[ext]
theorem ext {I J : ΩIdeal R X}
    (h : ∀ {Y : C} (f : Y ⟶ X) (a : R.obj (op Y)),
      I.mem f a ↔ J.mem f a) : I = J :=
  Subtype.val_injective (ΩLower.ext h)

instance : OrderBot (ΩIdeal R X) where
  bot := ⟨⊥, ΩLower.isDirected_bot⟩
  bot_le I := @bot_le (ΩLower R X) _ _ I.val

@[simp]
theorem mem_bot (f : Y ⟶ X) (a : R.obj (op Y)) :
    (⊥ : ΩIdeal R X).mem f a ↔ a ≤ ⊥ := ΩLower.mem_bot f a

@[simp↓] theorem presheaf_map_mem (I : ΩIdeal R X) (f : Y ⟶ X) (g : Z ⟶ Y) (a : R.obj (op Z)) :
    (I.pullback f).mem g a ↔ I.mem (g ≫ f) a := Iff.rfl

@[simp↓] theorem presheaf_map_mem_id (I : ΩIdeal R X) (f : Y ⟶ X)
    (a : R.obj (op Y)) :
    (I.pullback f).mem (𝟙 Y) a ↔ I.mem f a := by simp

@[simp] theorem pullback_bot (f : Y ⟶ X) : (⊥ : ΩIdeal R X).pullback f = ⊥ :=
  ext fun g a => by simp

def principal (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) (x : R.obj (op X)) : ΩIdeal R X where
  val := ΩLower.principal R x
  property := ΩLower.isDirected_principal x

@[simp] theorem mem_principal (x : R.obj (op X)) (f : Y ⟶ X) (a : R.obj (op Y)) :
    (principal R x).mem f a ↔ a ≤ R.map f.op x := ΩLower.mem_principal x f a

@[simp]
theorem principal_bottom : principal R (⊥ : R.obj (op X)) = ⊥ :=
  Subtype.val_injective ΩLower.principal_bottom

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

@[simp]
theorem val_toIdeal (L : ΩLower R X) (hL : L.IsDirected) :
    (L.toIdeal hL).val = L := rfl

def pair (I : ΩLower R X) (J : ΩLower S X) : ΩLower (R ⊗ S) X where
  mem f := fun (a, b) => I.mem f a ∧ J.mem f b
  natural f g := fun (a, b) ⟨ha, hb⟩ => ⟨I.natural f g a ha, J.natural f g b hb⟩
  bottom f := ⟨I.bottom f, J.bottom f⟩
  lower f := fun ⟨ha, hb⟩ ⟨ha', hb'⟩ => ⟨I.lower f ha ha', J.lower f hb hb'⟩

theorem IsDirected.pair {I : ΩLower R X} {J : ΩLower S X}
    (hI : I.IsDirected) (hJ : J.IsDirected) : (I.pair J).IsDirected := by
  intro Y f a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
  have ⟨c, hc, hac, hbc⟩ := hI f ha₁ hb₁
  have ⟨d, hd, had, hbd⟩ := hJ f ha₂ hb₂
  exact ⟨(c, d), ⟨hc, hd⟩, ⟨hac, had⟩, ⟨hbc, hbd⟩⟩

def bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) : ΩLower S X where
  mem f b := ∃ a, I.mem f a ∧ (F.app _ ⟨f⟩ a).mem (𝟙 _) b
  natural f g b := fun ⟨a, ha, hb⟩ =>
    ⟨R.map g.op a, I.natural f g a ha, (homObj_app_map_mem F g.op ⟨f⟩ a (𝟙 _) _).mpr
      (by simpa using (F.app _ ⟨f⟩ a).natural (𝟙 _) g b hb)⟩
  bottom f := ⟨(⊥ : R.obj (op _)), I.bottom f, (F.app _ ⟨f⟩ (⊥ : R.obj (op _))).bottom _⟩
  lower f h := fun ⟨a, ha, hb⟩ => ⟨a, ha, (F.app _ ⟨f⟩ a).lower _ h hb⟩

@[simp] theorem mem_bind (I : ΩLower R X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord) (presheaf S)
      (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (b : S.obj (op Y)) :
    (I.bind F).mem f b ↔ ∃ a, I.mem f a ∧ (F.app (op Y) ⟨f⟩ a).mem (𝟙 Y) b := Iff.rfl

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

def bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) : ΩLower T X :=
  (I.pair J).bind F

@[simp] theorem mem_bind₂ (I : ΩLower R X) (J : ΩLower S X)
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X)) (f : Y ⟶ X) (c : T.obj (op Y)) :
    (bind₂ I J F).mem f c ↔ ∃ a b, I.mem f a ∧ J.mem f b ∧
      (F.app (op Y) ⟨f⟩ (a, b)).mem (𝟙 Y) c :=
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
  mem f b := ∃ a, I.mem f a ∧ b ≤ F.app _ ⟨f⟩ a
  natural f g _ := fun ⟨a, ha, hb⟩ => ⟨R.map g.op a, I.natural f g a ha,
    (map_rel (ConcreteCategory.hom (S.map g.op)) hb).trans_eq (F.naturality_apply g.op ⟨f⟩ a).symm⟩
  bottom f := ⟨⊥, I.bottom f, bot_le⟩
  lower _ h := fun ⟨a, ha, hb⟩ => ⟨a, ha, h.trans hb⟩

@[simp] theorem mem_map (I : ΩLower R X) (f : Y ⟶ X) (b : S.obj (op Y)) :
    (I.map F).mem f b ↔ ∃ a, I.mem f a ∧ b ≤ F.app (op Y) ⟨f⟩ a := Iff.rfl

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
    (bind₂ I J F).mem f c ↔ ∃ a b, I.mem f a ∧ J.mem f b ∧
      (F.app (op Y) ⟨f⟩ (a, b)).mem (𝟙 Y) c :=
  ΩLower.mem_bind₂ _ _ _ f c

end ΩIdeal

end Metalean.Presheaf
