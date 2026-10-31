/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Order.Hom.Order
public import Metalean.CategoryTheory.Functor.FunctorHom
public import Metalean.Order.Category.Preord.Cartesian

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

abbrev Functor.toPreord (F : C ⥤ Type w) [order : ∀ X, Preorder (F.obj X)]
    (hF : ∀ {X Y} (f : X ⟶ Y), Monotone (F.map f)) : C ⥤ Preord.{w} where
  obj X := Preord.of (F.obj X)
  map f := Preord.ofHom ⟨F.map f, hF f⟩
  map_id X := Preord.ext (F.map_id_apply X)
  map_comp f g := Preord.ext (F.map_comp_apply f g)

abbrev Subfunctor.toPreord {F : C ⥤ Preord.{w}}
    (S : Subfunctor (F ⋙ forget Preord)) : C ⥤ Preord.{w} where
  __ := S.toFunctor.toPreord (order := fun X => inferInstanceAs (Preorder {x : F.obj X // x ∈ S.obj X}))
    fun f _ _ h => OrderHom.monotone (Preord.Hom.hom (F.map f)) h
  obj X := Preord.of {x : F.obj X // x ∈ S.obj X}

namespace Functor

open MonoidalCategory Opposite

variable {F G : C ⥤ Preord.{w}} {A : C ⥤ Type v}

instance HomObj.instPreorder : Preorder (HomObj F G A) :=
  Preorder.lift fun α : HomObj F G A => fun X a x => α.app X a x

instance HomObj.instPartialOrder [∀ X, PartialOrder (G.obj X)] : PartialOrder (HomObj F G A) :=
  PartialOrder.lift (fun α : HomObj F G A => fun X a x => α.app X a x)
    fun _ _ h => HomObj.ext_app fun X a x => congr($h X a x)

section CompleteLattice

variable {G : C ⥤ Type w} [lattice : ∀ X, CompleteLattice (G.obj X)]

abbrev HomObj.completeLattice (hm : ∀ {X Y} (f : X ⟶ Y), Monotone (G.map f))
    (hG : ∀ {X Y} (f : X ⟶ Y) (S : Set (G.obj X)),
      G.map f (sSup S) = sSup (G.map f '' S)) : CompleteLattice (HomObj F (G.toPreord hm) A) :=
  letI : SupSet (HomObj F (G.toPreord hm) A) := ⟨fun S => {
    app X a := Preord.ofHom (⨆ α ∈ S, (α.app X a).hom)
    naturality {X Y} f a := Preord.ext fun x => by
      change (⨆ α ∈ S, (α.app Y (A.map f a)).hom) (F.map f x) =
        G.map f ((⨆ α ∈ S, (α.app X a).hom) x)
      simp only [OrderHom.iSup_apply]
      calc
        _ = ⨆ α ∈ S, G.map f (α.app X a x) := biSup_congr fun α _ => α.naturality_apply f a x
        _ = _ := by
          simpa only [sSup_image, iSup_image] using
            (hG f ((fun α : HomObj F (G.toPreord hm) A => α.app X a x) '' S)).symm }⟩
  { bot := {
      app X _ := Preord.ofHom (OrderHom.const _ ⊥)
      naturality f _ := Preord.ext fun _ => by simpa using (hG f ∅).symm }
    bot_le _ := fun X a x => bot_le
    __ := completeLatticeOfSup (HomObj F (G.toPreord hm) A) fun S => by
      constructor
      · intro α hα X a
        change (α.app X a).hom ≤ ⨆ β ∈ S, (β.app X a).hom
        exact le_iSup₂_of_le α hα le_rfl
      · intro α h X a
        change (⨆ β ∈ S, (β.app X a).hom) ≤ (α.app X a).hom
        exact iSup₂_le fun β hβ => h hβ X a }

end CompleteLattice

abbrev parameterizedHom (F G : C ⥤ Preord.{w})
    (A : C ⥤ Type v) : C ⥤ Preord.{max u v w} where
  __ := (coyoneda.rightOp ⋙ (tensorRight A).op ⋙ homObjFunctor F G).toPreord
    (order := fun _ => HomObj.instPreorder)
    (by intro X Y f α β h Z ⟨g, a⟩ x; exact h Z (f ≫ g, a) x)
  obj X := Preord.of (HomObj F G (dsimp% [Monoidal.FunctorCategory.tensorObj, types_tensorObj_def]
    Monoidal.FunctorCategory.tensorObj (coyoneda.obj (op X)) A))

namespace HomObj

variable {F G H : C ⥤ Preord.{max u v w}} {A B : C ⥤ Type v}

set_option backward.isDefEq.respectTransparency false in
def curry (f : HomObj (F ⊗ G) H (B ⊗ A)) : HomObj F (parameterizedHom G H A) B where
  app X b := Preord.ofHom {
    toFun x := {
      app Y p := Preord.ofHom {
        toFun y := f.app Y (B.map p.1 b, p.2) (F.map p.1 x, y)
        monotone' _ _ h := (f.app Y (B.map p.1 b, p.2)).hom.monotone ⟨le_rfl, h⟩ }
      naturality g p := Preord.ext fun y => by
        change f.app _ (B.map (p.1 ≫ g) b, A.map g p.2) (F.map (p.1 ≫ g) x, G.map g y) = _
        have h := f.naturality_apply g (B.map p.1 b, p.2) (F.map p.1 x, y)
        change f.app _ (B.map g (B.map p.1 b), A.map g p.2)
          (F.map g (F.map p.1 x), G.map g y) = _ at h
        simp only [map_comp_apply]
        exact h }
    monotone' _ _ h := fun Y p y =>
      (f.app Y (B.map p.1 b, p.2)).hom.monotone ⟨(F.map p.1).hom.monotone h, le_rfl⟩ }
  naturality {X Y} g b := Preord.ext fun x => by
    refine HomObj.ext_app (F := G) (G := H) fun Z (p : (Y ⟶ Z) × A.obj Z) y => ?_
    change f.app Z (B.map p.1 (B.map g b), p.2) (F.map p.1 (F.map g x), y) =
      f.app Z (B.map (g ≫ p.1) b, p.2) (F.map (g ≫ p.1) x, y)
    simp

set_option backward.isDefEq.respectTransparency false in
def uncurry (f : HomObj F (parameterizedHom G H A) B) : HomObj (F ⊗ G) H (B ⊗ A) where
  app X p := Preord.ofHom {
    toFun x := (f.app X p.1 x.1).app X (𝟙 X, p.2) x.2
    monotone' _ _ h := OrderHom.apply_mono
      ((f.app X p.1).hom.monotone h.1 X (𝟙 X, p.2)) h.2 }
  naturality g p := Preord.ext fun x => by
    have h := f.naturality_apply g p.1 x.1
    have h' := (f.app _ p.1 x.1).naturality_apply g (𝟙 _, p.2) x.2
    change ((f.app _ (B.map g p.1) (F.map g x.1)).app _ (𝟙 _, A.map g p.2)) (G.map g x.2) = _
    rw [h]
    change (f.app _ p.1 x.1).app _ (g ≫ 𝟙 _, A.map g p.2) (G.map g x.2) =
      H.map g ((f.app _ p.1 x.1).app _ (𝟙 _, p.2) x.2)
    change (f.app _ p.1 x.1).app _ (𝟙 _ ≫ g, A.map g p.2) (G.map g x.2) = _ at h'
    simpa only [Category.comp_id, Category.id_comp] using h'

@[simp] theorem uncurry_curry (f : HomObj (F ⊗ G) H (B ⊗ A)) : f.curry.uncurry = f := by
  apply HomObj.ext_app
  intro X p x
  change f.app X (B.map (𝟙 X) p.1, p.2) (F.map (𝟙 X) x.1, x.2) = f.app X p x
  simp only [map_id_apply]
  rfl

@[simp] theorem curry_uncurry (f : HomObj F (parameterizedHom G H A) B) : f.uncurry.curry = f := by
  apply HomObj.ext_app
  intro X b x
  apply HomObj.ext_app
  intro Y p y
  change (f.app Y (B.map p.1 b) (F.map p.1 x)).app Y (𝟙 Y, p.2) y = (f.app X b x).app Y p y
  rw [f.naturality_apply]
  change (f.app X b x).app Y (p.1 ≫ 𝟙 Y, p.2) y = (f.app X b x).app Y p y
  simp

end HomObj

end Functor

instance NatTrans.instPartialOrder {F G : C ⥤ Preord.{w}} [∀ X, PartialOrder (G.obj X)] :
    PartialOrder (F ⟶ G) :=
  PartialOrder.lift (fun α : F ⟶ G => fun X x => α.app X x)
    fun α β h => by ext X x; exact congr($h X x)

end CategoryTheory
