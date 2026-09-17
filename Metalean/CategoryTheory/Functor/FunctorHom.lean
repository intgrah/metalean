/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Functor.FunctorHom
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

@[expose] public section

universe u v w w' t

namespace CategoryTheory.Functor

open MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
  {F G H : C ⥤ D} {A : C ⥤ Type t}

/-- Internal hom -/
@[implicit_reducible] def HomObj.functor (F G : C ⥤ D) : C ⥤ Type (max w' v u) where
  obj X := HomObj F G (coyoneda.obj (Opposite.op X))
  map f := ↾HomObj.map (coyoneda.map f.op)
  map_id X := by ext; simp
  map_comp f g := by ext; simp

@[simp] theorem HomObj.functor_map_app (F G : C ⥤ D) {X Y Z : C}
    (f : X ⟶ Y) (x : (HomObj.functor F G).obj X) (g : Y ⟶ Z) :
    (x.map (coyoneda.map f.op)).app Z g = x.app Z (f ≫ g) := rfl

section Concrete

variable {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]

@[ext] theorem HomObj.ext_app {α β : HomObj F G A}
    (h : ∀ X a x, α.app X a x = β.app X a x) : α = β :=
  HomObj.ext <| funext₂ fun X a => ConcreteCategory.hom_ext _ _ (h X a)

@[simp] theorem HomObj.naturality_apply (α : HomObj F G A)
    {X Y : C} (f : X ⟶ Y) (a : A.obj X) (x : ToType (F.obj X)) :
    α.app Y (A.map f a) (F.map f x) = G.map f (α.app X a x) := by
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (α.naturality f a) x

end Concrete

namespace HomObj

variable [CartesianMonoidalCategory D]

def fst : HomObj (F ⊗ G) F A := .ofNatTrans (CartesianMonoidalCategory.fst F G)

def snd : HomObj (F ⊗ G) G A := .ofNatTrans (CartesianMonoidalCategory.snd F G)

def pair (f : HomObj F G A) (g : HomObj F H A) : HomObj F (G ⊗ H) A where
  app X a := CartesianMonoidalCategory.lift (f.app X a) (g.app X a)
  naturality h a := by apply CartesianMonoidalCategory.hom_ext <;> simp

end HomObj

end CategoryTheory.Functor
