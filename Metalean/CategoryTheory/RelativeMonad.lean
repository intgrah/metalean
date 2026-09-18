/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Functor.Category

@[expose] public section

namespace CategoryTheory

variable {C : Type*} {D : Type*} [Category* C] [Category* D]

structure RelativeMonad (J : C ⥤ D) where
  obj : C → D
  unit (X : C) : J.obj X ⟶ obj X
  bind {X Y : C} (f : J.obj X ⟶ obj Y) : obj X ⟶ obj Y
  unit_bind {X Y : C} (f : J.obj X ⟶ obj Y) : unit X ≫ bind f = f
  bind_unit (X : C) : bind (unit X) = 𝟙 (obj X)
  bind_bind {X₁ X₂ X₃ : C} (f₁ : J.obj X₁ ⟶ obj X₂)
    (f₂ : J.obj X₂ ⟶ obj X₃) :
    bind f₁ ≫ bind f₂ = bind (f₁ ≫ bind f₂)

namespace RelativeMonad

variable {J : C ⥤ D}

structure Kleisli (T : RelativeMonad J) where
  of : C

@[ext] structure Kleisli.Hom {T : RelativeMonad J} (X Y : Kleisli T) where
  of : J.obj X.of ⟶ T.obj Y.of

instance (T : RelativeMonad J) : Category (Kleisli T) where
  Hom := Kleisli.Hom
  id X := ⟨T.unit X.of⟩
  comp f₁ f₂ := ⟨f₁.of ≫ T.bind f₂.of⟩
  id_comp f := Kleisli.Hom.ext (T.unit_bind f.of)
  comp_id f := by simp [T.bind_unit]
  assoc f₁ f₂ f₃ := by simp [T.bind_bind]

@[reducible] def lift (T : RelativeMonad J) : C ⥤ Kleisli T where
  obj X := ⟨X⟩
  map {_ Y} f := ⟨J.map f ≫ T.unit Y⟩
  map_id X :=
    Kleisli.Hom.ext ((congrArg (· ≫ T.unit X) (J.map_id X)).trans (Category.id_comp _))
  map_comp {_ _ X₃} f₁ f₂ :=
    Kleisli.Hom.ext ((congrArg (· ≫ T.unit X₃) (J.map_comp f₁ f₂)).trans
      ((Category.assoc ..).trans
        ((congrArg (J.map f₁ ≫ ·) (T.unit_bind _).symm).trans (Category.assoc ..).symm)))

@[reducible] def extension (T : RelativeMonad J) : Kleisli T ⥤ D where
  obj X := T.obj X.of
  map f := T.bind f.of
  map_id X := T.bind_unit X.of
  map_comp f₁ f₂ := (T.bind_bind f₁.of f₂.of).symm

abbrev functor (T : RelativeMonad J) : C ⥤ D := T.lift ⋙ T.extension

@[reducible] def η (T : RelativeMonad J) : J ⟶ T.functor where
  app X := T.unit X
  naturality _ Y f := (T.unit_bind (J.map f ≫ T.unit Y)).symm

@[ext] structure Hom (T₁ T₂ : RelativeMonad J) where
  app (X : C) : T₁.obj X ⟶ T₂.obj X
  unit_app (X : C) : T₁.unit X ≫ app X = T₂.unit X
  bind_app {X Y : C} (f : J.obj X ⟶ T₁.obj Y) :
    T₁.bind f ≫ app Y = app X ≫ T₂.bind (f ≫ app Y)

instance : Category (RelativeMonad J) where
  Hom := Hom
  id T :=
    { app X := 𝟙 (T.obj X)
      unit_app X := Category.comp_id _
      bind_app f := by simp }
  comp α₁ α₂ :=
    { app X := α₁.app X ≫ α₂.app X
      unit_app X := by rw [← Category.assoc, α₁.unit_app, α₂.unit_app]
      bind_app f := by
        rw [← Category.assoc, α₁.bind_app, Category.assoc, α₂.bind_app,
          Category.assoc, Category.assoc] }
  id_comp α := by simp
  comp_id α := by simp
  assoc α₁ α₂ α₃ := by simp

@[ext] theorem hom_ext {T₁ T₂ : RelativeMonad J} {α₁ α₂ : T₁ ⟶ T₂}
    (h : ∀ X, α₁.app X = α₂.app X) : α₁ = α₂ :=
  Hom.ext (funext h)

@[reducible] def Hom.toNatTrans {T₁ T₂ : RelativeMonad J} (α : T₁ ⟶ T₂) :
    T₁.functor ⟶ T₂.functor where
  app := α.app
  naturality {X Y} f :=
    (α.bind_app _).trans
      (congrArg (fun g => α.app X ≫ T₂.bind g)
        ((Category.assoc ..).trans (congrArg (J.map f ≫ ·) (α.unit_app Y))))

@[reducible] def forget : RelativeMonad J ⥤ C ⥤ D where
  obj T := T.functor
  map α := α.toNatTrans

@[reducible] def Hom.kleisli {T₁ T₂ : RelativeMonad J} (α : T₁ ⟶ T₂) :
    T₁.Kleisli ⥤ T₂.Kleisli where
  obj X := ⟨X.of⟩
  map {_ Y} f := ⟨f.of ≫ α.app Y.of⟩
  map_id X := Kleisli.Hom.ext (α.unit_app X.of)
  map_comp f₁ f₂ :=
    Kleisli.Hom.ext ((Category.assoc ..).trans
      ((congrArg (f₁.of ≫ ·) (α.bind_app f₂.of)).trans (Category.assoc ..).symm))

end RelativeMonad

end CategoryTheory
