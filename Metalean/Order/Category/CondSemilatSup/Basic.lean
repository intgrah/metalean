/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.Order.Category.Preord
public import Metalean.Order.Hom.CondLattice

@[expose] public section

universe u

open CategoryTheory

structure CondSemilatSup where
  of ::
  carrier : Type u
  [str : CondSemilatticeSup carrier]

attribute [instance] CondSemilatSup.str

namespace CondSemilatSup

instance : CoeSort CondSemilatSup (Type u) := ⟨carrier⟩

instance : Category CondSemilatSup where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := g.comp f

instance : ConcreteCategory CondSemilatSup (Hom · ·) where
  hom f := f
  ofHom f := f

abbrev ofHom {α β : Type u} [CondSemilatticeSup α] [CondSemilatticeSup β] (f : Hom α β) :
    of α ⟶ of β := f

@[ext] theorem ext {X Y : CondSemilatSup} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ h

instance : HasForget₂ CondSemilatSup Preord where
  forget₂.obj X := Preord.of X
  forget₂.map f := Preord.ofHom f.toOrderHom

@[simp] theorem forget₂_map_apply {X Y : CondSemilatSup} (f : X ⟶ Y) (a : X) :
    ((forget₂ CondSemilatSup Preord).map f).hom a = f a := rfl

end CondSemilatSup
