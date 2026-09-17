/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.Order.Category.Preord

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace Preord

def terminalLimitCone : LimitCone (Functor.empty Preord.{u}) :=
  ⟨_, IsTerminal.ofUniqueHom (fun X => ofHom (OrderHom.const X PUnit.unit))
    fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

def binaryProductLimitCone (X Y : Preord.{u}) : LimitCone (pair X Y) :=
  ⟨BinaryFan.mk (ofHom (OrderHom.fst : X × Y →o X)) (ofHom (OrderHom.snd : X × Y →o Y)),
    BinaryFan.IsLimit.mk _ (fun f g => ofHom (f.hom.prod g.hom))
      (fun _ _ => rfl) (fun _ _ => rfl)
      fun _ _ _ hf hg => ext fun x => Prod.ext
        (ConcreteCategory.congr_hom hf x) (ConcreteCategory.congr_hom hg x)⟩

instance : CartesianMonoidalCategory Preord.{u} :=
  .ofChosenFiniteProducts terminalLimitCone binaryProductLimitCone

instance : BraidedCategory Preord.{u} := .ofCartesianMonoidalCategory

@[simp] theorem tensor_apply {W X Y Z : Preord.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : W × Y) :
    (f ⊗ₘ g) p = (f p.1, g p.2) := rfl

end Preord
