/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Metalean.Order.Category.CondSemilatSup.Basic

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CondSemilatSup

def terminalLimitCone : LimitCone (Functor.empty CondSemilatSup.{u}) :=
  ⟨_, IsTerminal.ofUniqueHom (fun X => ofHom {
    __ := OrderHom.const X PUnit.unit
    map_bot' := rfl
    map_cSup' _ _ _ {_} _ _ := trivial }) fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

def binaryProductLimitCone (X Y : CondSemilatSup.{u}) : LimitCone (pair X Y) :=
  ⟨BinaryFan.mk
    (ofHom { __ := (OrderHom.fst : X × Y →o X), map_bot' := rfl, map_cSup' _ _ _ := cSup_le _ })
    (ofHom { __ := (OrderHom.snd : X × Y →o Y), map_bot' := rfl, map_cSup' _ _ _ := cSup_le _ }),
    BinaryFan.IsLimit.mk _ (fun f g => ofHom {
      __ := f.toOrderHom.prod g.toOrderHom
      map_bot' := Prod.ext f.map_bot' g.map_bot'
      map_cSup' a b h {_} ha hb :=
        ⟨map_cSup_le (ConcreteCategory.hom f) a b h ha.1 hb.1,
          map_cSup_le (ConcreteCategory.hom g) a b h ha.2 hb.2⟩ })
      (fun _ _ => rfl) (fun _ _ => rfl)
      fun _ _ _ hf hg => ext fun x => Prod.ext
        (ConcreteCategory.congr_hom hf x) (ConcreteCategory.congr_hom hg x)⟩

instance : CartesianMonoidalCategory CondSemilatSup.{u} :=
  .ofChosenFiniteProducts terminalLimitCone binaryProductLimitCone

instance : BraidedCategory CondSemilatSup.{u} := .ofCartesianMonoidalCategory

@[simp] theorem tensor_apply {W X Y Z : CondSemilatSup.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : W × Y) :
    (f ⊗ₘ g) p = (f p.1, g p.2) := rfl

end CondSemilatSup
