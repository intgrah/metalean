/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Consistency
public import Metalean.TypeTheory.SetModel.False

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory ZFSet NaturalModel

universe u

variable {ζ : Sigs} {E : Env ζ} {Γ : ZFSet.{u}}

theorem con_of_realizer (γ : Γ) (R : Realisation E Ty.{u} Γ) : E.Con :=
  R.con (isEmpty_sect_falseType γ)

end Metalean.TypeTheory.SetModel
