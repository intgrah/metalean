/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Morphism
public import Metalean.TypeTheory.Syntactic.Pi.Structure
public import Metalean.TypeTheory.Syntactic.Sort

@[expose] public noncomputable section

namespace Metalean.TypeTheory

open CategoryTheory NaturalModel

universe u v

variable {ℓ : Nat} {D : Type v} [SmallCategory D] {Ty' Tm' : Dᵒᵖ ⥤ Type v}
  [NaturalModel Ty' Tm'] [HasSorts Ty' Tm' ℓ] [HasPi Ty' Tm']

theorem initiality :
    ∃! F : Morphism (Ty (Env.nil) ℓ) Ty', F.PreservesSorts (ℓ := ℓ) ∧ F.PreservesPi :=
  sorry

end Metalean.TypeTheory
