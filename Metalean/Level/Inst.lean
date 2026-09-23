/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Metalean

universe u v w v'

class InstLevel (σ : Type u) (α : Type v) (β : outParam (Type w)) where
  inst : σ → α → β

namespace InstLevel

macro:max a:term noWs "{" ls:term "}" : term => `(inst $ls $a)

variable {σ : Type u} {α : Type v} {α' : Type v'}

instance {n : Nat} [InstLevel σ α α'] :
    InstLevel σ (Fin n → α) (Fin n → α') where
  inst ls a i := inst ls (a i)

end InstLevel

end Metalean
