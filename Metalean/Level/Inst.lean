/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Metalean

universe u v w

class InstLevel (σ : Type u) (α : Type v) (β : outParam (Type w)) where
  inst : σ → α → β

namespace InstLevel

macro:max a:term noWs "{" ls:term "}" : term => `(inst $ls $a)

variable {σ : Type u} {α : Type v} {β : Type w}

instance {n : Nat} [InstLevel σ α β] :
    InstLevel σ (Fin n → α) (Fin n → β) where
  inst ls a i := inst ls (a i)

theorem inst_tuple {n : Nat} [InstLevel σ α β]
    (ls : σ) (a : Fin n → α) : a{ls} = fun i => (a i){ls} := rfl

@[simp] theorem inst_apply {n : Nat} [InstLevel σ α β]
    (ls : σ) (a : Fin n → α) (i : Fin n) : a{ls} i = (a i){ls} := rfl

instance [InstLevel σ α β] : InstLevel σ (List α) (List β) where
  inst ls xs := xs.map (·{ls})

instance [InstLevel σ α β] : InstLevel σ (Array α) (Array β) where
  inst ls xs := xs.map (·{ls})

@[simp] theorem inst_array_size [InstLevel σ α β]
    (ls : σ) (xs : Array α) : xs{ls}.size = xs.size := Array.size_map

@[simp] theorem inst_array_getElem [InstLevel σ α β]
    (ls : σ) (xs : Array α) (i : Nat) (hi : i < xs{ls}.size) :
    xs{ls}[i] = (xs[i]'(by simpa using hi)){ls} :=
  Array.getElem_map (fun x => x{ls}) hi

end InstLevel

end Metalean
