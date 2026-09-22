/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Nonempty
public import Metalean.Typing.Env

@[expose] public section

namespace Metalean.Nonempty

variable {ζ ζ₁ ζ₂ : Sigs}

@[simp] theorem block_map (pre : ζ₁ ⟶ ζ₂) :
    (@block ζ₁).map pre = @block ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  refine Fin.cases ?_ (fun i => Fin.elim0 i) s
  refine Fin.cases ?_ (fun i => Fin.elim0 i) c
  dsimp [Ctor.map]
  congr <;> exact Subsingleton.elim _ _

theorem wf (E : Env ζ) : block.WFStrong E :=
  ⟨.snoc .nil ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun ⟨0, _⟩ ⟨0, _⟩ => {
      ordinary
        | ⟨0, _⟩ =>
          ⟨.var .sortDF, Inductive.levelOK_of_zero block rfl⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

end Metalean.Nonempty
