/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Iff
public import Metalean.Typing.Env
import Metalean.Level.Order

@[expose] public section

namespace Metalean.Iff

variable {ζ ζ₁ ζ₂ : Sigs}

@[simp] theorem block_map (pre : ζ₁ ⟶ ζ₂) :
    (@block ζ₁).map pre = @block ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  refine Fin.cases ?_ (fun i => Fin.elim0 i) s
  refine Fin.cases ?_ (fun i => Fin.elim0 i) c
  dsimp [Ctor.map, Field.map]
  congr
  · funext f
    refine Fin.cases ?_ (fun f => ?_) f
    · simp [Expr.map]
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) f
      simp [Expr.map]
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

theorem wf (E : Env ζ) : block.WFStrong E :=
  ⟨.snoc (.snoc .nil ⟨_, trivial, .sortDF⟩) ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun _ _ => {
      ordinary
        | ⟨0, _⟩ =>
          ⟨by
              refine .defeqDF (l := .succ .zero) ?_ (.forallEDF (.var .sortDF) (.var .sortDF) (.var .sortDF))
              rw [Level.imax_zero]
              exact .sortDF,
            Inductive.levelOK_of_zero _ rfl⟩
        | ⟨1, _⟩ =>
          ⟨by
              refine .defeqDF (l := .succ .zero) ?_ (.forallEDF (.var .sortDF) (.var .sortDF) (.var .sortDF))
              rw [Level.imax_zero]
              exact .sortDF,
            Inductive.levelOK_of_zero _ rfl⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

end Metalean.Iff
