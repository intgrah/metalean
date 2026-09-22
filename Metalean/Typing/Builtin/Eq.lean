/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env.Defs
public import Metalean.Syntax.Eq

/-! # Well-formedness of the equality declaration -/

@[expose] public section

namespace Metalean.Eq

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

theorem wf (E : Env ζ) : InductiveWF E block where
  params := .snoc
    (.snoc .nil ⟨_, trivial, .sortDF⟩)
    ⟨_, trivial, .var .sortDF⟩
  indices | ⟨0, _⟩ => .snoc .nil ⟨_, trivial, .var .sortDF⟩
  ctors | ⟨0, _⟩, ⟨0, _⟩ => {
    ordinary f := Fin.elim0 f
    recursive f := Fin.elim0 f
    targetIndices | ⟨0, _⟩ => .var (.var .sortDF)
  }

end Metalean.Eq
