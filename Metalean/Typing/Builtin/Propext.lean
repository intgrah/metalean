/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Propext
public import Metalean.Typing.Defs

@[expose] public section

namespace Metalean.Propext

theorem isType : Quot.Sound.env[.nil] ⊢ type typ := by
  refine ⟨.imax .one (.imax .one (.imax .zero .zero)), ?_⟩
  unfold type
  apply Defeq.forallEDF (l₂ := .imax .one (.imax .zero .zero)) .sortDF <;>
    apply Defeq.forallEDF (l₂ := .imax .zero .zero) .sortDF
  all_goals
    apply Defeq.forallEDF (l₂ := .zero)
      (.indDF (η := iffHead) (s := ⟨0, by decide⟩)
        (fun
          | ⟨0, _⟩ => .var .sortDF
          | ⟨1, _⟩ => .var .sortDF)
        fun index => Fin.elim0 index)
    all_goals
      exact .indDF (η := eqHead) (s := ⟨0, by decide⟩)
        (fun
          | ⟨0, _⟩ => .sortDF
          | ⟨1, _⟩ => .var .sortDF)
        fun ⟨0, _⟩ => .var .sortDF

end Metalean.Propext
