/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Choice
public import Metalean.Strong.Defs

@[expose] public section

namespace Metalean.Choice

theorem isType : Propext.env[.nil] ⊢ₛ type typ :=
  ⟨_, .forallEDF .sortDF
    (.forallEDF
      (.indDF (η := nonemptyHead) (s := ⟨0, by decide⟩)
        (fun ⟨0, _⟩ => .var .sortDF)
        fun i => Fin.elim0 i)
      (.var .sortDF) (.var .sortDF))
    (.forallEDF
      (.indDF (η := nonemptyHead) (s := ⟨0, by decide⟩)
        (fun ⟨0, _⟩ => .var .sortDF)
        fun i => Fin.elim0 i)
      (.var .sortDF) (.var .sortDF))⟩

end Metalean.Choice
