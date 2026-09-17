/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Choice
public import Metalean.Typing.Defeq

@[expose] public section

namespace Metalean.Choice

theorem isType : Propext.env[.nil] ⊢ type typ :=
  ⟨_, .forallEDF .sortDF
    (.forallEDF
      (.indDF (η := nonemptyHead) (s := ⟨0, by decide⟩)
        (fun ⟨0, _⟩ => .var)
        fun index => Fin.elim0 index)
      .var)⟩

end Metalean.Choice
