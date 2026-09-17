/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Propext
public import Metalean.Typing.Defeq

@[expose] public section

namespace Metalean.Propext

theorem isType : Quot.Sound.env[.nil] ⊢ type typ :=
  ⟨_, .forallEDF .sortDF
    (.forallEDF .sortDF
      (.forallEDF
        (.indDF (η := iffHead) (s := ⟨0, by decide⟩)
          (fun
            | ⟨0, _⟩ => .var
            | ⟨1, _⟩ => .var)
          fun index => Fin.elim0 index)
        (.indDF (η := eqHead) (s := ⟨0, by decide⟩)
          (fun
            | ⟨0, _⟩ => .sortDF
            | ⟨1, _⟩ => .var)
          fun ⟨0, _⟩ => .var)))⟩

end Metalean.Propext
