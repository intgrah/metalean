/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.QuotSound
public import Metalean.Typing.Defeq

@[expose] public section

namespace Metalean.Quot.Sound

theorem isType : Nonempty.env[.nil] ⊢ type typ :=
  ⟨_, .forallEDF .sortDF
    (.forallEDF (.forallEDF .var (.forallEDF .var .sortDF))
      (.forallEDF .var
        (.forallEDF .var
          (.forallEDF
            (.appDF (t' := (.prop : Expr Nonempty.sigs 1 5))
              (.appDF (t' := (.forallE #0 .prop : Expr Nonempty.sigs 1 5)) .var .var) .var)
            (.indDF (η := eqHead) (s := ⟨0, by decide⟩)
              (fun
                | ⟨0, _⟩ => .quotDF .var .var
                | ⟨1, _⟩ => .quotMkDF .var .var .var)
              fun ⟨0, _⟩ => by exact .quotMkDF .var .var .var)))))⟩

end Metalean.Quot.Sound
