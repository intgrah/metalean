/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Propext

/-! # The `Classical.choice` axiom -/

@[expose] public section

namespace Metalean

namespace Choice

abbrev nonemptyHead : Head Propext.sigs (.inductive Nonempty.sig) := .there (.there .here)

/-- `Classical.choice.{u} : ∀ α : Sort u, Nonempty.{u} α → α` -/
def type : Expr Propext.sigs 1 0 :=
  .forallE (.sort (.param ⟨0, by decide⟩))
    (.forallE
      (.ind nonemptyHead ⟨0, by decide⟩ (fun _ => .param ⟨0, by decide⟩)
        ![#0] ![])
      #0)

end Choice

end Metalean
