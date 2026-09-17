/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.QuotSound

/-! # The `propext` axiom -/

@[expose] public section

namespace Metalean.Propext

abbrev eqHead : Head Quot.Sound.sigs (.inductive Eq.sig) :=
  .there (.there (.there (.there .here)))

abbrev iffHead : Head Quot.Sound.sigs (.inductive Iff.sig) := .there (.there .here)

/-- `propext : ∀ a b : Prop, Iff a b → Eq.{0} (Sort 0) a b` -/
def type : Expr Quot.Sound.sigs 0 0 :=
  .forallE .prop
    (.forallE .prop
      (.forallE
        (.ind iffHead ⟨0, by decide⟩ ![] ![#0, #1] ![])
        (.ind eqHead ⟨0, by decide⟩ (fun _ => .succ .zero)
          ![.prop, #0] ![#1])))

abbrev sigs : Sigs := .snoc Quot.Sound.sigs (.const .axiom 0)

def env : Env sigs := .snoc Quot.Sound.env (.axiom type)

end Metalean.Propext
