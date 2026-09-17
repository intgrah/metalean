/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Nonempty
public import Metalean.Syntax.Quot

@[expose] public section

namespace Metalean.Quot.Sound

abbrev eqHead : Head Nonempty.sigs (.inductive Eq.sig) := .there (.there (.there .here))

abbrev quotHead : Head Nonempty.sigs .quot := .there (.there .here)

/-- `Quot.sound : ∀ α r (a b : α), r a b → Eq (Quot α r) (Quot.mk α r a) (Quot.mk α r b)` -/
def type : Expr Nonempty.sigs 1 0 :=
  let r := (#1 : Expr Nonempty.sigs 1 5)
  .forallE (.sort (.param ⟨0, by decide⟩))
    (.forallE (.forallE #0 (.forallE #0 .prop))
      (.forallE #0
        (.forallE #0
          (.forallE (.app (.app #1 #2) #3)
            (Quot.eqApp eqHead (.param ⟨0, by decide⟩)
              (.quot quotHead (.param ⟨0, by decide⟩) #0 r)
              (.quotMk quotHead (.param ⟨0, by decide⟩) #0 r #2)
              (.quotMk quotHead (.param ⟨0, by decide⟩) #0 r #3))))))

abbrev sigs : Sigs := .snoc Nonempty.sigs (.const .axiom 1)

def env : Env sigs := .snoc Nonempty.env (.axiom type)

end Metalean.Quot.Sound
