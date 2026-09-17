/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Quot

@[expose] public section

namespace Metalean.Iff

variable {ζ : Sigs}

@[reducible] def ctorSig : CtorSig 1 where
  nfields := 2
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def sig : IndSig where
  nlevels := 0
  nparams := 2
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ _ := ctorSig

/-- `Iff (a b : Prop) : Prop` -/
@[reducible] def block : Inductive ζ sig where
  params := #t[.prop, .prop]
  indices _ := .nil
  level := .zero
  ctors _ _ := {
    ordinary
      | ⟨0, _⟩ => ⟨.forallE
            (.var ⟨0, by simp⟩)
            (.var ⟨1, by simp⟩),
          .zero⟩
      | ⟨1, _⟩ => ⟨.forallE
            (.var ⟨1, by simp⟩)
            (.var ⟨0, by simp⟩),
          .zero⟩
    recursive f := Fin.elim0 f
    targetIndices := ![]
  }

abbrev sigs : Sigs := .snoc Quot.sigs (.inductive sig)

def env : Env sigs := .snoc Quot.env (.inductive block)

end Metalean.Iff
