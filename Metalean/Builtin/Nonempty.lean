/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Iff

@[expose] public section

namespace Metalean.Nonempty

variable {ζ : Sigs}

@[reducible] def ctorSig : CtorSig 1 where
  nfields := 1
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def sig : IndSig where
  nlevels := 1
  nparams := 1
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ _ := ctorSig

/-- `Nonempty.{u} (α : Sort u) : Prop` -/
@[reducible] def block : Inductive ζ sig where
  params := #t[.sort (.param ⟨0, by decide⟩)]
  indices _ := .nil
  level := .zero
  ctors | ⟨0, _⟩, ⟨0, _⟩ => {
    ordinary _ := ⟨.var ⟨0, by simp [sig]⟩,
      .param ⟨0, by decide⟩⟩
    recursive f := Fin.elim0 f
    targetIndices := ![]
  }

abbrev sigs : Sigs := .snoc Iff.sigs (.inductive sig)

def env : Env sigs := .snoc Iff.env (.inductive block)

end Metalean.Nonempty
