/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Basic

@[expose] public section

namespace Metalean.Eq

variable {ζ : Sigs}

def ctorDecl :
    Ctor ζ sig ⟨0, by decide⟩ ctorSig where
  ordinary := fun f => ![] f
  recursive := fun f => ![] f
  targetIndices _ := #1

/-- `Eq.{u} (α : Sort u) (a : α) : α → Prop` -/
@[reducible] def block : Inductive ζ sig where
  params := #t[.sort (.param ⟨0, by decide⟩), #0]
  indices _ := #t[#0]
  level := .zero
  ctors | ⟨0, _⟩, ⟨0, _⟩ => ctorDecl

end Metalean.Eq
