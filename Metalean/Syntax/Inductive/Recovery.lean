/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Ctor
public import Metalean.Syntax.Inductive.LargeElimination
public import Metalean.Level.Relevance

/-! # Idk
Hard to even explain what this code is doing
-/

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {ι : IndSig} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}

namespace Ctor

def recoveryIndex (ctor : Ctor ζ ι s csig) (f : Fin csig.nfields) :
    Option (Fin (ι.nindices s)) :=
  (List.finRange (ι.nindices s)).find? fun i =>
    (ctor.targetIndices i).isVar == some (ι.nparams + f.val)

theorem recoveryIndex_ne_none (ctor : Ctor ζ ι s csig) (f : Fin csig.nfields)
    (hi : ∃ i, (ctor.targetIndices i).isVar = some (ι.nparams + f.val)) :
    ctor.recoveryIndex f ≠ none := by
  simpa [recoveryIndex, List.find?_eq_none] using hi

variable {ctor : Ctor ζ ι s csig} {f : Fin csig.nfields} {i : Fin (ι.nindices s)}

theorem recoveryIndex_spec (h : ctor.recoveryIndex f = some i) :
    ctor.targetIndices i = .var (Fin.natAdd ι.nparams f) := by
  apply Expr.eq_var_of_isVar
  have hi := List.find?_some h
  simpa using hi

theorem targetIndex_recovery {ℓ n : Nat} (h : ctor.recoveryIndex f = some i)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin csig.nfields → Expr ζ ℓ n) :
    ctor.targetIndex ls ps fds i = fds f := by
  simp [targetIndex, recoveryIndex_spec h, Expr.instL, Expr.subst]

theorem recoveryIndex_exists {u : Level ι.nlevels} (h : ctor.Eligible u)
    {ℓ : Nat} (ls : Fin ι.nlevels → Level ℓ) (f : Fin csig.nfields)
    (hf : Level.rel ((ctor.ordinary f).level.inst ls) = true) :
    ∃ i, ctor.recoveryIndex f = some i := by
  have he := h.ordinary f
  have hex : ∃ i, (ctor.targetIndices i).isVar = some (ι.nparams + f.val) := by
    rcases he with hz | he
    · simp [hz] at hf
    · exact he
  cases hi : ctor.recoveryIndex f with
  | none => exact (ctor.recoveryIndex_ne_none f hex hi).elim
  | some i => exact ⟨i, rfl⟩

end Ctor

end Metalean
