/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Env

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {ι : IndSig} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}

structure PreCtorDecl (ζ : Sigs) (ι : IndSig) (s : Fin ι.nsorts)
    (csig : CtorSig ι.nsorts) where
  ordinary (f : Fin csig.nfields) :
    Expr ζ ι.nlevels (ι.nparams + f.val)
  recursive (f : Fin csig.nrecFields) :
    RecField ζ ι csig.nfields (csig.recursiveArity f) (csig.recursiveTarget f)
  targetIndices : Fin (ι.nindices s) →
    Expr ζ ι.nlevels (ι.nparams + csig.nfields)

structure PreInductive (ζ : Sigs) (ι : IndSig) where
  params : Ctx ζ ι.nlevels 0 ι.nparams
  indices (s : Fin ι.nsorts) :
    Ctx ζ ι.nlevels ι.nparams (ι.nparams + ι.nindices s)
  level : Level ι.nlevels
  ctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    PreCtorDecl ζ ι s (ι.ctors s c)

def PreCtorDecl.ordinaryTeleAux (pre : PreCtorDecl ζ ι s csig) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    Ctx ζ ι.nlevels ι.nparams (ι.nparams + count) :=
  match count with
  | 0 => .nil
  | count + 1 =>
    (pre.ordinaryTeleAux count (by omega)).snoc (pre.ordinary ⟨count, by omega⟩)

def PreCtorDecl.ordinaryTele (pre : PreCtorDecl ζ ι s csig) :
    Ctx ζ ι.nlevels ι.nparams (ι.nparams + csig.nfields) :=
  pre.ordinaryTeleAux csig.nfields le_rfl

def PreCtorDecl.withLevels (pre : PreCtorDecl ζ ι s csig)
    (levels : Fin csig.nfields → Level ι.nlevels) : Ctor ζ ι s csig where
  ordinary f := ⟨pre.ordinary f, levels f⟩
  recursive := pre.recursive
  targetIndices := pre.targetIndices

def PreInductive.withLevels (pre : PreInductive ζ ι)
    (levels : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Fin (ι.ctors s c).nfields → Level ι.nlevels) : Inductive ζ ι where
  params := pre.params
  indices := pre.indices
  level := pre.level
  ctors s c := (pre.ctors s c).withLevels (levels s c)

@[simp] theorem PreCtorDecl.withLevels_ordinaryTeleAux (pre : PreCtorDecl ζ ι s csig)
    (levels : Fin csig.nfields → Level ι.nlevels) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    (pre.withLevels levels).ordinaryTeleAux count hcount =
      pre.ordinaryTeleAux count hcount := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (Ctor.ordinaryTeleAux _ count _).snoc _ = (pre.ordinaryTeleAux count _).snoc _
    rw [ih (by omega)]
    rfl

@[simp] theorem PreCtorDecl.withLevels_ordinaryTele (pre : PreCtorDecl ζ ι s csig)
    (levels : Fin csig.nfields → Level ι.nlevels) :
    (pre.withLevels levels).ordinaryTele = pre.ordinaryTele :=
  pre.withLevels_ordinaryTeleAux levels csig.nfields le_rfl

end Metalean
