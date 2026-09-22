/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Ctx
public import Metalean.Level.Order
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₁ ζ₂ : Sigs}
  {ℓ ℓ' n nfields arity : Nat} {ι : IndSig} {s target : Fin ι.nsorts}
  {csig : CtorSig ι.nsorts}

@[derive_functor ζ]
structure Field (ζ : Sigs) (ι : IndSig) (nfields : Nat) where
  type : Expr ζ ι.nlevels (ι.nparams + nfields)
  level : Level ι.nlevels

/--
Instead of saying that we have some type, and that the type looks like some pattern,
with no recursive call negatively, we take a more intrinsic approach.
Since we don't use free variables (we cannot even mention the inductive type),
we just assume it is there and state what indices we are supplying it with.
The parameters are fixed so there is nothign to supply.
Since recursive occurrences are allowed to have things to the left of arrows, we
also prescribe it a telescope of types.
-/
@[derive_functor ζ]
structure RecField (ζ : Sigs) (ι : IndSig) (nfields arity : Nat) (target : Fin ι.nsorts) where
  tele : Ctx ζ ι.nlevels (ι.nparams + nfields) (ι.nparams + nfields + arity)
  indices : Fin (ι.nindices target) → Expr ζ ι.nlevels (ι.nparams + nfields + arity)

/--
It's impossible for a recursive field to be depended on.
So for all purposes we just assume that all recursive fields come last, which is fine
since this is just weakened from what the user wrote.
That means we need some frontend translation.
-/
@[derive_functor ζ]
structure Ctor (ζ : Sigs) (ι : IndSig) (s : Fin ι.nsorts) (csig : CtorSig ι.nsorts) where
  /-- Non-recursive field -/
  ordinary (f : Fin csig.nfields) : Field ζ ι f.val
  /-- Recursive fields come last and get all the non-recursive fields in the context. -/
  recursive (f : Fin csig.nrecFields) :
    RecField ζ ι csig.nfields (csig.recursiveArity f) (csig.recursiveTarget f)
  /--
  The return type of the constructor has to choose a particular sort (within the
  mutual inductive block), and the indices for that sort. The parameters are fixed
  so there is nothing to choose.
  -/
  targetIndices : Fin (ι.nindices s) → Expr ζ ι.nlevels (ι.nparams + csig.nfields)

/-- This is a (possibly mutual) inductive block -/
@[derive_functor ζ]
structure Inductive (ζ : Sigs) (ι : IndSig) where
  params : Ctx ζ ι.nlevels 0 ι.nparams
  indices (s : Fin ι.nsorts) : Ctx ζ ι.nlevels ι.nparams (ι.nparams + ι.nindices s)
  level : Level ι.nlevels
  ctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) : Ctor ζ ι s (ι.ctors s c)

namespace Ctor

def ordinaryTeleAux (ctor : Ctor ζ ι s csig) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    Ctx ζ ι.nlevels ι.nparams (ι.nparams + count) :=
  match count with
  | 0 => .nil
  | count + 1 =>
    ctor.ordinaryTeleAux count (by omega)
      |>.snoc ((ctor.ordinary ⟨count, by omega⟩).type)

@[simp] theorem ordinaryTeleAux_entry (ctor : Ctor ζ ι s csig)
    (count : Nat) (hcount : count ≤ csig.nfields) (f : Fin count) :
    Ctx.entry (p := ι.nparams + f.val)
        (ctor.ordinaryTeleAux count hcount) (by omega) (by omega) =
      (ctor.ordinary (f.castLE hcount)).type := by
  induction f using Fin.lastInduction with
  | last count =>
      change (ctor.ordinaryTeleAux (count + 1) hcount).entry _ _ =
        (ctor.ordinary ⟨count, by omega⟩).type
      simp [ordinaryTeleAux]
  | cast f ih =>
    simpa [ordinaryTeleAux] using ih (by omega)

abbrev ordinaryTele (ctor : Ctor ζ ι s csig) :
    Ctx ζ ι.nlevels ι.nparams (ι.nparams + csig.nfields) :=
  ctor.ordinaryTeleAux csig.nfields le_rfl

@[simp] theorem ordinaryTeleAux_map (pre : ζ₁ ⟶ ζ₂)
    (ctor : Ctor ζ₁ ι s csig) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    (ctor.ordinaryTeleAux count hcount).map pre =
      (ctor.map pre).ordinaryTeleAux count hcount := by
  induction count with
  | zero => rfl
  | succ count ih => simp [ordinaryTeleAux, map, Field.map, ih]

end Ctor

namespace Inductive

def argTele (I : Inductive ζ ι) (s : Fin ι.nsorts) :
    Ctx ζ ι.nlevels 0 (ι.nparams + ι.nindices s) :=
  I.params ++ I.indices s

variable
  (I : Inductive ζ₁ ι)
  (pre : ζ₁ ⟶ ζ₂)
  (ls : Fin ι.nlevels → Level ℓ)
  (s : Fin ι.nsorts)
  (ps : Fin ι.nparams → Expr ζ₁ ℓ n)

def paramType (f : Fin ι.nparams) : Expr ζ₁ ℓ n :=
  ((I.params.entry (Nat.zero_le f.val) f.isLt).instL ls).subst
    fun previous : Fin f.val => ps (previous.castLE (by omega))

def indexType
    (is : Fin (ι.nindices s) → Expr ζ₁ ℓ n)
    (f : Fin (ι.nindices s)) : Expr ζ₁ ℓ n :=
  I.indices s |>.proj f |>.instL ls |>.subst
    (Fin.append ps fun previous => is (previous.castLE f.isLt.le))

@[simp] theorem paramType_map
    (f : Fin ι.nparams) :
    (I.paramType ls ps f).map pre =
      (I.map pre).paramType ls
        (fun i => (ps i).map pre) f := by
  simp [paramType]
  rfl

@[simp] theorem indexType_map
    (is : Fin (ι.nindices s) → Expr ζ₁ ℓ n)
    (f : Fin (ι.nindices s)) :
    (I.indexType ls s ps is f).map pre =
      (I.map pre).indexType ls s
        (fun i => (ps i).map pre)
        (fun i => (is i).map pre) f := by
  simp [indexType, map]

@[simp] theorem paramType_instL (I : Inductive ζ₁ ι)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin ι.nparams) (levelSubst : Param ℓ → Level ℓ') :
    (I.paramType ls ps f).instL levelSubst =
      I.paramType (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst) f := by
  simp [paramType]
  rfl

@[simp] theorem indexType_instL
    (is : Fin (ι.nindices s) → Expr ζ₁ ℓ n)
    (f : Fin (ι.nindices s)) (levelSubst : Param ℓ → Level ℓ') :
    (I.indexType ls s ps is f).instL levelSubst =
      I.indexType (fun i => (ls i).inst levelSubst) s
        (fun i => (ps i).instL levelSubst)
        (fun i => (is i).instL levelSubst) f := by
  simp [indexType]

def indexTele (I : Inductive ζ₁ ι)
    (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n) :
    Ctx ζ₁ ℓ n (n + ι.nindices s) :=
  I.indices s |>.instL ls |>.substN ps (ι.nindices s)

@[simp] theorem indexTele_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (ls : Fin ι.nlevels → Level ℓ)
    (s : Fin ι.nsorts) (ps : Fin ι.nparams → Expr ζ₁ ℓ n) :
    (I.indexTele ls s ps).map pre =
      (I.map pre).indexTele ls s
        fun i => (ps i).map pre :=
  (Ctx.map_substN pre ps _ _).trans
    (congrArg (Ctx.substN _ _) ((I.indices s).map_instL pre ls))

@[simp] theorem indexTele_instL (I : Inductive ζ₁ ι)
    (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (levelSubst : Param ℓ → Level ℓ') :
    (I.indexTele ls s ps).instL levelSubst =
      I.indexTele (fun i => (ls i).inst levelSubst) s
        fun i => (ps i).instL levelSubst := by
  simp [indexTele]
  rfl

end Inductive

namespace Inductive

variable {ι : IndSig} (I : Inductive ζ ι)

def LevelOK (l : Level ι.nlevels) : Prop :=
  Level.imax l I.level ≤ I.level

theorem levelOK_of_zero {l : Level ι.nlevels} :
    I.level = .zero → I.LevelOK l :=
  Level.imax_le_right_of_eq_zero

end Inductive

end Metalean
