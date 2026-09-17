/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Batteries.Data.Fin.Coding
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Fintype.Basic
public import Metalean.Fin
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {nsorts : Nat}

inductive ConstKind where
  | «axiom»
  | «opaque»
  | «def»
deriving DecidableEq, Repr

/--
This is the "shape" of a constructor, consisting of only numeric data.
It tells you in what ways you can legally index into it
-/
structure CtorSig (nsorts : Nat) where
  nfields : Nat
  nrecFields : Nat
  recursiveArity : Fin nrecFields → Nat
  recursiveTarget : Fin nrecFields → Fin nsorts
deriving DecidableEq

/--
This is the "shape" of an inductive type, consisting of only numeric data.
It tells you in what ways you can legally index into it
-/
structure IndSig where
  nlevels : Nat
  nparams : Nat
  nsorts : Nat
  nindices (s : Fin nsorts) : Nat
  nctors (s : Fin nsorts) : Nat
  ctors (s : Fin nsorts) (c : Fin (nctors s)) : CtorSig nsorts
deriving DecidableEq

namespace IndSig

@[reducible] def motivesEnd (ι : IndSig) : Nat := ι.nparams + ι.nsorts
@[reducible] def casesEnd (ι : IndSig) : Nat := ι.motivesEnd + Fin.sum ι.nctors
@[reducible] def recrEnd (ι : IndSig) (s : Fin ι.nsorts) : Nat := ι.casesEnd + ι.nindices s + 1

/-- It is sometimes convenient to defer addition of bounds -/
inductive RecrBinder (ι : IndSig) (s : Fin ι.nsorts) where
  | param (p : Fin ι.nparams)
  | motive (t : Fin ι.nsorts)
  | case (t : Fin ι.nsorts) (c : Fin (ι.nctors t))
  | index (i : Fin (ι.nindices s))
  | major

namespace RecrBinder

variable {ι : IndSig} {s : Fin ι.nsorts}

/-- Reify the bound -/
def resolve : RecrBinder ι s → Fin (ι.recrEnd s)
  | .param p => ⟨p.val, by lia⟩
  | .motive t => ⟨ι.nparams + t.val, by lia⟩
  | .case t c => ⟨ι.motivesEnd + (Fin.encodeSigma ι.nctors ⟨t, c⟩).val, by lia⟩
  | .index i => ⟨ι.casesEnd + i.val, by lia⟩
  | .major => Fin.last _

theorem resolve_motive_eq (t : Fin ι.nsorts) :
    (RecrBinder.motive t).resolve =
      (((Fin.natAdd ι.nparams t).castAdd (Fin.sum ι.nctors)).castAdd
        (ι.nindices s)).castSucc := rfl

theorem resolve_index_eq (i : Fin (ι.nindices s)) :
    (RecrBinder.index i).resolve =
      (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) i).castSucc :=
  rfl

end RecrBinder

end IndSig

namespace Eq

@[reducible] def ctorSig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def sig : IndSig where
  nlevels := 1
  nparams := 2
  nsorts := 1
  nindices _ := 1
  nctors _ := 1
  ctors _ _ := ctorSig

end Eq

/-- This is the "shape" of any constant-like head -/
inductive Sig where
  | const (kind : ConstKind) (nlevels : Nat)
  | inductive (ι : IndSig)
  /-- No information carried here because we already know what
  the quotient constants look like and thus how to index into them -/
  | quot
deriving DecidableEq

/-- Snoc list of signature shapes -/
inductive Sigs where
  | nil
  | snoc (ζ : Sigs) (sig : Sig)

namespace Sigs

def length : Sigs → Nat
  | .nil => 0
  | .snoc pre _ => pre.length + 1

/-- Data that one is a prefix of the other -/
inductive Prefix (ζ : Sigs) : Sigs → Type
  | refl : Prefix ζ ζ
  | step {ζ' : Sigs} {sig : Sig} :
    Prefix ζ ζ' → Prefix ζ (.snoc ζ' sig)

def Prefix.trans {ζ₁ ζ₂ ζ₃ : Sigs} :
    Prefix ζ₁ ζ₂ → Prefix ζ₂ ζ₃ → Prefix ζ₁ ζ₃
  | pre, .refl => pre
  | pre, .step suffix => .step (pre.trans suffix)

instance : SmallCategory Sigs where
  Hom := Prefix
  id _ := .refl
  comp := Prefix.trans
  id_comp p := by
    induction p with
    | refl => rfl
    | step p ih => simp! [ih]
  comp_id _ := rfl
  assoc p₁ p₂ p₃ := by
    induction p₃ with
    | refl => rfl
    | step p₃ ih => simp! [ih]

end Sigs

/--
A well scoped reference to something in the environment.
This is data. It's sort of similar to the literal string "Nat", which
says that you want a constant named Nat. Because this is indexed by the
shape of the thing you want, you already know what shape of thing you are looking for.
So the thing that you get is guaranteed to have that shape.
-/
inductive Head : Sigs → Sig → Type
  | here {ζ : Sigs} {sig : Sig} :
    Head (.snoc ζ sig) sig
  | there {ζ : Sigs} {sig sig₁ : Sig} :
    Head ζ sig → Head (.snoc ζ sig₁) sig
deriving DecidableEq

namespace Head

def map {sig : Sig} {ζ₁ ζ₂ : Sigs} : (ζ₁ ⟶ ζ₂) →
    Head ζ₁ sig → Head ζ₂ sig
  | .refl => id
  | .step rest => fun η => (η.map rest).there

@[reducible, functor] def functor (sig : Sig) : Sigs ⥤ Type where
  obj ζ := Head ζ sig
  map pre := ↾map pre
  map_id _ := rfl
  map_comp p₁ p₂ := by
    induction p₂ with
    | refl => rfl
    | step pre₂ ih =>
      ext η
      exact congrArg Head.there (ConcreteCategory.congr_hom ih η)

/-- Oldest-first numeric position -/
def position {ζ : Sigs} {sig : Sig} : Head ζ sig → Nat
  | @here pre _ => pre.length
  | there η => η.position

/-- Remove the newest signature entry from a head when it refers to the strict prefix -/
def unstep {sig sig₁ : Sig} {ζ : Sigs} :
    Head (.snoc ζ sig₁) sig → Option (Head ζ sig)
  | .here => none
  | .there η => some η

@[simp] theorem unstep_map_step {sig sig₁ : Sig} {ζ : Sigs}
    (η : Head ζ sig) :
    unstep (η.map (@.step ζ ζ sig₁ .refl)) = some η :=
  rfl

end Head

end Metalean
