/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Basic
public import Metalean.Level.Order
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' : Nat}
  {ι : IndSig} {I : Inductive ζ ι} {s : Fin ι.nsorts}
  {csig : CtorSig ι.nsorts}
  {u : Level ℓ} {ν : Param ℓ → Nat}

namespace Ctor

structure Eligible (ctor : Ctor ζ ι s csig)
    (l : Level ι.nlevels) : Prop where
  ordinary (f : Fin csig.nfields) :
    (ctor.ordinary f).level = .zero ∨
      ∃ i, (ctor.targetIndices i).isVar = some (ι.nparams + f.val)
  recursive (f : Fin csig.nrecFields) :
    l = .zero

@[simp] theorem eligible_map (ctor : Ctor ζ₁ ι s csig)
    (pre : ζ₁ ⟶ ζ₂) (l : Level ι.nlevels) :
    (ctor.map pre).Eligible l ↔ ctor.Eligible l := by
  constructor
  · intro h
    exact ⟨fun f => by simpa [map, Field.map] using h.ordinary f, h.recursive⟩
  · intro h
    exact ⟨fun f => by simpa [map, Field.map] using h.ordinary f, h.recursive⟩

end Ctor

namespace Inductive

judgement SortLargeElim (I : Inductive ζ ι) (s : Fin ι.nsorts) : Prop where

  /-- Not a proposition, so it is proof relevant -/
  Level.one ≤ I.level
  ──────────────────── large
  SortLargeElim I s

  /-- Could be a proposition, but:
  - The block declares a single sort (n.b. this restriction is not actually necessary)
  - It has no constructors to distinguish, i.e. at most constructor
  - For all constructors (well, there is at most one, so really, *the* constructor if it exists),
    there are no fields to distinguish  -/
  ι.nsorts = 1
  ∀ c c' : Fin (ι.nctors s), c = c'
  ∀ c, (I.ctors s c).Eligible I.level
  ──────────────────── subsingleton
  SortLargeElim I s

def LargeElim (I : Inductive ζ ι) : Prop :=
  ∀ s, I.SortLargeElim s

def RecAllowed (I : Inductive ζ ι) (l : Level ℓ) : Prop :=
  l = .zero ∨ I.LargeElim

theorem RecAllowed.largeElim {l : Level ℓ} {ν : Param ℓ → Nat} (h : I.RecAllowed l)
    (hl : l.eval ν ≠ 0) : I.LargeElim := by
  rcases h with rfl | hlarge
  · exact (hl rfl).elim
  · exact hlarge

theorem RecAllowed.instL (h : I.RecAllowed u) (ls : Param ℓ → Level ℓ') :
    I.RecAllowed (u.inst ls) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr h

@[simp] theorem sortLargeElim_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (s : Fin ι.nsorts) :
    (I.map pre).SortLargeElim s ↔ I.SortLargeElim s := by
  constructor <;> intro h
  · cases h with
    | large hlevel => exact .large hlevel
    | subsingleton hsorts hunique heligible =>
      exact .subsingleton hsorts hunique fun c =>
        ((I.ctors s c).eligible_map pre I.level).mp (heligible c)
  · cases h with
    | large hlevel => exact .large hlevel
    | subsingleton hsorts hunique heligible =>
      exact .subsingleton hsorts hunique fun c =>
        ((I.ctors s c).eligible_map pre I.level).mpr (heligible c)

@[simp] theorem largeElim_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) :
    (I.map pre).LargeElim ↔ I.LargeElim := by
  constructor <;> intro h s
  · exact (I.sortLargeElim_map pre s).mp (h s)
  · exact (I.sortLargeElim_map pre s).mpr (h s)

@[simp] theorem recAllowed_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (l : Level ℓ) :
    (I.map pre).RecAllowed l ↔ I.RecAllowed l := by
  simp [RecAllowed]

namespace SortLargeElim

theorem singleton_of_eval_zero (h : I.SortLargeElim s)
    (ls : Fin ι.nlevels → Level ℓ)
    (hzero : (I.level.inst ls).eval ν = 0)
    (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 ∧ (I.ctors s c).Eligible I.level := by
  cases h with
  | large hlevel =>
    have hpositive : 1 ≤ (I.level.inst ls).eval ν := by
      rw [Level.eval_inst]
      exact hlevel fun p => (ls p).eval ν
    omega
  | subsingleton _ hunique heligible =>
    refine ⟨Nat.le_antisymm ?_ (Nat.zero_lt_of_lt c.isLt), heligible c⟩
    by_contra hlt
    have h01 : (⟨0, by omega⟩ : Fin (ι.nctors s)) = ⟨1, by omega⟩ := hunique _ _
    simp at h01

end SortLargeElim

end Inductive

end Metalean
