/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Basic
public import Metalean.Level.Quot.Order
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

inductive Subsingleton (I : Inductive ζ ι) : Prop where
  | intro :
    (∀ s, ∀ c c' : Fin (ι.nctors s), c = c') →
    (∀ s c, (I.ctors s c).Eligible I.level) →
    Subsingleton I

def RecAllowed (I : Inductive ζ ι) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) : Prop :=
  I.Subsingleton ∨ l ≤ Level.imax l I.level{ls}

theorem Subsingleton.singleton (h : I.Subsingleton) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 ∧ (I.ctors s c).Eligible I.level := by
  have ⟨hunique, heligible⟩ := h
  refine ⟨Nat.le_antisymm ?_ (Nat.zero_lt_of_lt c.isLt), heligible s c⟩
  by_contra hlt
  have h01 : (⟨0, by omega⟩ : Fin (ι.nctors s)) = ⟨1, by omega⟩ := hunique s _ _
  simp at h01

theorem RecAllowed.subsingleton {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
    (h : I.RecAllowed ls l) (hl : l.eval ν ≠ 0) (hI : I.level{ls}.eval ν = 0) :
    I.Subsingleton := by
  rcases h with h | h
  · exact h
  · exact (hl ((Level.le_imax_iff.mp h) ν hI)).elim

theorem RecAllowed.zero (ls : Fin ι.nlevels → Level ℓ) : I.RecAllowed ls .zero :=
  .inr fun ν => by simp

theorem LargeElim.recAllowed (h : I.LargeElim) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    I.RecAllowed ls l := by
  by_cases hlevel : Level.one ≤ I.level
  · refine .inr (Level.le_imax_iff.mpr fun ν hzero => ?_)
    have hpos := hlevel fun p => (ls p).eval ν
    rw [Level.eval_inst] at hzero
    simp [Function.comp_def] at hpos hzero
    omega
  · refine .inl ⟨fun s c c' => ?_, fun s c => ?_⟩
    · cases h s with
      | large hl => exact (hlevel hl).elim
      | subsingleton _ hunique _ => exact hunique c c'
    · cases h s with
      | large hl => exact (hlevel hl).elim
      | subsingleton _ _ heligible => exact heligible c

theorem RecAllowed.instL {ls : Fin ι.nlevels → Level ℓ} (h : I.RecAllowed ls u)
    (ls' : Param ℓ → Level ℓ') : I.RecAllowed ls{ls'} u{ls'} := by
  rcases h with h | h
  · exact .inl h
  · refine .inr (Level.le_imax_iff.mpr fun ν hzero => ?_)
    have key := (Level.le_imax_iff.mp h) (Level.eval ν ∘ ls')
    simp only [Level.eval_inst, Function.comp_def, InstLevel.inst_tuple] at hzero key ⊢
    exact key hzero

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

@[simp] theorem subsingleton_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂) :
    (I.map pre).Subsingleton ↔ I.Subsingleton := by
  constructor <;> intro ⟨hunique, heligible⟩
  · exact ⟨hunique, fun s c => ((I.ctors s c).eligible_map pre I.level).mp (heligible s c)⟩
  · exact ⟨hunique, fun s c => ((I.ctors s c).eligible_map pre I.level).mpr (heligible s c)⟩

@[simp] theorem recAllowed_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    (I.map pre).RecAllowed ls l ↔ I.RecAllowed ls l :=
  or_congr (I.subsingleton_map pre) Iff.rfl

namespace SortLargeElim

theorem singleton_of_eval_zero (h : I.SortLargeElim s)
    (ls : Fin ι.nlevels → Level ℓ)
    (hzero : I.level{ls}.eval ν = 0)
    (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 ∧ (I.ctors s c).Eligible I.level := by
  cases h with
  | large hlevel =>
    have hpositive : 1 ≤ I.level{ls}.eval ν := by
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
