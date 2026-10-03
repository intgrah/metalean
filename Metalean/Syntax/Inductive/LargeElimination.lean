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

judgement Subsingleton (I : Inductive ζ ι) : Prop where

  ∀ s, ∀ c c' : Fin (ι.nctors s), c = c'
  ∀ s c, (I.ctors s c).Eligible I.level
  ──────────────────── intro
  Subsingleton I

def LargeElim (I : Inductive ζ ι) : Prop :=
  I.Subsingleton ∨ Level.one ≤ I.level

def RecAllowed (I : Inductive ζ ι) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) : Prop :=
  I.Subsingleton ∨ l ≤ Level.imax l I.level{ls}

namespace Subsingleton

theorem unique (h : I.Subsingleton) (s : Fin ι.nsorts) (c c' : Fin (ι.nctors s)) : c = c' := by
  cases h with
  | intro hunique _ => exact hunique s c c'

theorem eligible (h : I.Subsingleton) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.ctors s c).Eligible I.level := by
  cases h with
  | intro _ heligible => exact heligible s c

theorem nctors_eq_one (h : I.Subsingleton) {s : Fin ι.nsorts} (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 := by
  refine Nat.le_antisymm ?_ (Nat.zero_lt_of_lt c.isLt)
  by_contra hlt
  have h01 : (⟨0, by omega⟩ : Fin (ι.nctors s)) = ⟨1, by omega⟩ := h.unique s _ _
  simp at h01

end Subsingleton

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
  rcases h with h | hlevel
  · exact .inl h
  · refine .inr (Level.le_imax_iff.mpr fun ν hzero => ?_)
    have hpositive : 1 ≤ I.level{ls}.eval ν := by
      rw [Level.eval_inst]
      exact hlevel fun p => (ls p).eval ν
    omega

theorem RecAllowed.instL {ls : Fin ι.nlevels → Level ℓ} (h : I.RecAllowed ls u)
    (ls' : Param ℓ → Level ℓ') : I.RecAllowed ls{ls'} u{ls'} := by
  rcases h with h | h
  · exact .inl h
  · refine .inr (Level.le_imax_iff.mpr fun ν hzero => ?_)
    have key := (Level.le_imax_iff.mp h) (Level.eval ν ∘ ls')
    simp only [Level.eval_inst, Function.comp_def, InstLevel.inst_tuple] at hzero key ⊢
    exact key hzero

@[simp] theorem subsingleton_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂) :
    (I.map pre).Subsingleton ↔ I.Subsingleton := by
  constructor <;> intro ⟨hunique, heligible⟩
  · exact ⟨hunique, fun s c => ((I.ctors s c).eligible_map pre I.level).mp (heligible s c)⟩
  · exact ⟨hunique, fun s c => ((I.ctors s c).eligible_map pre I.level).mpr (heligible s c)⟩

@[simp] theorem largeElim_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂) :
    (I.map pre).LargeElim ↔ I.LargeElim := by
  simp only [LargeElim, subsingleton_map]
  exact Iff.rfl

@[simp] theorem recAllowed_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    (I.map pre).RecAllowed ls l ↔ I.RecAllowed ls l :=
  or_congr (I.subsingleton_map pre) Iff.rfl

end Inductive

end Metalean
