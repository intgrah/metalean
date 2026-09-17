/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.Basic

public section

namespace ZFSet

@[simp] abbrev proof : ZFSet := ∅

@[simp] abbrev falsum : ZFSet := ∅

@[simp] abbrev verum : ZFSet := {proof}

@[simp] abbrev truth : ZFSet := powerset verum

@[simp] theorem mem_verum {z : ZFSet} : z ∈ verum ↔ z = proof := by simp

theorem proof_mem_verum : proof ∈ verum := by simp
theorem falsum_mem_truth : falsum ∈ truth := by simp

theorem falsum_ne_verum : falsum ≠ verum := by
  intro h
  simpa using congrArg (fun x => ∅ ∈ x) h

@[simp] theorem mem_truth {z : ZFSet} : z ∈ truth ↔ z = falsum ∨ z = verum := by
  rw [truth, mem_powerset]
  constructor
  · intro h
    rcases eq_empty_or_nonempty z with hz | ⟨w, hw⟩
    · exact .inl hz
    · have hp : proof ∈ z := mem_verum.mp (h hw) ▸ hw
      exact .inr (ext fun v => ⟨fun hv => h hv, fun hv => mem_verum.mp hv ▸ hp⟩)
  · rintro (rfl | rfl)
    · simp [falsum]
    · exact fun _ => id

variable {p u v : ZFSet}

theorem eq_verum_of_mem (hp : p ∈ truth) (hu : u ∈ p) : p = verum := by
  rcases mem_truth.mp hp with rfl | rfl
  · simp at hu
  · rfl

theorem eq_of_mem_truth (hp : p ∈ truth) (hu : u ∈ p) (hv : v ∈ p) :
    u = v := by
  rcases mem_truth.mp hp with rfl | rfl
  · simp at hu
  · exact (mem_verum.mp hu).trans (mem_verum.mp hv).symm

end ZFSet
