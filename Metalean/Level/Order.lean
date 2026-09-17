/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Basic

public section

namespace Metalean.Level

variable {ℓ : Nat} {l₁ l₂ : Level ℓ}

instance : SemilatticeSup (Level ℓ) where
  le l₁ l₂ := ∀ ν, l₁.eval ν ≤ l₂.eval ν
  le_refl _ _ := Nat.le_refl _
  le_trans _ _ _ h h' ν := Nat.le_trans (h ν) (h' ν)
  le_antisymm _ _ h h' := Level.ext fun ν => Nat.le_antisymm (h ν) (h' ν)
  sup := Level.max
  le_sup_left _ _ ν := by simp
  le_sup_right _ _ ν := by simp
  sup_le _ _ _ h h' ν := by simpa using Nat.max_le.mpr ⟨h ν, h' ν⟩

theorem imax_le_right_of_eq_zero (h : l₂ = zero) : l₁.imax l₂ ≤ l₂ :=
  fun ν => by simp [h]

theorem eval_le_of_imax_le {ν : Param ℓ → Nat} (h : l₁.imax l₂ ≤ l₂) (hl₂ : l₂.eval ν ≠ 0) :
    l₁.eval ν ≤ l₂.eval ν :=
  Nat.le_of_imax_le (by simpa using h ν) hl₂

end Metalean.Level
