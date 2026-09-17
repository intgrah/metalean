/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.RawLevel.Equiv

public section

namespace Metalean.RawLevel

variable {ℓ : Nat} {l₁ l₂ : RawLevel ℓ}

instance : Preorder (RawLevel ℓ) where
  le l₁ l₂ := ∀ ν, l₁.eval ν ≤ l₂.eval ν
  le_refl _ _ := Nat.le_refl _
  le_trans _ _ _ h h' ν := Nat.le_trans (h ν) (h' ν)

theorem Equiv.le (h : l₁ ≈ l₂) : l₁ ≤ l₂ := fun ν => Nat.le_of_eq (h.eval ν)

theorem Equiv.ge (h : l₁ ≈ l₂) : l₁ ≥ l₂ := h.symm.le

theorem le_antisymm (h : l₁ ≤ l₂) (h' : l₂ ≤ l₁) : l₁ ≈ l₂ :=
  Equiv.of_eval fun ν => Nat.le_antisymm (h ν) (h' ν)

theorem equiv_iff_le_le : l₁ ≈ l₂ ↔ l₁ ≤ l₂ ∧ l₂ ≤ l₁ :=
  ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

theorem le_max_left (l₁ l₂ : RawLevel ℓ) : l₁ ≤ l₁.max l₂ := fun _ => Nat.le_max_left _ _

end Metalean.RawLevel
