/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Order

@[expose] public section

namespace Metalean.Level

variable {ℓ : Nat}

instance : DecidableLE (Level ℓ) := fun u v =>
  Quotient.recOnSubsingleton₂ u v fun a b =>
    decidable_of_iff (a ≤ b) ⟨fun h => h, fun h => h⟩

def decZeroLe (u v : Level ℓ) : Bool :=
  Quotient.liftOn₂ u v RawLevel.decZeroLe fun a b a' b' ha hb => by
    apply Bool.eq_iff_iff.mpr
    rw [RawLevel.decZeroLe_iff, RawLevel.decZeroLe_iff]
    simp [← ha.eval, ← hb.eval]

theorem decZeroLe_iff (u v : Level ℓ) :
    decZeroLe u v = true ↔ ∀ ν, u.eval ν = 0 → v.eval ν = 0 := by
  induction u using Quotient.inductionOn with
  | h a =>
    induction v using Quotient.inductionOn with
    | h b => exact RawLevel.decZeroLe_iff a b

end Metalean.Level
