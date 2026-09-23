/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Quot.Basic

@[expose] public section

namespace Metalean.Level

variable {ℓ : Nat}

@[simp] def rel (u : Level ℓ) : Bool := decide (u ≠ zero)

@[simp] theorem rel_zero : (zero : Level ℓ).rel = false := by simp

theorem imax_eq_zero_iff (u v : Level ℓ) : u.imax v = zero ↔ v = zero := by
  constructor
  · intro h
    exact ext fun ν => by simpa using congrArg (eval ν) h
  · intro rfl
    exact ext <| by simp

@[simp] theorem rel_imax (u v : Level ℓ) : (u.imax v).rel = v.rel := by
  simp [imax_eq_zero_iff]

end Metalean.Level
