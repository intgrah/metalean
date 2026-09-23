/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Raw.Basic

public section

namespace Metalean.RawLevel

variable {ℓ : Nat} {l l₁ l₂ l₃ l₄ : RawLevel ℓ}

@[expose] protected def Equiv (l₁ l₂ : RawLevel ℓ) : Prop := l₁.eval = l₂.eval

instance : HasEquiv (RawLevel ℓ) := ⟨RawLevel.Equiv⟩

theorem Equiv.eval (h : l₁ ≈ l₂) (ν : Param ℓ → Nat) : l₁.eval ν = l₂.eval ν :=
  congrFun h ν

theorem Equiv.of_eval (h : ∀ ν, l₁.eval ν = l₂.eval ν) : l₁ ≈ l₂ := funext h

@[refl] theorem Equiv.refl (l : RawLevel ℓ) : l ≈ l := rfl

theorem Equiv.symm (h : l₁ ≈ l₂) : l₂ ≈ l₁ := Eq.symm h

theorem Equiv.trans {l₃ : RawLevel ℓ} (h : l₁ ≈ l₂) (h' : l₂ ≈ l₃) : l₁ ≈ l₃ :=
  Eq.trans h h'

instance : Trans (α := RawLevel ℓ) (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨Equiv.trans⟩

theorem Equiv.succ (h : l₁ ≈ l₂) : l₁.succ ≈ l₂.succ :=
  Equiv.of_eval fun ν => congrArg (· + 1) (h.eval ν)

theorem Equiv.max (h₁ : l₁ ≈ l₂) (h₂ : l₃ ≈ l₄) : l₁.max l₃ ≈ l₂.max l₄ :=
  Equiv.of_eval fun ν => by simp [h₁.eval ν, h₂.eval ν]

theorem Equiv.imax (h₁ : l₁ ≈ l₂) (h₂ : l₃ ≈ l₄) : l₁.imax l₃ ≈ l₂.imax l₄ :=
  Equiv.of_eval fun ν => by simp [h₁.eval ν, h₂.eval ν]

instance setoid (ℓ : Nat) : Setoid (RawLevel ℓ) where
  r := (· ≈ ·)
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end Metalean.RawLevel
