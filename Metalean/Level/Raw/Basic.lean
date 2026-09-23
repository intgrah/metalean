/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Metalean.Level.Quot.Nat

@[expose] public section

namespace Metalean

abbrev Param ℓ := Fin ℓ

inductive RawLevel (ℓ : Nat) where
  | zero
  | succ (l : RawLevel ℓ)
  | max (l₁ l₂ : RawLevel ℓ)
  | imax (l₁ l₂ : RawLevel ℓ)
  | param (p : Param ℓ)
deriving DecidableEq, Hashable

namespace RawLevel

variable {ℓ ℓ₁ ℓ₂ : Nat}

def one : RawLevel ℓ := succ zero

def ofNat : Nat → RawLevel 0
  | 0 => zero
  | n + 1 => succ (ofNat n)

variable (ν : Param ℓ → Nat) in
def eval : RawLevel ℓ → Nat
  | zero => 0
  | succ u => u.eval + 1
  | max u₁ u₂ => Nat.max u₁.eval u₂.eval
  | imax u₁ u₂ => Nat.imax u₁.eval u₂.eval
  | param p => ν p

@[simp] theorem eval_zero (ν : Param ℓ → Nat) : eval ν zero = 0 := rfl

@[simp] theorem eval_succ (ν : Param ℓ → Nat) (l : RawLevel ℓ) :
    eval ν l.succ = eval ν l + 1 := rfl

@[simp] theorem eval_max (ν : Param ℓ → Nat) (l₁ l₂ : RawLevel ℓ) :
    eval ν (l₁.max l₂) = Nat.max (eval ν l₁) (eval ν l₂) := rfl

@[simp] theorem eval_imax (ν : Param ℓ → Nat) (l₁ l₂ : RawLevel ℓ) :
    eval ν (l₁.imax l₂) = Nat.imax (eval ν l₁) (eval ν l₂) := rfl

@[simp] theorem eval_param (ν : Param ℓ → Nat) (p : Param ℓ) : eval ν (param p) = ν p := rfl

@[simp] theorem eval_one (ν : Param ℓ → Nat) : eval ν (one : RawLevel ℓ) = 1 := rfl

@[simp] theorem eval_ofNat : ∀ n : Nat, (ofNat n).eval ![] = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (eval_ofNat n)

variable (ls : Param ℓ → RawLevel ℓ₁) in
def inst : RawLevel ℓ → RawLevel ℓ₁
  | zero => zero
  | succ u => succ u.inst
  | max u₁ u₂ => max u₁.inst u₂.inst
  | imax u₁ u₂ => imax u₁.inst u₂.inst
  | param p => ls p

@[simp] theorem inst_zero (ls : Param ℓ → RawLevel ℓ₁) : (zero : RawLevel ℓ).inst ls = zero := rfl

@[simp] theorem inst_succ (ls : Param ℓ → RawLevel ℓ₁) (l : RawLevel ℓ) :
    l.succ.inst ls = (l.inst ls).succ := rfl

@[simp] theorem inst_max (ls : Param ℓ → RawLevel ℓ₁) (l₁ l₂ : RawLevel ℓ) :
    (l₁.max l₂).inst ls = (l₁.inst ls).max (l₂.inst ls) := rfl

@[simp] theorem inst_imax (ls : Param ℓ → RawLevel ℓ₁) (l₁ l₂ : RawLevel ℓ) :
    (l₁.imax l₂).inst ls = (l₁.inst ls).imax (l₂.inst ls) := rfl

@[simp] theorem inst_param (ls : Param ℓ → RawLevel ℓ₁) (p : Param ℓ) : (param p).inst ls = ls p := rfl

@[simp] theorem inst_id (l : RawLevel ℓ) : l.inst param = l := by
  induction l <;> simp [*]

@[simp] theorem inst_inst (ls₁ : Param ℓ → RawLevel ℓ₁)
    (ls₂ : Param ℓ₁ → RawLevel ℓ₂) (l : RawLevel ℓ) :
    (l.inst ls₁).inst ls₂ =
      l.inst fun p => (ls₁ p).inst ls₂ := by
  induction l <;> simp [*]

end RawLevel

end Metalean
