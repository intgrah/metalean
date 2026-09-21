/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Metalean.Level.Nat

@[expose] public section

namespace Metalean

abbrev Param ℓ := Fin ℓ

def zeroNs : Param 0 → Nat := ![]

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

@[simp] theorem eval_ofNat : ∀ n : Nat, (ofNat n).eval zeroNs = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (eval_ofNat n)

variable (levelSubst : Param ℓ → RawLevel ℓ₁) in
def inst : RawLevel ℓ → RawLevel ℓ₁
  | zero => zero
  | succ u => succ u.inst
  | max u₁ u₂ => max u₁.inst u₂.inst
  | imax u₁ u₂ => imax u₁.inst u₂.inst
  | param p => levelSubst p

@[simp] theorem inst_zero (levelSubst : Param ℓ → RawLevel ℓ₁) : (zero : RawLevel ℓ).inst levelSubst = zero := rfl

@[simp] theorem inst_succ (levelSubst : Param ℓ → RawLevel ℓ₁) (l : RawLevel ℓ) :
    l.succ.inst levelSubst = (l.inst levelSubst).succ := rfl

@[simp] theorem inst_max (levelSubst : Param ℓ → RawLevel ℓ₁) (l₁ l₂ : RawLevel ℓ) :
    (l₁.max l₂).inst levelSubst = (l₁.inst levelSubst).max (l₂.inst levelSubst) := rfl

@[simp] theorem inst_imax (levelSubst : Param ℓ → RawLevel ℓ₁) (l₁ l₂ : RawLevel ℓ) :
    (l₁.imax l₂).inst levelSubst = (l₁.inst levelSubst).imax (l₂.inst levelSubst) := rfl

@[simp] theorem inst_param (levelSubst : Param ℓ → RawLevel ℓ₁) (p : Param ℓ) : (param p).inst levelSubst = levelSubst p := rfl

@[simp] theorem inst_id (l : RawLevel ℓ) : l.inst param = l := by
  induction l <;> simp [*]

@[simp] theorem inst_inst (levelSubst₁ : Param ℓ → RawLevel ℓ₁)
    (levelSubst₂ : Param ℓ₁ → RawLevel ℓ₂) (l : RawLevel ℓ) :
    (l.inst levelSubst₁).inst levelSubst₂ =
      l.inst fun p => (levelSubst₁ p).inst levelSubst₂ := by
  induction l <;> simp [*]

end RawLevel

end Metalean
