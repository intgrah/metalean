/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.RawLevel.Decide
public import Mathlib.CategoryTheory.Types.Basic
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

abbrev Level (ℓ : Nat) := Quotient (RawLevel.setoid ℓ)

namespace Level

open CategoryTheory

variable {ℓ ℓ₁ ℓ₂ : Nat}

instance : DecidableEq (Level ℓ) := fun u v =>
  Quotient.recOnSubsingleton₂ u v fun a b =>
    decidable_of_iff (a ≈ b) ⟨Quotient.sound, Quotient.exact⟩

def zero : Level ℓ := ⟦RawLevel.zero⟧
def param (p : Param ℓ) : Level ℓ := ⟦RawLevel.param p⟧
def succ (u : Level ℓ) : Level ℓ :=
  Quotient.liftOn u (⟦RawLevel.succ ·⟧)
    fun _ _ h => Quotient.sound h.succ

def max (u v : Level ℓ) : Level ℓ :=
  Quotient.liftOn₂ u v (⟦RawLevel.max · ·⟧)
    fun _ _ _ _ ha hb => Quotient.sound (ha.max hb)

def imax (u v : Level ℓ) : Level ℓ :=
  Quotient.liftOn₂ u v (⟦RawLevel.imax · ·⟧)
    fun _ _ _ _ ha hb => Quotient.sound (ha.imax hb)

def one : Level ℓ := succ zero

def ofNat : Nat → Level ℓ
  | 0 => zero
  | n + 1 => succ (ofNat n)

def eval (ν : Param ℓ → Nat) (u : Level ℓ) : Nat :=
  Quotient.liftOn u (RawLevel.eval ν) fun _ _ h => h.eval ν

@[ext] theorem ext {u v : Level ℓ} (h : ∀ ν, eval ν u = eval ν v) : u = v := by
  induction u using Quotient.inductionOn with
  | h a =>
    induction v using Quotient.inductionOn with
    | h b => exact Quotient.sound (RawLevel.Equiv.of_eval h)

@[simp] theorem eval_zero (ν : Param ℓ → Nat) : eval ν zero = 0 := rfl
@[simp] theorem eval_param (ν : Param ℓ → Nat) (p : Param ℓ) : eval ν (param p) = ν p := rfl

@[simp] theorem eval_succ (ν : Param ℓ → Nat) (u : Level ℓ) :
    eval ν u.succ = eval ν u + 1 := by
  obtain ⟨u⟩ := u
  rfl

@[simp] theorem eval_max (ν : Param ℓ → Nat) (u v : Level ℓ) :
    eval ν (u.max v) = Nat.max (eval ν u) (eval ν v) := by
  obtain ⟨u⟩ := u
  obtain ⟨v⟩ := v
  rfl

@[simp] theorem eval_imax (ν : Param ℓ → Nat) (u v : Level ℓ) :
    eval ν (u.imax v) = Nat.imax (eval ν u) (eval ν v) := by
  obtain ⟨u⟩ := u
  obtain ⟨v⟩ := v
  rfl

@[simp] theorem eval_one (ν : Param ℓ → Nat) : eval ν (one : Level ℓ) = 1 := rfl

@[simp] theorem eval_ofNat (ν : Param ℓ → Nat) (n : Nat) : (ofNat n).eval ν = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofNat, ih]

@[simp] theorem succ_ne_zero (u : Level ℓ) : u.succ ≠ zero :=
  fun h => by simpa using congrArg (eval fun _ => 0) h

theorem imax_zero (u : Level ℓ) : u.imax zero = zero :=
  ext <| by simp

def instRaw (σ : Param ℓ → Level ℓ₁) : RawLevel ℓ → Level ℓ₁
  | .zero => zero
  | .param p => σ p
  | .succ u => (instRaw σ u).succ
  | .max u v => (instRaw σ u).max (instRaw σ v)
  | .imax u v => (instRaw σ u).imax (instRaw σ v)

private theorem eval_instRaw (σ : Param ℓ → Level ℓ₁) (ν : Param ℓ₁ → Nat)
    (u : RawLevel ℓ) :
    eval ν (instRaw σ u) = u.eval fun p => eval ν (σ p) := by
  induction u <;> simp! [*]

def inst (σ : Param ℓ → Level ℓ₁) (u : Level ℓ) : Level ℓ₁ :=
  Quotient.liftOn u (instRaw σ) fun a b h => ext fun ν => by
    rw [eval_instRaw, eval_instRaw]
    exact h.eval _

theorem mk_inst (σ : Param ℓ → RawLevel ℓ₁) (l : RawLevel ℓ) :
    ⟦l.inst σ⟧ = Level.inst (⟦σ ·⟧) ⟦l⟧ := by
  induction l with
  | zero | param => rfl
  | succ _ ih => exact congrArg succ ih
  | max _ _ ih₁ ih₂ => exact congrArg₂ max ih₁ ih₂
  | imax _ _ ih₁ ih₂ => exact congrArg₂ imax ih₁ ih₂

@[simp] theorem inst_zero (σ : Param ℓ → Level ℓ₁) : (zero : Level ℓ).inst σ = zero := rfl
@[simp] theorem inst_param (σ : Param ℓ → Level ℓ₁) (p : Param ℓ) : (param p).inst σ = σ p := rfl

@[simp] theorem inst_succ (σ : Param ℓ → Level ℓ₁) (u : Level ℓ) :
    u.succ.inst σ = (u.inst σ).succ := by
  obtain ⟨u⟩ := u
  rfl

@[simp] theorem inst_max (σ : Param ℓ → Level ℓ₁) (u v : Level ℓ) :
    (u.max v).inst σ = (u.inst σ).max (v.inst σ) := by
  obtain ⟨u⟩ := u
  obtain ⟨v⟩ := v
  rfl

@[simp] theorem inst_imax (σ : Param ℓ → Level ℓ₁) (u v : Level ℓ) :
    (u.imax v).inst σ = (u.inst σ).imax (v.inst σ) := by
  obtain ⟨u⟩ := u
  obtain ⟨v⟩ := v
  rfl

theorem eval_inst (σ : Param ℓ → Level ℓ₁) (ν : Param ℓ₁ → Nat) (u : Level ℓ) :
    eval ν (u.inst σ) = eval (eval ν ∘ σ) u := by
  obtain ⟨u⟩ := u
  exact eval_instRaw σ ν u

@[simp] theorem inst_id (u : Level ℓ) : u.inst param = u := by
  ext ν
  simp [eval_inst, Function.comp_def]

@[simp] theorem inst_inst (σ₁ : Param ℓ → Level ℓ₁) (σ₂ : Param ℓ₁ → Level ℓ₂) (u : Level ℓ) :
    (u.inst σ₁).inst σ₂ = u.inst fun p => (σ₁ p).inst σ₂ := by
  ext ν
  simp [eval_inst, Function.comp_def]

@[reducible] def category : SmallCategory Nat where
  Hom ℓ₁ ℓ₂ := Param ℓ₁ → Level ℓ₂
  id _ := param
  comp σ₁ σ₂ := fun p => (σ₁ p).inst σ₂
  id_comp _ := rfl
  comp_id σ := funext fun p => inst_id (σ p)
  assoc σ₁ σ₂ σ₃ := funext fun p => inst_inst σ₂ σ₃ (σ₁ p)

attribute [local instance] category in
@[reducible, functor] def functor : Nat ⥤ Type where
  obj := Level
  map σ := ↾inst σ
  map_id _ := ConcreteCategory.hom_ext _ _ inst_id
  map_comp σ₁ σ₂ := ConcreteCategory.hom_ext _ _ fun u => (inst_inst σ₁ σ₂ u).symm

end Level
end Metalean
