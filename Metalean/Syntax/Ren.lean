/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Var
public import Mathlib.CategoryTheory.Types.Basic
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {m n k : Nat}

@[reducible] def Ren (m n : Nat) : Type := Var m → Var n

namespace Ren

def id : Ren n n := fun v => v
def comp (ρ₂ : Ren n k) (ρ₁ : Ren m n) : Ren m k := fun v => ρ₂ (ρ₁ v)

@[reducible] def category : SmallCategory Nat where
  Hom := Ren
  id _ := id
  comp ρ₁ ρ₂ := comp ρ₂ ρ₁

attribute [local instance] category in
@[reducible, functor] def functor : Nat ⥤ Type where
  obj := Var
  map ρ := ↾ρ

def lift (ρ : Ren m n) : Ren (m + 1) (n + 1) := fun v =>
  if h : v.val < m then (ρ ⟨v.val, h⟩).castSucc else Fin.last n

@[simp] theorem lift_castSucc (ρ : Ren m n) (v : Var m) :
    ρ.lift v.castSucc = (ρ v).castSucc := by
  simp [lift]

@[simp] theorem lift_last (ρ : Ren m n) :
    ρ.lift (Fin.last m) = Fin.last n := by
  simp [lift]

def wkFrom (cut : Nat) : Ren n (n + 1) := fun v =>
  if _ : v.val < cut then v.castSucc else v.succ

@[simp] theorem wkFrom_of_lt {cut : Nat} (v : Var n) (h : v.val < cut) :
    wkFrom cut v = v.castSucc := by
  simp [wkFrom, h]

@[simp] theorem wkFrom_of_ge {cut : Nat} (v : Var n) (h : cut ≤ v.val) :
    wkFrom cut v = v.succ := by
  simp [wkFrom, show ¬v.val < cut by omega]

def wkN (k : Nat) : Ren n (n + k) := Fin.castAdd k

def liftN (ρ : Ren m n) : (k : Nat) → Ren (m + k) (n + k)
  | 0 => ρ
  | k + 1 => (ρ.liftN k).lift

@[simp] theorem lift_id : (Ren.id : Ren n n).lift = Ren.id := by
  funext v
  cases v using Fin.lastCases <;> simp [id]

@[simp] theorem liftN_id (k : Nat) : (Ren.id : Ren n n).liftN k = Ren.id := by
  induction k with
  | zero => rfl
  | succ k ih => rw [liftN, ih, lift_id]

@[simp] theorem lift_comp (ρ₂ : Ren n k) (ρ₁ : Ren m n) :
    (ρ₂.comp ρ₁).lift = ρ₂.lift.comp ρ₁.lift := by
  funext v
  by_cases h : v.val < m
  · have hr := (ρ₁ ⟨v.val, h⟩).isLt
    simp [comp, lift, h]
  · obtain rfl : v = Fin.last m := Fin.ext (by simp; omega)
    simp [comp]

attribute [local instance] category in
@[reducible, functor] def successor : Nat ⥤ Nat where
  obj n := n + 1
  map := lift
  map_id _ := lift_id
  map_comp ρ₁ ρ₂ := lift_comp ρ₂ ρ₁

@[simp] theorem liftN_comp (ρ₂ : Ren n k) (ρ₁ : Ren m n) (count : Nat) :
    (ρ₂.comp ρ₁).liftN count = (ρ₂.liftN count).comp (ρ₁.liftN count) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [liftN, liftN, liftN, ih, lift_comp]

@[simp] theorem wkFrom_lift (cut : Nat) (h : cut ≤ n) :
    (wkFrom cut : Ren n (n + 1)).lift =
      (wkFrom cut : Ren (n + 1) (n + 1 + 1)) := by
  funext v
  simp [wkFrom, lift]
  split <;> split <;> ext <;> simp_all <;> omega

@[simp] theorem lift_comp_wkFrom (ρ : Ren n k) :
    ρ.lift.comp (wkFrom n) = (wkFrom k).comp ρ := by
  funext v
  simp [comp]

theorem wkFrom_comm {cut₁ cut₂ : Nat} (h : cut₁ ≤ cut₂) :
    (wkFrom cut₁ : Ren (n + 1) (n + 2)).comp (wkFrom cut₂ : Ren n (n + 1)) =
      (wkFrom (cut₂ + 1) : Ren (n + 1) (n + 2)).comp
        (wkFrom cut₁ : Ren n (n + 1)) := by
  funext v
  simp [comp, wkFrom]
  split <;> split <;> split <;> split <;> simp_all <;> omega

end Ren

end Metalean
