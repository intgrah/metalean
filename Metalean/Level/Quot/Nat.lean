/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public section

namespace Nat

variable {k n m : Nat}

@[expose] def imax (n m : Nat) : Nat :=
  if m = 0 then 0 else Nat.max n m

@[simp] theorem imax_zero_right : imax n 0 = 0 := ite_eq_left rfl

@[simp] theorem imax_succ_right : imax n (m + 1) = Nat.max n (m + 1) :=
  ite_eq_right (Nat.succ_ne_zero m)

theorem imax_eq_max (h : m ≠ 0) : imax n m = Nat.max n m := ite_eq_right h

theorem le_imax_right : m ≤ imax n m :=
  match m with
  | zero => Nat.le_refl 0
  | succ m => imax_succ_right ▸ Nat.le_max_right n (m + 1)

theorem imax_le_iff : imax n m ≤ k ↔ m ≠ 0 → n ≤ k ∧ m ≤ k := by
  cases m with simp [Nat.max_le]

theorem imax_le (h₁ : n ≤ k) (h₂ : m ≤ k) : imax n m ≤ k :=
  imax_le_iff.mpr fun _ => ⟨h₁, h₂⟩

theorem le_of_imax_le (h : imax n m ≤ k) (hm : m ≠ 0) : n ≤ k :=
  (imax_le_iff.mp h hm).1

@[simp] theorem imax_zero_left : imax 0 m = m :=
  Nat.le_antisymm (imax_le (Nat.zero_le m) (Nat.le_refl m)) le_imax_right

@[simp] theorem imax_self : imax n n = n :=
  Nat.le_antisymm (imax_le (Nat.le_refl n) (Nat.le_refl n)) le_imax_right

@[simp] theorem imax_eq_zero_iff : imax n m = 0 ↔ m = 0 :=
  ⟨fun h => Nat.le_zero.mp (h ▸ le_imax_right), fun h => by simp [h]⟩

end Nat
