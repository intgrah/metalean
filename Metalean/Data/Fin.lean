/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Batteries.Data.Fin.Coding
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.NeZero

@[expose] public section

universe u v

namespace Fin

theorem emptyFun {α : Sort u} (f g : Fin 0 → α) : f = g :=
  funext nofun

@[elab_as_elim] def lastInduction
  {motive : {n : Nat} → Fin n → Sort u}
    (last : ∀ n, motive (last n))
    (cast : ∀ {n} (i : Fin n), motive i → motive i.castSucc)
    {n : Nat} (i : Fin n) :
    motive i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih =>
    cases i using lastCases with
    | last => exact last n
    | cast i => exact cast i (ih i)

instance {α : Type u} {n : Nat} : GetElem (Fin n → α) Nat α fun _ i => i < n where
  getElem f i h := f ⟨i, h⟩

instance {α : Type u} {n : Nat} : GetElem? (Fin n → α) Nat α fun _ i => i < n where
  getElem? f i := if h : i < n then some (f ⟨i, h⟩) else none

instance {α : Type u} {n : Nat} : LawfulGetElem (Fin n → α) Nat α fun _ i => i < n where
  getElem?_def f i h := by
    split <;> simp_all

@[simp] theorem getElem?_fun {α : Type u} {n : Nat} (f : Fin n → α) (i : Nat) :
    f[i]? = if h : i < n then some (f ⟨i, h⟩) else none := rfl

instance {α : Type u} {k : Nat} [DecidableEq α] : DecidableEq (Fin k → α) := fun f g =>
  if h : ∀ i, f i = g i then isTrue (funext h) else isFalse fun he => h fun _ => he ▸ rfl

theorem eq_zero_of_isEmpty {n : Nat} (h : IsEmpty (Fin n)) : n = 0 :=
  Nat.eq_zero_of_not_pos fun hn => h.elim ⟨0, hn⟩

theorem eq_one_of_unique {k : Nat} (s : Fin k) (h : ∀ s', s' = s) : k = 1 := by
  cases k with
  | zero => exact s.elim0
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      have h01 := (h 0).trans (h 1).symm
      simp at h01

theorem append_of_lt {α : Type u} {m k : Nat} (u : Fin m → α) (w : Fin k → α)
    (i : Fin (m + k)) (h : i.val < m) : append u w i = u ⟨i.val, h⟩ :=
  append_left u w ⟨i.val, h⟩

theorem snoc_of_lt {α : Type u} {k : Nat} (as : Fin k → α) (a : α) (i : Fin (k + 1))
    (h : i.val < k) : (snoc as a : Fin (k + 1) → α) i = as ⟨i.val, h⟩ := by
  cases i using lastCases with
  | last => simp at h
  | cast i =>
    rw [snoc_castSucc]
    rfl

@[simp] theorem append_zero_right {α : Type u} {m : Nat} (u : Fin m → α) (w : Fin 0 → α) :
    append u w = u :=
  funext fun i => append_left u w i

@[simp] theorem append_castLE_left {α : Sort u} {m n k : Nat}
    (u : Fin m → α) (v : Fin n → α) (h : k ≤ m) (i : Fin k) :
    append u v (i.castLE (h.trans (Nat.le_add_right _ _))) = u (i.castLE h) :=
  append_left u v (i.castLE h)

@[simp] theorem append_castLE_right {α : Sort u} {m n k : Nat}
    (u : Fin m → α) (v : Fin n → α) (h : k ≤ n) (i : Fin (m + k)) :
    append u v (i.castLE (Nat.add_le_add_left h m)) =
      append u (fun j => v (j.castLE h)) i := by
  cases i using addCases with
  | left i => exact (append_left u v i).trans (append_left u _ i).symm
  | right i => exact (append_right u v (i.castLE h)).trans (append_right u (fun j => v (j.castLE h)) i).symm

theorem append_comp {α : Type u} {β : Type v} {n m : Nat} (u : Fin m → α) (w : Fin n → α)
    (g : α → β) :
    (fun i => g (append u w i)) = append (fun i => g (u i)) fun i => g (w i) := by
  funext i
  cases i using addCases with
  | left i => rw [append_left, append_left]
  | right i => rw [append_right, append_right]

@[simp] theorem snoc_const {α : Sort u} (n : Nat) (a : α) :
    snoc (fun _ : Fin n => a) a = fun _ => a := by
  funext i
  cases i using lastCases <;> simp

end Fin
