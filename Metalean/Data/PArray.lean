/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

/-! # Better array implementation -/

public section

universe u

namespace Metalean

def PArray.chunkSize : Nat := 256

structure PArray (α : Type u) where
  chunks : Array (Array α)
  tail : Array α
  chunks_size : ∀ c ∈ chunks, c.size = PArray.chunkSize
  tail_size : tail.size < PArray.chunkSize

namespace PArray

variable {α : Type u}

def empty : PArray α where
  chunks := #[]
  tail := #[]
  chunks_size := by simp
  tail_size := by simp [chunkSize]

instance : EmptyCollection (PArray α) := ⟨empty⟩

def size (a : PArray α) : Nat :=
  a.chunks.size * chunkSize + a.tail.size

def get? (a : PArray α) (i : Nat) : Option α :=
  if i / chunkSize < a.chunks.size then a.chunks[i / chunkSize]?.bind (·[i % chunkSize]?)
  else if i / chunkSize = a.chunks.size then a.tail[i % chunkSize]?
  else none

def push (x : α) : PArray α → PArray α
  | ⟨chunks, tail, hc, ht⟩ =>
    if h : tail.size + 1 = chunkSize then
      { chunks := chunks.push (tail.push x)
        tail := #[]
        chunks_size := by
          intro c hc'
          rcases Array.mem_push.mp hc' with hc' | rfl
          · exact hc c hc'
          · simpa using h
        tail_size := by simp [chunkSize] }
    else
      { chunks
        tail := tail.push x
        chunks_size := hc
        tail_size := by simp; omega }

theorem get?_isSome (a : PArray α) {i : Nat} (h : i < a.size) : (a.get? i).isSome := by
  have hC : chunkSize = 256 := rfl
  have hdm := Nat.div_add_mod i 256
  have hml := Nat.mod_lt i (show 256 > 0 by decide)
  unfold get?
  rw [hC]
  unfold size at h
  rw [hC] at h
  generalize i / 256 = q at *
  generalize i % 256 = r at *
  subst hdm
  by_cases hq : q < a.chunks.size
  · have hc := a.chunks_size _ (Array.getElem_mem hq)
    rw [hC] at hc
    simp [hq, Array.getElem?_eq_getElem (hc ▸ hml : r < _)]
  · have ht := a.tail_size
    rw [hC] at ht
    have hq' : q = a.chunks.size := by omega
    have hr : r < a.tail.size := by subst hq'; omega
    simp [hq', Array.getElem?_eq_getElem hr]

instance : GetElem? (PArray α) Nat α fun a i => i < a.size where
  getElem a i h := (a.get? i).get (a.get?_isSome h)
  getElem? a i := a.get? i

theorem lt_size_of_getElem? {a : PArray α} {i : Nat} {x : α} (h : a[i]? = some x) :
    i < a.size := by
  change a.get? i = some x at h
  have hC : chunkSize = 256 := rfl
  have hdm := Nat.div_add_mod i 256
  have ht := a.tail_size
  unfold get? at h
  unfold size
  rw [hC] at h ht ⊢
  generalize i / 256 = q at *
  generalize i % 256 = r at *
  subst hdm
  by_cases hq : q < a.chunks.size
  · have hc := a.chunks_size _ (Array.getElem_mem hq)
    rw [hC] at hc
    simp only [hq, ↓reduceIte, Array.getElem?_eq_getElem hq, Option.bind_some] at h
    have hr := (Array.getElem?_eq_some_iff.mp h).1
    omega
  · by_cases hq' : q = a.chunks.size
    · simp only [hq', Nat.lt_irrefl, ↓reduceIte] at h
      have hr := (Array.getElem?_eq_some_iff.mp h).1
      omega
    · simp [hq, hq'] at h

@[simp] theorem getElem?_empty (i : Nat) : (∅ : PArray α)[i]? = none := by
  show empty.get? i = none
  simp [empty, get?]

@[simp] theorem size_empty : (∅ : PArray α).size = 0 := by
  simp [EmptyCollection.emptyCollection, empty, size]

@[simp] theorem size_push (a : PArray α) (x : α) : (a.push x).size = a.size + 1 := by
  cases a with
  | mk chunks tail hc ht =>
    simp only [push]
    split
    · next h => simp [size, chunkSize] at h ⊢; omega
    · simp [size]; omega

theorem getElem?_push (a : PArray α) (x : α) (i : Nat) :
    (a.push x)[i]? = if i = a.size then some x else a[i]? := by
  show (a.push x).get? i = if i = a.size then some x else a.get? i
  cases a with
  | mk chunks tail hc ht =>
    have hC : chunkSize = 256 := rfl
    have hdm := Nat.div_add_mod i 256
    have hml := Nat.mod_lt i (show 256 > 0 by decide)
    simp only [push, get?, size, hC] at ht ⊢
    generalize i / 256 = q at *
    generalize i % 256 = r at *
    subst hdm
    by_cases h : tail.size + 1 = 256
    · simp only [h, ↓reduceDIte, Array.size_push]
      rcases Nat.lt_trichotomy q chunks.size with hq | rfl | hq
      · have hne : 256 * q + r ≠ chunks.size * 256 + tail.size := by omega
        simp [hq, Nat.lt_succ_of_lt hq, hne, Array.getElem_push_lt hq]
      · have hiff : (256 * chunks.size + r = chunks.size * 256 + tail.size) ↔ r = tail.size := by
          omega
        simp [hiff, Array.getElem?_push]
      · have hne : 256 * q + r ≠ chunks.size * 256 + tail.size := by omega
        have hq' : ¬q < chunks.size + 1 := by omega
        simp [hq', Nat.not_lt_of_gt hq, Nat.ne_of_gt hq, hne]
    · simp only [h, ↓reduceDIte]
      rcases Nat.lt_trichotomy q chunks.size with hq | rfl | hq
      · have hne : 256 * q + r ≠ chunks.size * 256 + tail.size := by omega
        simp [hq, hne]
      · have hiff : (256 * chunks.size + r = chunks.size * 256 + tail.size) ↔ r = tail.size := by
          omega
        simp [hiff, Array.getElem?_push]
      · have hne : 256 * q + r ≠ chunks.size * 256 + tail.size := by omega
        simp [Nat.not_lt_of_gt hq, Nat.ne_of_gt hq, hne]

theorem getElem?_eq_none {a : PArray α} {i : Nat} (h : a.size ≤ i) : a[i]? = none := by
  cases hget : a[i]? with
  | none => rfl
  | some x => exact absurd (lt_size_of_getElem? hget) (Nat.not_lt.mpr h)

instance : LawfulGetElem (PArray α) Nat α fun a i => i < a.size where
  getElem?_def a i _ := by
    split
    · next h => exact (Option.some_get (a.get?_isSome h)).symm
    · next h => exact getElem?_eq_none (Nat.not_lt.mp h)

theorem push_inj {a b : PArray α} {x y : α} (h : a.push x = b.push y) : a = b ∧ x = y := by
  cases a with
  | mk chunks tail hc ht =>
  cases b with
  | mk chunks' tail' hc' ht' =>
    simp only [push] at h
    split at h <;> split at h
    · have ⟨h₁, h₂⟩ := PArray.mk.inj h
      have ⟨h₃, h₄⟩ := Array.push_eq_push.mp h₁
      have ⟨h₅, h₆⟩ := Array.push_eq_push.mp h₃
      subst h₄ h₆
      exact ⟨rfl, h₅⟩
    · have := congrArg Array.size (PArray.mk.inj h).2
      simp at this
    · have := congrArg Array.size (PArray.mk.inj h).2
      simp at this
    · have ⟨h₁, h₂⟩ := PArray.mk.inj h
      have ⟨h₃, h₄⟩ := Array.push_eq_push.mp h₂
      subst h₁ h₄
      exact ⟨rfl, h₃⟩

end PArray

end Metalean
