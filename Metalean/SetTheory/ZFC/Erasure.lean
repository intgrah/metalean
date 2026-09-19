/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Aczel
public import Metalean.SetTheory.ZFC.Universe.Sort

public section

namespace Metalean

open ZFSet

@[expose] def propVal (level : Nat) (value : ZFSet) : ZFSet := if level = 0 then proof else value

@[simp] theorem propVal_zero (value : ZFSet) : propVal 0 value = proof := ite_eq_left rfl

@[simp] theorem propVal_succ (level : Nat) (value : ZFSet) :
    propVal (level + 1) value = value :=
  ite_eq_right (Nat.succ_ne_zero level)

theorem propVal_of_ne_zero {level : Nat} (h : level ≠ 0) (value : ZFSet) :
    propVal level value = value :=
  ite_eq_right h

@[expose] noncomputable def propSet (level : Nat) (carrier : ZFSet) : ZFSet :=
  if level = 0 then squash carrier else carrier

@[simp] theorem propSet_zero (carrier : ZFSet) : propSet 0 carrier = squash carrier :=
  ite_eq_left rfl

@[simp] theorem propSet_succ (level : Nat) (carrier : ZFSet) :
    propSet (level + 1) carrier = carrier :=
  ite_eq_right (Nat.succ_ne_zero level)

theorem propVal_mem_propSet {level : Nat} {carrier value : ZFSet} (h : value ∈ carrier) :
    propVal level value ∈ propSet level carrier := by
  match level with
  | 0 => exact mem_squash.mpr ⟨value, h, rfl⟩
  | _ + 1 => exact h

noncomputable def propGet (level : Nat) (carrier value : ZFSet) : ZFSet :=
  if level = 0 then Classical.epsilon (· ∈ carrier) else value

theorem propGet_of_ne_zero {level : Nat} (h : level ≠ 0)
    (carrier value : ZFSet) : propGet level carrier value = value := by
  simp [propGet, h]

theorem propGet_mem {level : Nat} {carrier value : ZFSet}
    (h : value ∈ propSet level carrier) : propGet level carrier value ∈ carrier := by
  cases level with
  | zero =>
    have ⟨raw, hraw, _⟩ := mem_squash.mp h
    exact Classical.epsilon_spec ⟨raw, hraw⟩
  | succ level => simpa [propGet] using h

theorem propVal_propGet {level : Nat} {carrier value : ZFSet}
    (h : value ∈ propSet level carrier) :
    propVal level (propGet level carrier value) = value := by
  cases level with
  | zero =>
    have ⟨_, _, hvalue⟩ := mem_squash.mp h
    simpa using hvalue.symm
  | succ level => simp [propGet]

theorem propSet_mem_sort {level : Nat} {carrier : ZFSet}
    (h : ∀ k : Nat, level = k + 1 → carrier ∈ U_ k) :
    propSet level carrier ∈ S_ level := by
  match level with
  | 0 => exact squash_mem_truth carrier
  | _ + 1 => exact h _ rfl

theorem propSet_eq_self_of_mem_sort {level : Nat} {carrier : ZFSet}
    (h : carrier ∈ S_ level) : propSet level carrier = carrier := by
  cases level with
  | zero =>
    rcases mem_truth.mp h with rfl | rfl
    · exact squash_falsum
    · exact squash_eq_verum proof_mem_verum
  | succ level => simp

end Metalean
