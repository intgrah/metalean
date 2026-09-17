/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Basic
public import Metalean.RawLevel.Basic
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.FastChecker

inductive FLevel where
  | zero
  | succ (l : FLevel)
  | max (l₁ l₂ : FLevel)
  | imax (l₁ l₂ : FLevel)
  | param (p : Nat)
deriving DecidableEq, Hashable

namespace FLevel

def hasParam : FLevel → Bool
  | zero => false
  | succ l => l.hasParam
  | max l₁ l₂ | imax l₁ l₂ => l₁.hasParam || l₂.hasParam
  | param _ => true

def inst (us : Array FLevel) : FLevel → FLevel
  | zero => zero
  | succ l => succ (l.inst us)
  | max l₁ l₂ => max (l₁.inst us) (l₂.inst us)
  | imax l₁ l₂ => imax (l₁.inst us) (l₂.inst us)
  | param p => us[p]?.getD (param p)

def toRaw (ℓ : Nat) : FLevel → Option (RawLevel ℓ)
  | .zero => some .zero
  | .succ l => (l.toRaw ℓ).map .succ
  | .max l₁ l₂ => do pure (.max (← l₁.toRaw ℓ) (← l₂.toRaw ℓ))
  | .imax l₁ l₂ => do pure (.imax (← l₁.toRaw ℓ) (← l₂.toRaw ℓ))
  | .param p => if h : p < ℓ then some (.param ⟨p, h⟩) else none

variable {ℓ : Nat}

judgement Denotes : FLevel → RawLevel ℓ → Prop where

  ──────────────────── zero
  Denotes .zero .zero

  Denotes l l'
  ──────────────────── succ {l : FLevel} {l' : RawLevel ℓ}
  Denotes (.succ l) (.succ l')

  Denotes l₁ l₁'
  Denotes l₂ l₂'
  ──────────────────── max {l₁ l₂ : FLevel} {l₁' l₂' : RawLevel ℓ}
  Denotes (.max l₁ l₂) (.max l₁' l₂')

  Denotes l₁ l₁'
  Denotes l₂ l₂'
  ──────────────────── imax {l₁ l₂ : FLevel} {l₁' l₂' : RawLevel ℓ}
  Denotes (.imax l₁ l₂) (.imax l₁' l₂')

  ──────────────────── param {p : Nat} (h : p < ℓ)
  Denotes (.param p) (.param ⟨p, h⟩)

variable {ℓ' : Nat}

theorem Denotes.unique {l : FLevel} {l₁ l₂ : RawLevel ℓ} :
    Denotes l l₁ →
    Denotes l l₂ →
    l₁ = l₂
  | .zero, .zero => rfl
  | .succ h, .succ h' => by rw [h.unique h']
  | .max h₁ h₂, .max h₁' h₂' => by rw [h₁.unique h₁', h₂.unique h₂']
  | .imax h₁ h₂, .imax h₁' h₂' => by rw [h₁.unique h₁', h₂.unique h₂']
  | .param _, .param _ => rfl

theorem Denotes.inst {us : Array FLevel} {σ : Param ℓ → RawLevel ℓ'} (hus : us.size = ℓ)
    {l : FLevel} {l' : RawLevel ℓ} :
    Denotes l l' →
    (∀ i, Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (σ i)) →
    Denotes (l.inst us) (l'.inst σ)
  | .zero, _ => .zero
  | .succ h, hus' => .succ (h.inst hus hus')
  | .max h₁ h₂, hus' => .max (h₁.inst hus hus') (h₂.inst hus hus')
  | .imax h₁ h₂, hus' => .imax (h₁.inst hus hus') (h₂.inst hus hus')
  | .param (p := p) hp, hus' => by simpa! [hus, hp] using hus' ⟨p, hp⟩

theorem Denotes.inst_of_hasParam_eq_false {l : FLevel} {l' : RawLevel ℓ}
    (hp : l.hasParam = false) (σ : Param ℓ → RawLevel ℓ') :
    Denotes l l' →
    Denotes l (l'.inst σ) := by
  intro h
  induction h with
  | zero => exact .zero
  | succ _ ih => exact .succ (ih hp)
  | max _ _ ih₁ ih₂ =>
    simp only [hasParam, Bool.or_eq_false_iff] at hp
    exact .max (ih₁ hp.1) (ih₂ hp.2)
  | imax _ _ ih₁ ih₂ =>
    simp only [hasParam, Bool.or_eq_false_iff] at hp
    exact .imax (ih₁ hp.1) (ih₂ hp.2)
  | param => cases hp

theorem toRaw_eq_of_denotes {ℓ : Nat} {l : FLevel} {l' : RawLevel ℓ} :
    Denotes l l' →
    toRaw ℓ l = some l'
  | .zero => rfl
  | .succ h => by simp [toRaw, toRaw_eq_of_denotes h]
  | .max h₁ h₂ => by simp [toRaw, toRaw_eq_of_denotes h₁, toRaw_eq_of_denotes h₂]
  | .imax h₁ h₂ => by simp [toRaw, toRaw_eq_of_denotes h₁, toRaw_eq_of_denotes h₂]
  | .param h => by simp [toRaw, h]

def isNotZero : FLevel → Bool
  | zero => false
  | succ _ => true
  | max l₁ l₂ => l₁.isNotZero || l₂.isNotZero
  | imax _ l₂ => l₂.isNotZero
  | param _ => false

theorem Denotes.one_le_of_isNotZero {fl : FLevel} {l : RawLevel ℓ} (hl : fl.isNotZero = true)
    (ν : Param ℓ → Nat) :
    Denotes fl l →
    1 ≤ l.eval ν := by
  intro h
  induction h with
  | zero => cases hl
  | succ _ _ => simp
  | max _ _ ih₁ ih₂ =>
    simp only [isNotZero, Bool.or_eq_true] at hl
    rcases hl with hl | hl
    · exact (ih₁ hl).trans (by simp)
    · exact (ih₂ hl).trans (by simp)
  | imax _ _ _ ih₂ =>
    have := ih₂ hl
    simp only [RawLevel.eval_imax, Nat.imax]
    rw [ite_eq_right (by omega)]
    exact this.trans (Nat.le_max_right _ _)
  | param => cases hl

def nonZeroWhenPositive : FLevel → Bool
  | zero => false
  | succ _ => true
  | max l₁ l₂ => l₁.nonZeroWhenPositive || l₂.nonZeroWhenPositive
  | imax _ l₂ => l₂.nonZeroWhenPositive
  | param _ => true

def alwaysZero : FLevel → Bool
  | zero => true
  | succ _ => false
  | max l₁ l₂ => l₁.alwaysZero && l₂.alwaysZero
  | imax _ l₂ => l₂.alwaysZero
  | param _ => false

theorem Denotes.eval_eq_zero {fl : FLevel} {l : RawLevel ℓ} (hl : fl.alwaysZero = true)
    (ν : Param ℓ → Nat) :
    Denotes fl l →
    l.eval ν = 0 := by
  intro h
  induction h with
  | zero => rfl
  | succ _ _ => cases hl
  | max _ _ ih₁ ih₂ =>
    simp only [alwaysZero, Bool.and_eq_true] at hl
    simp [ih₁ hl.1, ih₂ hl.2]
  | imax _ _ _ ih₂ => simp [Nat.imax, ih₂ hl]
  | param => cases hl

theorem Denotes.interp_eq_zero {fl : FLevel} {l : RawLevel ℓ} (hl : fl.alwaysZero = true) :
    Denotes fl l →
    (⟦l⟧ : Level ℓ) = Level.zero :=
  fun h => Level.ext fun ν => h.eval_eq_zero hl ν

theorem Denotes.eq_zero {l : RawLevel ℓ} :
    Denotes .zero l →
    l = .zero
  | .zero => rfl

def params (nlevels : Nat) : Array FLevel :=
  Array.ofFn fun i : Fin nlevels => .param i.val

@[simp] theorem size_params (nlevels : Nat) : (params nlevels).size = nlevels := by
  simp [FLevel.params]

theorem denotes_params {nlevels : Nat} (i : Fin nlevels) :
    FLevel.Denotes ((params nlevels)[i.val]'(by simp)) (.param i) := by
  simp only [FLevel.params, Array.getElem_ofFn]
  exact .param i.isLt

end FLevel

def LevelWF (ℓ : Nat) (l : FLevel) : Prop :=
  ∃ l' : RawLevel ℓ, FLevel.Denotes l l'

theorem LevelWF.choose {ℓ m : Nat} {ls : Array FLevel} (hls : ls.size = m) :
    (∀ i (hi : i < ls.size), LevelWF ℓ ls[i]) →
    ∃ ls' : Fin m → RawLevel ℓ, ∀ i, FLevel.Denotes (ls[i.val]'(hls.symm ▸ i.isLt)) (ls' i) :=
  fun h => Classical.axiomOfChoice fun i : Fin m => h i.val (hls.symm ▸ i.isLt)

end Metalean.FastChecker
