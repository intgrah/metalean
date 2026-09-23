/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Level
public import Metalean.Level.Quot.Basic
public import Metalean.Level.Raw.Normalize
public import Metalean.Control
public import Metalean.Frontend.Failure

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

section

variable (ℓ : Nat)

def LevelEqSpec (l₁ l₂ : FLevel) : Prop :=
  ∀ {l₁' l₂' : RawLevel ℓ},
  FLevel.Denotes l₁ l₁' →
  FLevel.Denotes l₂ l₂' →
  (⟦l₁'⟧ : Level ℓ) = ⟦l₂'⟧

end

def checkLevel (ℓ : Nat) :
    (l : FLevel) → Except Failure {l' : RawLevel ℓ // FLevel.Denotes l l'}
  | .zero => pure ⟨.zero, .zero⟩
  | .succ l => do
    let ⟨l', h⟩ ← checkLevel ℓ l
    pure ⟨.succ l', .succ h⟩
  | .max l₁ l₂ => do
    let ⟨l₁', h₁⟩ ← checkLevel ℓ l₁
    let ⟨l₂', h₂⟩ ← checkLevel ℓ l₂
    pure ⟨.max l₁' l₂', .max h₁ h₂⟩
  | .imax l₁ l₂ => do
    let ⟨l₁', h₁⟩ ← checkLevel ℓ l₁
    let ⟨l₂', h₂⟩ ← checkLevel ℓ l₂
    pure ⟨.imax l₁' l₂', .imax h₁ h₂⟩
  | .param p =>
    if h : p < ℓ then pure ⟨.param ⟨p, h⟩, .param h⟩ else throw (.reject .unknownLevelParam)

def FLevel.isZero (ℓ : Nat) (l : FLevel) : Except Failure Bool :=
  match l.toRaw ℓ with
  | some _ => pure !l.nonZeroWhenPositive
  | none => throw (.reject .unknownLevelParam)

def checkLevels (ℓ : Nat) (ls : Array FLevel) :
    Except Failure (PLift (∀ i (h : i < ls.size), LevelWF ℓ ls[i])) :=
  Array.forallM ls (fun i h => LevelWF ℓ ls[i]) fun i h => do
    let ⟨_, hl⟩ ← checkLevel ℓ (ls[i]'h)
    pure ⟨_, hl⟩

def isDefEqLevel (ℓ : Nat) (l₁ l₂ : FLevel) : Except Failure (PLift (LevelEqSpec ℓ l₁ l₂)) := do
  if h : l₁ = l₂ then
    return ⟨fun h₁ h₂ => by subst h; rw [h₁.unique h₂]⟩
  let ⟨l₁', h₁⟩ ← checkLevel ℓ l₁
  let ⟨l₂', h₂⟩ ← checkLevel ℓ l₂
  if hn : l₁'.normalize = l₂'.normalize then
    return ⟨fun h₁' h₂' => by
      rw [← h₁.unique h₁', ← h₂.unique h₂']
      exact Quotient.sound
        ((RawLevel.normalize_equiv l₁').symm.trans (hn ▸ RawLevel.normalize_equiv l₂'))⟩
  let ⟨heq⟩ ← guardProofOr ((⟦l₁'⟧ : Level ℓ) = ⟦l₂'⟧) (.reject .notDefEq)
  pure ⟨fun h₁' h₂' => by rw [h₁.unique h₁', h₂.unique h₂'] at heq; exact heq⟩
end Metalean.FastChecker
