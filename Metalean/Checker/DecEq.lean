/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Control
public import Metalean.Frontend.Failure
public import Metalean.Syntax.Inductive.Basic
import Metalean.Meta.IfRfl

@[expose] public section

namespace Metalean

open Frontend (Failure)

variable {ζ : Sigs} {ℓ : Nat}

def Head.decEq? {ζ : Sigs} {sig₁ sig₂ : Sig} :
    (η₁ : Head ζ sig₁) → (η₂ : Head ζ sig₂) →
    Except Failure (PLift (sig₁ = sig₂ ∧ η₁ ≍ η₂))
  | .here, .here => pure ⟨rfl, HEq.rfl⟩
  | .there η₁, .there η₂ => do
    let ⟨rfl, rfl⟩ ← decEq? η₁ η₂
    pure ⟨rfl, HEq.rfl⟩
  | _, _ => throw (.reject .notDefEq)

def Head.indDecEq? {ι₁ ι₂ : IndSig} (η₁ : Head ζ (.inductive ι₁))
    (η₂ : Head ζ (.inductive ι₂)) :
    Except Failure (PLift (ι₁ = ι₂ ∧ η₁ ≍ η₂)) := do
  let ⟨_, heq⟩ ← η₁.decEq? η₂
  let ⟨rfl⟩ ← guardProofOr (ι₁ = ι₂) (.reject .notDefEq)
  pure ⟨rfl, heq⟩

def Expr.decEq? {n : Nat} : (e₁ e₂ : Expr ζ ℓ n) → Except Failure (PLift (e₁ = e₂))
  | .var v₁, .var v₂ => do
    let ⟨rfl⟩ ← guardProofOr (v₁ = v₂) (.reject .notDefEq)
    pure ⟨rfl⟩
  | .sort l₁, .sort l₂ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    pure ⟨rfl⟩
  | .const (kind := kind₁) (nlevels := nlevels₁) η₁ ls₁,
      .const (kind := kind₂) (nlevels := nlevels₂) η₂ ls₂ => do
    let ⟨rfl⟩ ← guardProofOr (kind₁ = kind₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (nlevels₁ = nlevels₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η₁ = η₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls₁ = ls₂) (.reject .notDefEq)
    pure ⟨rfl⟩
  | .ind η₁ s₁ ls₁ ps₁ is₁, .ind η₂ s₂ ls₂ ps₂ is₂ => do
    let ⟨rfl, rfl⟩ ← η₁.indDecEq? η₂
    let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls₁ = ls₂) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p => (ps₁ p).decEq? (ps₂ p)
    let ⟨his⟩ ← Fin.sequenceM fun i => (is₁ i).decEq? (is₂ i)
    pure ⟨by rw [funext hps, funext his]⟩
  | .ctor η₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁, .ctor η₂ s₂ c₂ ls₂ ps₂ fds₂ recFds₂ => do
    let ⟨rfl, rfl⟩ ← η₁.indDecEq? η₂
    let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (c₁ = c₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls₁ = ls₂) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p => (ps₁ p).decEq? (ps₂ p)
    let ⟨hfds⟩ ← Fin.sequenceM fun f => (fds₁ f).decEq? (fds₂ f)
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f => (recFds₁ f).decEq? (recFds₂ f)
    pure ⟨by rw [funext hps, funext hfds, funext hrecFds]⟩
  | .recr η₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁, .recr η₂ s₂ ls₂ l₂ ps₂ ms₂ mins₂ is₂ maj₂ => do
    let ⟨rfl, rfl⟩ ← η₁.indDecEq? η₂
    let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls₁ = ls₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p => (ps₁ p).decEq? (ps₂ p)
    let ⟨hms⟩ ← Fin.sequenceM fun t => (ms₁ t).decEq? (ms₂ t)
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c => (mins₁ t c).decEq? (mins₂ t c)
    let ⟨his⟩ ← Fin.sequenceM fun i => (is₁ i).decEq? (is₂ i)
    let ⟨rfl⟩ ← maj₁.decEq? maj₂
    pure ⟨by rw [funext hps, funext hms, funext₂ hmins, funext his]⟩
  | .quot η₁ l₁ α₁ r₁, .quot η₂ l₂ α₂ r₂ => do
    let ⟨rfl⟩ ← guardProofOr (η₁ = η₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← α₁.decEq? α₂
    let ⟨rfl⟩ ← r₁.decEq? r₂
    pure ⟨rfl⟩
  | .quotMk η₁ l₁ α₁ r₁ e₁, .quotMk η₂ l₂ α₂ r₂ e₂ => do
    let ⟨rfl⟩ ← guardProofOr (η₁ = η₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← α₁.decEq? α₂
    let ⟨rfl⟩ ← r₁.decEq? r₂
    let ⟨rfl⟩ ← e₁.decEq? e₂
    pure ⟨rfl⟩
  | .quotLift η₁ l₁ l₂ α₁ r₁ β₁ f₁ h₁ e₁,
      .quotLift η₂ l₁' l₂' α₂ r₂ β₂ f₂ h₂ e₂ => do
    let ⟨rfl⟩ ← guardProofOr (η₁ = η₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₁') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₂ = l₂') (.reject .notDefEq)
    let ⟨rfl⟩ ← α₁.decEq? α₂
    let ⟨rfl⟩ ← r₁.decEq? r₂
    let ⟨rfl⟩ ← β₁.decEq? β₂
    let ⟨rfl⟩ ← f₁.decEq? f₂
    let ⟨rfl⟩ ← h₁.decEq? h₂
    let ⟨rfl⟩ ← e₁.decEq? e₂
    pure ⟨rfl⟩
  | .quotInd η₁ l₁ α₁ r₁ β₁ f₁ e₁, .quotInd η₂ l₂ α₂ r₂ β₂ f₂ e₂ => do
    let ⟨rfl⟩ ← guardProofOr (η₁ = η₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← α₁.decEq? α₂
    let ⟨rfl⟩ ← r₁.decEq? r₂
    let ⟨rfl⟩ ← β₁.decEq? β₂
    let ⟨rfl⟩ ← f₁.decEq? f₂
    let ⟨rfl⟩ ← e₁.decEq? e₂
    pure ⟨rfl⟩
  | .app f₁ a₁, .app f₂ a₂ => do
    let ⟨rfl⟩ ← f₁.decEq? f₂
    let ⟨rfl⟩ ← a₁.decEq? a₂
    pure ⟨rfl⟩
  | .lam t₁ e₁', .lam t₂ e₂' => do
    let ⟨rfl⟩ ← t₁.decEq? t₂
    let ⟨rfl⟩ ← e₁'.decEq? e₂'
    pure ⟨rfl⟩
  | .forallE t₁ t₁', .forallE t₂ t₂' => do
    let ⟨rfl⟩ ← t₁.decEq? t₂
    let ⟨rfl⟩ ← t₁'.decEq? t₂'
    pure ⟨rfl⟩
  | .letE t₁ v₁ e₁', .letE t₂ v₂ e₂' => do
    let ⟨rfl⟩ ← t₁.decEq? t₂
    let ⟨rfl⟩ ← v₁.decEq? v₂
    let ⟨rfl⟩ ← e₁'.decEq? e₂'
    pure ⟨rfl⟩
  | _, _ => throw (.reject .notDefEq)

def Ctx.decEq? {a b : Nat} : (Δ₁ Δ₂ : Ctx ζ ℓ a b) → Except Failure (PLift (Δ₁ = Δ₂))
  | .nil, .nil => pure ⟨rfl⟩
  | .snoc Δ₁ t₁, .snoc Δ₂ t₂ => do
    let ⟨rfl⟩ ← Δ₁.decEq? Δ₂
    let ⟨rfl⟩ ← t₁.decEq? t₂
    pure ⟨rfl⟩
  | _, _ => throw (.reject .notDefEq)

variable {ι : IndSig}

def Field.decEq? {nfields : Nat} :
    (fd₁ fd₂ : Field ζ ι nfields) → Except Failure (PLift (fd₁ = fd₂))
  | ⟨t₁, l₁⟩, ⟨t₂, l₂⟩ => do
    let ⟨rfl⟩ ← t₁.decEq? t₂
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    pure ⟨rfl⟩

def RecField.decEq? {nfields arity : Nat} {target : Fin ι.nsorts} :
    (fd₁ fd₂ : RecField ζ ι nfields arity target) → Except Failure (PLift (fd₁ = fd₂))
  | ⟨tele₁, is₁⟩, ⟨tele₂, is₂⟩ => do
    let ⟨rfl⟩ ← tele₁.decEq? tele₂
    let ⟨his⟩ ← Fin.sequenceM fun i => (is₁ i).decEq? (is₂ i)
    pure ⟨by rw [funext his]⟩

def Ctor.decEq? {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
    (ctor₁ ctor₂ : Ctor ζ ι s csig) : Except Failure (PLift (ctor₁ = ctor₂)) := do
  let ⟨hordinary⟩ ← Fin.sequenceM fun f => (ctor₁.ordinary f).decEq? (ctor₂.ordinary f)
  let ⟨hrecursive⟩ ← Fin.sequenceM fun f => (ctor₁.recursive f).decEq? (ctor₂.recursive f)
  let ⟨htarget⟩ ← Fin.sequenceM fun i =>
    (ctor₁.targetIndices i).decEq? (ctor₂.targetIndices i)
  pure ⟨by
    change (⟨ctor₁.ordinary, ctor₁.recursive, ctor₁.targetIndices⟩ : Ctor ζ ι s csig) =
      ⟨ctor₂.ordinary, ctor₂.recursive, ctor₂.targetIndices⟩
    rw [funext hordinary, funext hrecursive, funext htarget]⟩

def Inductive.decEq? (I₁ I₂ : Inductive ζ ι) : Except Failure (PLift (I₁ = I₂)) := do
  let ⟨hparams⟩ ← I₁.params.decEq? I₂.params
  let ⟨hindices⟩ ← Fin.sequenceM fun s => (I₁.indices s).decEq? (I₂.indices s)
  let ⟨hctors⟩ ← Fin.sequenceM fun s =>
    Fin.sequenceM fun c => (I₁.ctors s c).decEq? (I₂.ctors s c)
  let ⟨hlevel⟩ ← guardProofOr (I₁.level = I₂.level) (.reject .notDefEq)
  pure ⟨by
    change (⟨I₁.params, I₁.indices, I₁.level, I₁.ctors⟩ : Inductive ζ ι) =
      ⟨I₂.params, I₂.indices, I₂.level, I₂.ctors⟩
    rw [hparams, funext hindices, hlevel, funext₂ hctors]⟩

end Metalean
