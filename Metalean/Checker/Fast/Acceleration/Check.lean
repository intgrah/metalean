/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Extension
public import Metalean.Checker.Fast.Infer
public import Metalean.Checker.Fast.WF
public import Metalean.Frontend.Table

@[expose] public section

namespace Metalean.Checker.Fast

open Acceleration

open Frontend (Failure Table)

variable (F : FEnv)

/-- `p` is the position of `Nat` -/
structure NatSpec (p : Nat) : Prop where
  sig : ∃ I : FInductive, F[p]? = some (.inductive Nat.sig I)

def ConstHeadSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
  FEnv.Denotes F E →
  ∃ η : Head ζ (.const .def 0), ζ.lookup pos = some ⟨.const .def 0, η⟩

def inductiveSig (ι : IndSig) (pos : Nat) :
    Except Failure (PLift (∃ I : FInductive, F[pos]? = some (.inductive ι I))) :=
  match F[pos]? with
  | some (.inductive ι' I) =>
    if hι : ι' = ι then pure ⟨I, by rw [hι]⟩ else throw .internal
  | _ => throw .internal

def natSpec (t : Table) : Except Failure {p : Nat // NatSpec F p} := do
  let p ← t.ind ``Nat
  let ⟨hsig⟩ ← inductiveSig F Nat.sig p
  pure ⟨p, ⟨hsig⟩⟩

def natAt (p : Nat) : Except Failure (PLift (NatSpec F p)) := do
  let ⟨hsig⟩ ← inductiveSig F Nat.sig p
  pure ⟨⟨hsig⟩⟩

def NatOp.at {f : Nat → Nat → Nat} (op : NatOp F f) (p : Nat) :
    Except Failure (PLift (NatOpSpec F p op.pos f)) :=
  if h : op.nat = p then pure ⟨h ▸ op.spec⟩ else throw .internal

def BoolOp.at {f : Nat → Nat → Bool} (op : BoolOp F f) (p b : Nat) :
    Except Failure (PLift (BoolOpSpec F p b op.pos f)) :=
  if h : op.nat = p ∧ op.bool = b then pure ⟨h.1 ▸ h.2 ▸ op.spec⟩ else throw .internal

def constDef (pos : Nat) : Except Failure (PLift (∃ t v, F[pos]? = some (.def 0 t v))) :=
  match F[pos]? with
  | some (.def 0 t v) => pure ⟨t, v, rfl⟩
  | _ => throw .internal

variable {F}

theorem ConstHeadSpec.ofDef {pos : Nat} :
    (∃ t v, F[pos]? = some (.def 0 t v)) →
    ConstHeadSpec F pos :=
  fun ⟨_, _, hfe⟩ _ _ hF => FEnv.Denotes.lookup (E := ⟨_, _⟩) hF hfe rfl

end Metalean.Checker.Fast
