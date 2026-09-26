/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.LiteralRec

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace Beq

variable (p b pos : Nat)

example : Nat.beq Nat.zero Nat.zero = true := rfl

def zeroZero : Schema :=
  schema% ⊢ op₂ pos (zero p) (zero p) ≡ boolLit b true : bool b

example (y : Nat) : Nat.beq Nat.zero (Nat.succ y) = false := rfl

def zeroSucc : Schema :=
  schema% (y : nat p) ⊢ op₂ pos (zero p) (succ p y) ≡ boolLit b false : bool b

example (x : Nat) : Nat.beq (Nat.succ x) Nat.zero = false := rfl

def succZero : Schema :=
  schema% (x : nat p) ⊢ op₂ pos (succ p x) (zero p) ≡ boolLit b false : bool b

example (x y : Nat) : Nat.beq (Nat.succ x) (Nat.succ y) = Nat.beq x y := rfl

def succSucc : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos (succ p x) (succ p y) ≡ op₂ pos x y : bool b

variable (F : FEnv)

structure Spec : Prop where
  zeroZero : (zeroZero p b pos).Spec F
  zeroSucc : (zeroSucc p b pos).Spec F
  succZero : (succZero p b pos).Spec F
  succSucc : (succSucc p b pos).Spec F
  opCongr : (LiteralRec.boolOpCongr p b pos).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p b pos F)) := do
  let ⟨zeroZero⟩ ← (zeroZero p b pos).check F hints
  let ⟨zeroSucc⟩ ← (zeroSucc p b pos).check F hints
  let ⟨succZero⟩ ← (succZero p b pos).check F hints
  let ⟨succSucc⟩ ← (succSucc p b pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.boolOpCongr p b pos).check F hints
  pure ⟨⟨zeroZero, zeroSucc, succZero, succSucc, opCongr⟩⟩

variable {p b pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p b pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (boolLit b (Nat.beq a c)) (bool b) := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr 0 0 (FEq.zeroLit hF hn).symm
        (FEq.zeroLit hF hn).symm
      exact c₁.trans (Schema.Spec.closed h.zeroZero hF hE)
    | succ c =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr 0 (c + 1) (FEq.zeroLit hF hn).symm
        (FEq.succLit hF hn c).symm
      have c₂ : FEq E (op₂ pos (zero p) (succ p (.natLit p c))) (boolLit b false) (bool b) := by
        schema_inst h.zeroSucc Beq.zeroSucc #[.natLit p c] #[.natLit p c] using FEq.natLit hF hn c
      exact c₁.trans c₂
  | succ a ih =>
    cases c with
    | zero =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr (a + 1) 0 (FEq.succLit hF hn a).symm
        (FEq.zeroLit hF hn).symm
      have c₂ : FEq E (op₂ pos (succ p (.natLit p a)) (zero p)) (boolLit b false) (bool b) := by
        schema_inst h.succZero Beq.succZero #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
      exact c₁.trans c₂
    | succ c =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr (a + 1) (c + 1)
        (FEq.succLit hF hn a).symm (FEq.succLit hF hn c).symm
      have c₂ : FEq E (op₂ pos (succ p (.natLit p a)) (succ p (.natLit p c)))
          (op₂ pos (.natLit p a) (.natLit p c)) (bool b) := by
        schema_inst h.succSucc Beq.succSucc #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
          using FEq.natLit hF hn a, FEq.natLit hF hn c
      exact c₁.trans (c₂.trans (ih c))

end Beq

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.beq` at `pos` -/
def verifyBeq (t : Table) (pos : Nat) :
    EIO Failure (BoolOp F Nat.beq) := do
  let ⟨p, hn⟩ ← natSpec F t
  let bool ← t.ind ``Bool
  let ⟨hbool⟩ ← inductiveSig F Bool.sig bool
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Beq.check p bool pos F hints
  pure ⟨p, bool, pos, BoolOpSpec.ofFEq hn hbool hop fun _ _ hF hE => h.eval hF hE hn⟩

end Metalean.Checker.Fast
