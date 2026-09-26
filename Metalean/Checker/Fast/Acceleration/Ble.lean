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

namespace Ble

variable (p b pos : Nat)

example (y : Nat) : Nat.ble Nat.zero y = true := rfl

def zero : Schema :=
  schema% (y : nat p) ⊢ op₂ pos (FExpr.zero p) y ≡ boolLit b true : bool b

example (x : Nat) : Nat.ble (Nat.succ x) Nat.zero = false := rfl

def succZero : Schema :=
  schema% (x : nat p) ⊢ op₂ pos (succ p x) (FExpr.zero p) ≡ boolLit b false : bool b

example (x y : Nat) : Nat.ble (Nat.succ x) (Nat.succ y) = Nat.ble x y := rfl

def succSucc : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos (succ p x) (succ p y) ≡ op₂ pos x y : bool b

variable (F : FEnv)

structure Spec : Prop where
  zero : (zero p b pos).Spec F
  succZero : (succZero p b pos).Spec F
  succSucc : (succSucc p b pos).Spec F
  opCongr : (LiteralRec.boolOpCongr p b pos).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p b pos F)) := do
  let ⟨zero⟩ ← (zero p b pos).check F hints
  let ⟨succZero⟩ ← (succZero p b pos).check F hints
  let ⟨succSucc⟩ ← (succSucc p b pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.boolOpCongr p b pos).check F hints
  pure ⟨⟨zero, succZero, succSucc, opCongr⟩⟩

variable {p b pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p b pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (boolLit b (Nat.ble a c)) (bool b) := by
  induction a generalizing c with
  | zero =>
    have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr 0 c (FEq.zeroLit hF hn).symm
      (FEq.natLit hF hn c)
    have c₂ : FEq E (op₂ pos (FExpr.zero p) (.natLit p c)) (boolLit b true) (bool b) := by
      schema_inst h.zero Ble.zero #[.natLit p c] #[.natLit p c] using FEq.natLit hF hn c
    exact c₁.trans c₂
  | succ a ih =>
    cases c with
    | zero =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr (a + 1) 0 (FEq.succLit hF hn a).symm
        (FEq.zeroLit hF hn).symm
      have c₂ : FEq E (op₂ pos (succ p (.natLit p a)) (FExpr.zero p)) (boolLit b false)
          (bool b) := by
        schema_inst h.succZero Ble.succZero #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
      exact c₁.trans c₂
    | succ c =>
      have c₁ := LiteralRec.boolOp_congr hF hE h.opCongr (a + 1) (c + 1)
        (FEq.succLit hF hn a).symm (FEq.succLit hF hn c).symm
      have c₂ : FEq E (op₂ pos (succ p (.natLit p a)) (succ p (.natLit p c)))
          (op₂ pos (.natLit p a) (.natLit p c)) (bool b) := by
        schema_inst h.succSucc Ble.succSucc #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
          using FEq.natLit hF hn a, FEq.natLit hF hn c
      exact c₁.trans (c₂.trans (ih c))

end Ble

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.ble` at `pos` -/
def verifyBle (t : Table) (pos : Nat) :
    EIO Failure (BoolOp F Nat.ble) := do
  let ⟨p, hn⟩ ← natSpec F t
  let bool ← t.ind ``Bool
  let ⟨hbool⟩ ← inductiveSig F Bool.sig bool
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Ble.check p bool pos F hints
  pure ⟨p, bool, pos, BoolOpSpec.ofFEq hn hbool hop fun _ _ hF hE => h.eval hF hE hn⟩

end Metalean.Checker.Fast
