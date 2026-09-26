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

open Frontend (Failure)

namespace ShiftRight

variable (p div pos : Nat)

example (x : Nat) : Nat.shiftRight x Nat.zero = x := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ x : nat p

example (x y : Nat) : Nat.shiftRight x (Nat.succ y) = Nat.div (Nat.shiftRight x y) 2 := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢
    op₂ pos x (succ p y) ≡ op₂ div (op₂ pos x y) (.natLit p 2) :
    nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p div pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F
  divCongr : (LiteralRec.opCongr p div).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p div pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p div pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  let ⟨divCongr⟩ ← (LiteralRec.opCongr p div).check F hints
  pure ⟨⟨base, step, opCongr, divCongr⟩⟩

variable {p div pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p div pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (hdiv : NatOpSpec F p div Nat.div) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.shiftRight a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base ShiftRight.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have hTwo := FEq.natLit hF hn 2
    have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (op₂ div (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p 2)) (nat p) := by
      schema_inst h.step ShiftRight.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using FEq.natLit hF hn a, FEq.natLit hF hn c
    have c₂ : FEq E (op₂ div (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p 2))
        (op₂ div (.natLit p (Nat.shiftRight a c)) (.natLit p 2)) (nat p) := by
      schema_inst h.divCongr LiteralRec.opCongr #[op₂ pos (.natLit p a) (.natLit p c), .natLit p 2]
        #[.natLit p (Nat.shiftRight a c), .natLit p 2] using ih a, hTwo
    exact c₁.trans (c₂.trans (FEq.natOp hF hE hn hdiv (Nat.shiftRight a c) 2))

end ShiftRight

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.shiftRight` at `pos` -/
def verifyShiftRight (pos : Nat) (div : NatOp F Nat.div) :
    EIO Failure (NatOp F Nat.shiftRight) := do
  let ⟨hn⟩ ← natAt F div.nat
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← ShiftRight.check div.nat div.pos pos F hints
  pure ⟨div.nat, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn div.spec⟩

end Metalean.Checker.Fast
