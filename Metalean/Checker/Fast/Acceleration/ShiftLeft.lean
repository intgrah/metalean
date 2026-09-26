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

namespace ShiftLeft

variable (p mul pos : Nat)

example (x : Nat) : Nat.shiftLeft x Nat.zero = x := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ x : nat p

example (x y : Nat) : Nat.shiftLeft x (Nat.succ y) = Nat.shiftLeft (Nat.mul 2 x) y := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢
    op₂ pos x (succ p y) ≡ op₂ pos (op₂ mul (.natLit p 2) x) y :
    nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p mul pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p mul pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p mul pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  pure ⟨⟨base, step, opCongr⟩⟩

variable {p mul pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p mul pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (hmul : NatOpSpec F p mul Nat.mul) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.shiftLeft a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base ShiftLeft.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have hC := FEq.natLit hF hn c
    have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (op₂ pos (op₂ mul (.natLit p 2) (.natLit p a)) (.natLit p c)) (nat p) := by
      schema_inst h.step ShiftLeft.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using FEq.natLit hF hn a, hC
    have c₂ : FEq E (op₂ pos (op₂ mul (.natLit p 2) (.natLit p a)) (.natLit p c))
        (op₂ pos (.natLit p (Nat.mul 2 a)) (.natLit p c)) (nat p) := by
      schema_inst h.opCongr LiteralRec.opCongr #[op₂ mul (.natLit p 2) (.natLit p a), .natLit p c]
        #[.natLit p (Nat.mul 2 a), .natLit p c] using FEq.natOp hF hE hn hmul 2 a, hC
    exact c₁.trans (c₂.trans (ih (Nat.mul 2 a)))

end ShiftLeft

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.shiftLeft` at `pos` -/
def verifyShiftLeft (pos : Nat) (mul : NatOp F Nat.mul) :
    EIO Failure (NatOp F Nat.shiftLeft) := do
  let ⟨hn⟩ ← natAt F mul.nat
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← ShiftLeft.check mul.nat mul.pos pos F hints
  pure ⟨mul.nat, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn mul.spec⟩

end Metalean.Checker.Fast
