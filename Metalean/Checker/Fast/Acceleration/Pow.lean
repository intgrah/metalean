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

namespace Pow

variable (p mul pos : Nat)

example (x : Nat) : Nat.pow x Nat.zero = 1 := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ .natLit p 1 : nat p

example (x y : Nat) : Nat.pow x (Nat.succ y) = Nat.mul (Nat.pow x y) x := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos x (succ p y) ≡ op₂ mul (op₂ pos x y) x : nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p mul pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F
  mulCongr : (LiteralRec.opCongr p mul).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p mul pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p mul pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  let ⟨mulCongr⟩ ← (LiteralRec.opCongr p mul).check F hints
  pure ⟨⟨base, step, opCongr, mulCongr⟩⟩

variable {p mul pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p mul pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (hmul : NatOpSpec F p mul Nat.mul) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.pow a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base Pow.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have hA := FEq.natLit hF hn a
    have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (op₂ mul (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p a)) (nat p) := by
      schema_inst h.step Pow.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using hA, FEq.natLit hF hn c
    have c₂ : FEq E (op₂ mul (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p a))
        (op₂ mul (.natLit p (Nat.pow a c)) (.natLit p a)) (nat p) := by
      schema_inst h.mulCongr LiteralRec.opCongr #[op₂ pos (.natLit p a) (.natLit p c), .natLit p a]
        #[.natLit p (Nat.pow a c), .natLit p a] using ih a, hA
    exact c₁.trans (c₂.trans (FEq.natOp hF hE hn hmul (Nat.pow a c) a))

end Pow

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.pow` at `pos` -/
def verifyPow (pos : Nat) (mul : NatOp F Nat.mul) :
    EIO Failure (NatOp F Nat.pow) := do
  let ⟨hn⟩ ← natAt F mul.nat
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Pow.check mul.nat mul.pos pos F hints
  pure ⟨mul.nat, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn mul.spec⟩

end Metalean.Checker.Fast
