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

namespace Mul

variable (p add pos : Nat)

example (x : Nat) : Nat.mul x Nat.zero = 0 := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ .natLit p 0 : nat p

example (x y : Nat) : Nat.mul x (Nat.succ y) = Nat.add (Nat.mul x y) x := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos x (succ p y) ≡ op₂ add (op₂ pos x y) x : nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p add pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F
  addCongr : (LiteralRec.opCongr p add).Spec F

variable (hints : PArray Export.Hints)

def check : EIO Failure (PLift (Spec p add pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p add pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  let ⟨addCongr⟩ ← (LiteralRec.opCongr p add).check F hints
  pure ⟨⟨base, step, opCongr, addCongr⟩⟩

variable {p add pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p add pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (hadd : NatOpSpec F p add Nat.add) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.mul a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base Mul.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have hA := FEq.natLit hF hn a
    have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (op₂ add (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p a)) (nat p) := by
      schema_inst h.step Mul.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using hA, FEq.natLit hF hn c
    have c₂ : FEq E (op₂ add (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p a))
        (op₂ add (.natLit p (Nat.mul a c)) (.natLit p a)) (nat p) := by
      schema_inst h.addCongr LiteralRec.opCongr #[op₂ pos (.natLit p a) (.natLit p c), .natLit p a]
        #[.natLit p (Nat.mul a c), .natLit p a] using ih a, hA
    exact c₁.trans (c₂.trans (FEq.natOp hF hE hn hadd (Nat.mul a c) a))

end Mul

variable (F : FEnv) (hints : PArray Export.Hints)

/-- `Nat.mul` at `pos` -/
def verifyMul (pos : Nat) (add : NatOp F Nat.add) :
    EIO Failure (NatOp F Nat.mul) := do
  let ⟨hn⟩ ← natAt F add.nat
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Mul.check add.nat add.pos pos F hints
  pure ⟨add.nat, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn add.spec⟩

end Metalean.Checker.Fast
