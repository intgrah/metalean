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

namespace Add

variable (p pos : Nat)

example (x : Nat) : Nat.add x Nat.zero = x := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ x : nat p

example (x y : Nat) : Nat.add x (Nat.succ y) = Nat.succ (Nat.add x y) := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos x (succ p y) ≡ succ p (op₂ pos x y) : nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F
  succCongr : (LiteralRec.succCongr p).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  let ⟨succCongr⟩ ← (LiteralRec.succCongr p).check F hints
  pure ⟨⟨base, step, opCongr, succCongr⟩⟩

variable {p pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.add a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base Add.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (succ p (op₂ pos (.natLit p a) (.natLit p c))) (nat p) := by
      schema_inst h.step Add.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using FEq.natLit hF hn a, FEq.natLit hF hn c
    exact c₁.trans (LiteralRec.succ_natLit hF hE hn h.succCongr _ (ih a))

end Add

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.add` at `pos` -/
def verifyAdd (t : Table) (pos : Nat) : EIO Failure (NatOp F Nat.add) := do
  let ⟨p, hn⟩ ← natSpec F t
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Add.check p pos F hints
  pure ⟨p, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn⟩

end Metalean.Checker.Fast
