/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Pred

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace Sub

variable (p pred pos : Nat)

example (x : Nat) : Nat.sub x Nat.zero = x := rfl

def base : Schema :=
  schema% (x : nat p) ⊢ op₂ pos x (zero p) ≡ x : nat p

example (x y : Nat) : Nat.sub x (Nat.succ y) = Nat.pred (Nat.sub x y) := rfl

def step : Schema :=
  schema% (x : nat p) (y : nat p) ⊢
    op₂ pos x (succ p y) ≡ FExpr.Nat.pred pred (op₂ pos x y) :
    nat p

variable (F : FEnv)

structure Spec : Prop where
  predSpec : Pred.Spec p pred F
  base : (base p pos).Spec F
  step : (step p pred pos).Spec F
  opCongr : (LiteralRec.opCongr p pos).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p pred pos F)) := do
  let ⟨predSpec⟩ ← Pred.check p pred F hints
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p pred pos).check F hints
  let ⟨opCongr⟩ ← (LiteralRec.opCongr p pos).check F hints
  pure ⟨⟨predSpec, base, step, opCongr⟩⟩

variable {p pred pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p pred pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (Nat.sub a c)) (nat p) := by
  refine LiteralRec.natOp hF hE hn h.opCongr (fun a => ?_) (fun c ih a => ?_) a c
  · schema_inst h.base Sub.base #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
  · have c₁ : FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c)))
        (FExpr.Nat.pred pred (op₂ pos (.natLit p a) (.natLit p c))) (nat p) := by
      schema_inst h.step Sub.step #[.natLit p a, .natLit p c] #[.natLit p a, .natLit p c]
        using FEq.natLit hF hn a, FEq.natLit hF hn c
    exact c₁.trans (h.predSpec.eval hF hE hn _ (ih a))

end Sub

variable (F : FEnv) (hints : Array Export.Hints)

/-- `Nat.sub` at `pos` -/
def verifySub (t : Table) (pos : Nat) : EIO Failure (NatOp F Nat.sub) := do
  let ⟨p, hn⟩ ← natSpec F t
  let ⟨hop⟩ ← constDef F pos
  let pred ← t.const ``Nat.pred
  let ⟨h⟩ ← Sub.check p pred pos F hints
  pure ⟨p, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE => h.eval hF hE hn⟩

end Metalean.Checker.Fast
