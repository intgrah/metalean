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

namespace FExpr

@[fexpr_unfold]
protected def Nat.pred (pos : Nat) (x : FExpr) : FExpr :=
  .app (.const pos #[]) x

end FExpr

namespace Pred

variable (p pos : Nat)

example : Nat.pred Nat.zero = Nat.zero := rfl

def base : Schema :=
  schema% ⊢ FExpr.Nat.pred pos (zero p) ≡ zero p : nat p

example (y : Nat) : Nat.pred (Nat.succ y) = y := rfl

def step : Schema :=
  schema% (y : nat p) ⊢ FExpr.Nat.pred pos (succ p y) ≡ y : nat p

example (x : Nat) : Nat := Nat.pred x

def congr : Schema :=
  schema% (x : nat p) ⊢ FExpr.Nat.pred pos x : nat p

variable (F : FEnv)

structure Spec : Prop where
  base : (base p pos).Spec F
  step : (step p pos).Spec F
  congr : (congr p pos).Spec F

variable (hints : Array Export.Hints)

def check : EIO Failure (PLift (Spec p pos F)) := do
  let ⟨base⟩ ← (base p pos).check F hints
  let ⟨step⟩ ← (step p pos).check F hints
  let ⟨congr⟩ ← (congr p pos).check F hints
  pure ⟨⟨base, step, congr⟩⟩

variable {p pos F} {ζ : Sigs} {E : Env ζ}

theorem Spec.eval (h : Spec p pos F) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) {x : FExpr} (a : Nat) :
    FEq E x (.natLit p a) (nat p) →
    FEq E (FExpr.Nat.pred pos x) (.natLit p (Nat.pred a)) (nat p) := by
  intro hx
  cases a with
  | zero =>
    have c₁ : FEq E (FExpr.Nat.pred pos x) (FExpr.Nat.pred pos (zero p)) (nat p) := by
      schema_inst h.congr Pred.congr #[x] #[zero p] using hx.trans (FEq.zeroLit hF hn).symm
    have c₂ : FEq E (FExpr.Nat.pred pos (zero p)) (zero p) (nat p) :=
      Schema.Spec.closed h.base hF hE
    exact c₁.trans (c₂.trans (FEq.zeroLit hF hn))
  | succ a =>
    have c₁ : FEq E (FExpr.Nat.pred pos x) (FExpr.Nat.pred pos (succ p (.natLit p a)))
        (nat p) := by
      schema_inst h.congr Pred.congr #[x] #[succ p (.natLit p a)]
        using hx.trans (FEq.succLit hF hn a).symm
    have c₂ : FEq E (FExpr.Nat.pred pos (succ p (.natLit p a))) (.natLit p a) (nat p) := by
      schema_inst h.step Pred.step #[.natLit p a] #[.natLit p a] using FEq.natLit hF hn a
    exact c₁.trans c₂

end Pred

end Metalean.Checker.Fast
