/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Base
public import Metalean.Frontend.Table

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

namespace LiteralRec

variable (p b pos : Nat)

example (x : Nat) : Nat := Nat.succ x

def succCongr : Schema :=
  schema% (x : nat p) ⊢ succ p x : nat p

example (f : Nat → Nat → Nat) (x y : Nat) : Nat := f x y

def opCongr : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos x y : nat p

example (f : Nat → Nat → Bool) (x y : Nat) : Bool := f x y

def boolOpCongr : Schema :=
  schema% (x : nat p) (y : nat p) ⊢ op₂ pos x y : bool b

variable {F : FEnv} {p b pos} {ζ : Sigs} {E : Env ζ}
  (hF : FEnv.Denotes F E) (hE : EnvWF E) (hn : NatSpec F p)

include hF hE hn in
theorem succ_natLit (h : (succCongr p).Spec F) {x : FExpr} (a : Nat) :
    FEq E x (.natLit p a) (nat p) →
    FEq E (succ p x) (.natLit p (a + 1)) (nat p) := by
  intro hx
  have c : FEq E (succ p x) (succ p (.natLit p a)) (nat p) := by
    schema_inst h LiteralRec.succCongr #[x] #[.natLit p a] using hx
  exact c.trans (FEq.succLit hF hn a)

include hF hE hn in
theorem natOp {f : Nat → Nat → Nat} (h : (opCongr p pos).Spec F)
    (base : ∀ a, FEq E (op₂ pos (.natLit p a) (zero p)) (.natLit p (f a 0)) (nat p))
    (step : ∀ c,
      (∀ a, FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (f a c)) (nat p)) →
      ∀ a, FEq E (op₂ pos (.natLit p a) (succ p (.natLit p c))) (.natLit p (f a (c + 1))) (nat p))
    (a c : Nat) :
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (.natLit p (f a c)) (nat p) := by
  induction c generalizing a with
  | zero =>
    have hA := FEq.natLit hF hn a
    have c₁ : FEq E (op₂ pos (.natLit p a) (.natLit p 0)) (op₂ pos (.natLit p a) (zero p))
        (nat p) := by
      schema_inst h LiteralRec.opCongr #[.natLit p a, .natLit p 0] #[.natLit p a, zero p]
        using hA, (FEq.zeroLit hF hn).symm
    exact c₁.trans (base a)
  | succ c ih =>
    have hA := FEq.natLit hF hn a
    have c₁ : FEq E (op₂ pos (.natLit p a) (.natLit p (c + 1)))
        (op₂ pos (.natLit p a) (succ p (.natLit p c))) (nat p) := by
      schema_inst h LiteralRec.opCongr #[.natLit p a, .natLit p (c + 1)]
        #[.natLit p a, succ p (.natLit p c)] using hA, (FEq.succLit hF hn c).symm
    exact c₁.trans (step c ih a)

include hF hE in
theorem boolOp_congr (h : (boolOpCongr p b pos).Spec F) {x y : FExpr} (a c : Nat) :
    FEq E (.natLit p a) x (nat p) →
    FEq E (.natLit p c) y (nat p) →
    FEq E (op₂ pos (.natLit p a) (.natLit p c)) (op₂ pos x y) (bool b) := by
  intro hx hy
  schema_inst h LiteralRec.boolOpCongr #[.natLit p a, .natLit p c] #[x, y] using hx, hy

end LiteralRec

end Metalean.Checker.Fast
