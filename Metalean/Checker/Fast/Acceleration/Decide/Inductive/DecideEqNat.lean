/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Decide.Inductive.EqNat

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open scoped FExpr

open Frontend (Failure Table)

namespace Decide.Inductive.DecideEqNat

structure Consts extends toEqNat : EqNat.Consts, toDecideConsts : Decide.DecideConsts

variable (F : FEnv) (hints : PArray Export.Hints) (D : Decide.DecideConsts)

def congr : Schema :=
  schema% (P : prop) (d : FExpr.Decidable D P) ⊢ FExpr.Decidable.decide D P d : bool D.Bool_

def lit (v : Bool) : Schema :=
  schema% (P : prop) (h : cond v P (FExpr.Not D P)) ⊢
    FExpr.Decidable.decide D P (FExpr.Decidable.ofBool D v P h) ≡ boolLit D.Bool_ v :
    bool D.Bool_

structure Spec : Prop where
  congr : (congr D).Spec F
  lit : ∀ v, (lit D v).Spec F

def check : EIO Failure (PLift (Spec F D)) := do
  let ⟨congr⟩ ← (congr D).check F hints
  let ⟨lit⟩ ← checkBools fun v => (lit D v).check F hints
  pure ⟨⟨congr, lit⟩⟩

variable {F D} {ζ : Sigs} {E : Env ζ}

theorem Spec.reduces (h : Spec F D) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {P d p : FExpr} (v : Bool) (hP : FEq E P P prop) :
    FEq E d (FExpr.Decidable.ofBool D v P p) (FExpr.Decidable D P) →
    FEq E p p (cond v P (FExpr.Not D P)) →
    FEq E (FExpr.Decidable.decide D P d) (boolLit D.Bool_ v) (bool D.Bool_) := by
  intro hd hp
  schema_have c₁ := h.congr DecideEqNat.congr #[P, d] #[P, FExpr.Decidable.ofBool D v P p]
    using hP, hd
  have hlit := h.lit v
  cases v <;>
  · schema_have c₂ := hlit DecideEqNat.lit #[P, p] #[P, p] using hP, hp
    exact c₁.trans c₂

theorem Spec.decideEqNat {C : Consts} (h : Spec F C.toDecideConsts)
    (he : EqNat.Spec F C.toEqNat) (hn : NatSpec F C.Nat_)
    (hbeq : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_beq Nat.beq) :
    DecideEqNat F C.toDecideConsts := by
  intro _ _ hF hE a b
  have ⟨hP, _, hdec, hp⟩ := he.eval hF hE hn hbeq a b
  exact h.reduces hF hE (Nat.beq a b) hP hdec hp

end DecideEqNat

variable (F : FEnv) (hints : PArray Export.Hints)

def verifyDecideEqNat (D : Decide.DecideConsts) (t : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecideEqNat F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let ⟨hbeq⟩ ← beq.at F D.Nat_ D.Bool_
  let C : DecideEqNat.Consts := { D with
    Nat_beq := beq.pos
    Nat_decEq_match_1 := ← t.const `Nat.decEq.match_1
    Nat_eq_of_beq_eq_true := ← t.const ``Nat.eq_of_beq_eq_true
    Nat_ne_of_beq_eq_false := ← t.const ``Nat.ne_of_beq_eq_false }
  let ⟨he⟩ ← EqNat.check F hints C.toEqNat
  let ⟨h⟩ ← DecideEqNat.check F hints D
  pure ⟨h.decideEqNat he hn hbeq⟩

end Decide.Inductive

end Metalean.Checker.Fast
