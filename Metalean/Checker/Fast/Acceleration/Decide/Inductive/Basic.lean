/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Decide.Basic

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open scoped FExpr

open Frontend (Failure)

/-- `Decidable.isFalse` or `Decidable.isTrue` -/
@[fexpr_unfold]
protected def FExpr.Decidable.ofBool (D : Decide.Consts) (v : Bool) (p h : FExpr) : FExpr :=
  .ctor D.Decidable_ 0 v.toNat #[] #[p] #[h] #[]

namespace Decide.Inductive

variable (F : FEnv) (hints : PArray Export.Hints)

def decidableProof (d : FExpr) : EIO Failure FExpr := do
  let ⟨r, _⟩ ← (whnf F 0 hints {} #[] d).eval
  match r with
  | .ctor _ _ _ _ _ #[q] _ => pure q
  | _ => throw .internal

namespace Dite

variable (D : Decide.Consts)

def congr : Schema :=
  schema% (P : prop) (d : FExpr.Decidable D P) (t : P ⟶ nat D.Nat_)
      (e : FExpr.Not D P ⟶ nat D.Nat_) ⊢
    FExpr.dite D (nat D.Nat_) P d t e : nat D.Nat_

def lit (v : Bool) : Schema :=
  schema% (P : prop) (h : cond v P (FExpr.Not D P)) (t : P ⟶ nat D.Nat_)
      (e : FExpr.Not D P ⟶ nat D.Nat_) ⊢
    FExpr.dite D (nat D.Nat_) P (FExpr.Decidable.ofBool D v P h) t e ≡ .app (cond v t e) h :
    nat D.Nat_

structure Spec : Prop where
  congr : (congr D).Spec F
  lit : ∀ v, (lit D v).Spec F

def check : EIO Failure (PLift (Spec F D)) := do
  let ⟨congr⟩ ← (congr D).check F hints
  let ⟨lit⟩ ← checkBools fun v => (lit D v).check F hints
  pure ⟨⟨congr, lit⟩⟩

variable {F D} {ζ : Sigs} {E : Env ζ}

theorem Spec.reduces (h : Spec F D) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {P d p t e : FExpr} (v : Bool) (hP : FEq E P P prop)
    (ht : FEq E t t (P ⟶ nat D.Nat_)) (he : FEq E e e (FExpr.Not D P ⟶ nat D.Nat_)) :
    FEq E d (FExpr.Decidable.ofBool D v P p) (FExpr.Decidable D P) →
    FEq E p p (cond v P (FExpr.Not D P)) →
    FEq E (FExpr.dite D (nat D.Nat_) P d t e) (.app (cond v t e) p) (nat D.Nat_) := by
  intro hd hp
  schema_have c₁ := h.congr Dite.congr #[P, d, t, e]
    #[P, FExpr.Decidable.ofBool D v P p, t, e] using hP, hd, ht, he
  have hlit := h.lit v
  cases v <;>
  · schema_have c₂ := hlit Dite.lit #[P, p, t, e] #[P, p, t, e] using hP, hp, ht, he
    exact c₁.trans c₂

end Dite

end Decide.Inductive

end Metalean.Checker.Fast
