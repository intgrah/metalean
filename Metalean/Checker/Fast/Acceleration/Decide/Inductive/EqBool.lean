/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Decide.Inductive.Basic

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open scoped FExpr

open Frontend (Failure Table)

namespace Decide.Inductive.EqBool

variable (F : FEnv) (hints : Array Export.Hints) (D : Decide.EqBoolConsts)
  (β γ : Bool)

def proofType (q : FExpr) : Schema :=
  schema% ⊢ q :
    cond (β == γ) (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
      (FExpr.Not D (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ)))

def reduce : Schema :=
  schema% (h : cond (β == γ) (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
        (FExpr.Not D (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))))
      (t : FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ) ⟶ nat D.Nat_)
      (e : FExpr.Not D (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ)) ⟶
        nat D.Nat_) ⊢
    FExpr.dite D (nat D.Nat_) (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
        (FExpr.instDecidableEqBool D (boolLit D.Bool_ β) (boolLit D.Bool_ γ)) t e ≡
      .app (cond (β == γ) t e) h :
    nat D.Nat_

variable {F D β γ}

theorem reduces {q : FExpr} (hq : (proofType D β γ q).Spec F) (hr : (reduce D β γ).Spec F) :
    Reduces F D (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
      (FExpr.instDecidableEqBool D (boolLit D.Bool_ β) (boolLit D.Bool_ γ)) (β == γ) := by
  intro _ _ hF hE t e ht he
  have hq' := Schema.Spec.closed hq hF hE
  refine ⟨q, hq', ?_⟩
  cases β <;> cases γ <;>
    schema_inst hr EqBool.reduce #[q, t, e] #[q, t, e] using hq', ht, he

variable (F D β γ)

def check : EIO Failure (PLift (Reduces F D
    (FExpr.Eq D (bool D.Bool_) (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
    (FExpr.instDecidableEqBool D (boolLit D.Bool_ β) (boolLit D.Bool_ γ)) (β == γ))) := do
  let q ← decidableProof F hints
    (FExpr.instDecidableEqBool D (boolLit D.Bool_ β) (boolLit D.Bool_ γ))
  let ⟨hq⟩ ← (proofType D β γ q).check F hints
  let ⟨hr⟩ ← (reduce D β γ).check F hints
  pure ⟨reduces hq hr⟩

end EqBool

variable (F : FEnv) (hints : Array Export.Hints)

def verifyDecEqBool (D : Decide.EqBoolConsts) (_ : Table) :
    EIO Failure (PLift (DecEqBool F D)) :=
  checkBools fun β => checkBools fun γ => EqBool.check F hints D β γ

end Decide.Inductive

end Metalean.Checker.Fast
