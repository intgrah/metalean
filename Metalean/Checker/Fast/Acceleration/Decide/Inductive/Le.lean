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

namespace Decide.Inductive.Le

structure Consts extends toLeConsts : Decide.LeConsts, toEqBoolConsts : Decide.EqBoolConsts where
  protected Nat_ble : Nat
  protected Nat_le_of_ble_eq_true : Nat
  protected Nat_not_le_of_not_ble_eq_true : Nat

instance : CoeOut Consts Decide.LeConsts := ⟨Consts.toLeConsts⟩

end Decide.Inductive.Le

namespace FExpr

variable (C : Decide.Inductive.Le.Consts)

@[fexpr_unfold]
protected def Nat.le_of_ble_eq_true (a b : FExpr) : FExpr :=
  op₂ C.Nat_le_of_ble_eq_true a b

@[fexpr_unfold]
protected def Nat.not_le_of_not_ble_eq_true (a b : FExpr) : FExpr :=
  op₂ C.Nat_not_le_of_not_ble_eq_true a b

end FExpr

namespace Decide.Inductive.Le

variable (F : FEnv) (hints : Array Export.Hints) (C : Consts)

@[fexpr_unfold]
def decideBool (P β yes no : FExpr) : FExpr :=
  let Q := FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true)
  FExpr.dite C (FExpr.Decidable C P) Q
    (FExpr.instDecidableEqBool C.toEqBoolConsts β (boolLit C.Bool_ true))
    (.lam Q (FExpr.Decidable.ofBool C true P (.app yes (.bvar 0))))
    (.lam (FExpr.Not C Q) (FExpr.Decidable.ofBool C false P (.app no (.bvar 0))))

def propType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢ FExpr.Nat.le C y x : prop

def unfold : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.decLe C y x ≡
      decideBool C (FExpr.Nat.le C y x) (op₂ C.Nat_ble y x)
        (FExpr.Nat.le_of_ble_eq_true C y x) (FExpr.Nat.not_le_of_not_ble_eq_true C y x) :
    FExpr.Decidable C (FExpr.Nat.le C y x)

def yesType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.le_of_ble_eq_true C y x :
    FExpr.Eq C (bool C.Bool_) (op₂ C.Nat_ble y x) (boolLit C.Bool_ true) ⟶ FExpr.Nat.le C y x

def noType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.not_le_of_not_ble_eq_true C y x :
    FExpr.Not C (FExpr.Eq C (bool C.Bool_) (op₂ C.Nat_ble y x) (boolLit C.Bool_ true)) ⟶
      FExpr.Not C (FExpr.Nat.le C y x)

def yesCongr : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) (β : bool C.Bool_) ⊢
    (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true) ⟶ FExpr.Nat.le C y x) : prop

def noCongr : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) (β : bool C.Bool_) ⊢
    (FExpr.Not C (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true)) ⟶
      FExpr.Not C (FExpr.Nat.le C y x)) :
    prop

def decideCongr : Schema :=
  schema% (P : prop) (β : bool C.Bool_)
      (yes : FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Not C (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true)) ⟶ FExpr.Not C P) ⊢
    decideBool C P β yes no : FExpr.Decidable C P

def witness (q : FExpr) (v : Bool) : Schema :=
  schema% ⊢ cond v (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ true)) q :
    cond v (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true))
      (FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)))

def decideLit (v : Bool) : Schema :=
  schema% (P : prop)
      (yes : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)) ⟶
        FExpr.Not C P)
      (r : cond v (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true))
        (FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)))) ⊢
    decideBool C P (boolLit C.Bool_ v) yes no ≡
      FExpr.Decidable.ofBool C v P (.app (cond v yes no) r) :
    FExpr.Decidable C P

def proofType (v : Bool) : Schema :=
  schema% (P : prop)
      (yes : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)) ⟶
        FExpr.Not C P)
      (r : cond v (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true))
        (FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)))) ⊢
    .app (cond v yes no) r : cond v P (FExpr.Not C P)

structure Spec (q : FExpr) : Prop where
  propType : (propType C).Spec F
  unfold : (unfold C).Spec F
  yesType : (yesType C).Spec F
  noType : (noType C).Spec F
  yesCongr : (yesCongr C).Spec F
  noCongr : (noCongr C).Spec F
  decideCongr : (decideCongr C).Spec F
  witness : ∀ v, (witness C q v).Spec F
  decideLit : ∀ v, (decideLit C v).Spec F
  proofType : ∀ v, (proofType C v).Spec F

def check (q : FExpr) : EIO Failure (PLift (Spec F C q)) := do
  let ⟨propType⟩ ← (propType C).check F hints
  let ⟨unfold⟩ ← (unfold C).check F hints
  let ⟨yesType⟩ ← (yesType C).check F hints
  let ⟨noType⟩ ← (noType C).check F hints
  let ⟨yesCongr⟩ ← (yesCongr C).check F hints
  let ⟨noCongr⟩ ← (noCongr C).check F hints
  let ⟨decideCongr⟩ ← (decideCongr C).check F hints
  let ⟨witness⟩ ← checkBools fun v => (witness C q v).check F hints
  let ⟨decideLit⟩ ← checkBools fun v => (decideLit C v).check F hints
  let ⟨proofType⟩ ← checkBools fun v => (proofType C v).check F hints
  pure ⟨⟨propType, unfold, yesType, noType, yesCongr, noCongr, decideCongr, witness, decideLit,
    proofType⟩⟩

variable {F C} {q : FExpr} {ζ : Sigs} {E : Env ζ}

theorem Spec.lit (h : Spec F C q) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {P yes no r : FExpr} (v : Bool) (hP : FEq E P P prop)
    (hyes : FEq E yes yes
      (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P))
    (hno : FEq E no no
      (FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true)) ⟶
        FExpr.Not C P))
    (hr : FEq E r r
      (cond v (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true))
        (FExpr.Not C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true))))) :
    FEq E (decideBool C P (boolLit C.Bool_ v) yes no)
      (FExpr.Decidable.ofBool C v P (.app (cond v yes no) r)) (FExpr.Decidable C P) ∧
    FEq E (.app (cond v yes no) r) (.app (cond v yes no) r) (cond v P (FExpr.Not C P)) := by
  have hd := h.decideLit v
  have hp := h.proofType v
  cases v <;>
  · schema_have c := hd Le.decideLit #[P, yes, no, r] #[P, yes, no, r] using hP, hyes, hno, hr
    schema_have hty := hp Le.proofType #[P, yes, no, r] #[P, yes, no, r]
      using hP, hyes, hno, hr
    exact ⟨c, hty⟩

theorem Spec.eval (h : Spec F C q) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F C.Nat_) (hble : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_ble Nat.ble) (b a : Nat) :
    FEq E (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a)) (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a))
      prop ∧
    ∃ p : FExpr,
      FEq E (FExpr.Nat.decLe C (.natLit C.Nat_ b) (.natLit C.Nat_ a))
        (FExpr.Decidable.ofBool C (Nat.ble b a) (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a)) p)
        (FExpr.Decidable C (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a))) ∧
      FEq E p p (cond (Nat.ble b a) (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a))
        (FExpr.Not C (FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a)))) := by
  have hB := FEq.natLit hF hn b
  have hA := FEq.natLit hF hn a
  have hβ := FEq.boolOp hF hE hn hble b a
  schema_have hP := h.propType Le.propType #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have hyes := h.yesType Le.yesType #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have hno := h.noType Le.noType #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have hyesT := h.yesCongr Le.yesCongr
    #[.natLit C.Nat_ b, .natLit C.Nat_ a, op₂ C.Nat_ble (.natLit C.Nat_ b) (.natLit C.Nat_ a)]
    #[.natLit C.Nat_ b, .natLit C.Nat_ a, boolLit C.Bool_ (Nat.ble b a)] using hB, hA, hβ
  schema_have hnoT := h.noCongr Le.noCongr
    #[.natLit C.Nat_ b, .natLit C.Nat_ a, op₂ C.Nat_ble (.natLit C.Nat_ b) (.natLit C.Nat_ a)]
    #[.natLit C.Nat_ b, .natLit C.Nat_ a, boolLit C.Bool_ (Nat.ble b a)] using hB, hA, hβ
  schema_have c₁ := h.unfold Le.unfold #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have c₂ := h.decideCongr Le.decideCongr
    #[FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a), op₂ C.Nat_ble (.natLit C.Nat_ b) (.natLit C.Nat_ a),
      FExpr.Nat.le_of_ble_eq_true C (.natLit C.Nat_ b) (.natLit C.Nat_ a),
      FExpr.Nat.not_le_of_not_ble_eq_true C (.natLit C.Nat_ b) (.natLit C.Nat_ a)]
    #[FExpr.Nat.le C (.natLit C.Nat_ b) (.natLit C.Nat_ a), boolLit C.Bool_ (Nat.ble b a),
      FExpr.Nat.le_of_ble_eq_true C (.natLit C.Nat_ b) (.natLit C.Nat_ a),
      FExpr.Nat.not_le_of_not_ble_eq_true C (.natLit C.Nat_ b) (.natLit C.Nat_ a)]
    using hP, hβ, hyes, hno
  have hr := Schema.Spec.closed (h.witness (Nat.ble b a)) hF hE
  have ⟨c₃, hp⟩ := h.lit hF hE (Nat.ble b a) hP (hyes.conv hyesT) (hno.conv hnoT) hr
  exact ⟨hP, _, c₁.trans (c₂.trans c₃), hp⟩

theorem Spec.decLe (h : Spec F C q) (hd : Dite.Spec F C) (hn : NatSpec F C.Nat_)
    (hble : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_ble Nat.ble) :
    DecLe F C.toLeConsts := by
  intro b a _ _ hF hE _ _ ht he
  have ⟨hP, p, hdec, hp⟩ := h.eval hF hE hn hble b a
  exact ⟨p, hp, hd.reduces hF hE (Nat.ble b a) hP ht he hdec hp⟩

end Le

variable (F : FEnv) (hints : Array Export.Hints)

def verifyDecLe (D : Decide.LeConsts) (t : Table) (ble : BoolOp F Nat.ble) :
    EIO Failure (PLift (DecLe F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let C : Le.Consts := { D with
    Bool_ := ble.bool
    Nat_ble := ble.pos
    instDecidableEqBool := ← t.const ``instDecidableEqBool
    Nat_le_of_ble_eq_true := ← t.const ``Nat.le_of_ble_eq_true
    Nat_not_le_of_not_ble_eq_true := ← t.const ``Nat.not_le_of_not_ble_eq_true }
  let q ← decidableProof F hints
    (FExpr.instDecidableEqBool C.toEqBoolConsts (boolLit C.Bool_ false) (boolLit C.Bool_ true))
  let ⟨h⟩ ← Le.check F hints C q
  let ⟨hd⟩ ← Dite.check F hints C
  let ⟨hble⟩ ← ble.at F C.Nat_ C.Bool_
  pure ⟨h.decLe hd hn hble⟩

end Decide.Inductive

end Metalean.Checker.Fast
