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

namespace Decide.Inductive.EqNat

structure Consts extends toEqNatConsts : Decide.EqNatConsts, toBoolConsts : Decide.BoolConsts where
  protected Nat_beq : Nat
  protected Nat_decEq_match_1 : Nat
  protected Nat_eq_of_beq_eq_true : Nat
  protected Nat_ne_of_beq_eq_false : Nat

instance : CoeOut Consts Decide.EqNatConsts := ⟨Consts.toEqNatConsts⟩

end Decide.Inductive.EqNat

namespace FExpr

variable (C : Decide.Inductive.EqNat.Consts)

@[fexpr_unfold]
protected def Nat.eq_of_beq_eq_true (a b : FExpr) : FExpr :=
  op₂ C.Nat_eq_of_beq_eq_true a b

@[fexpr_unfold]
protected def Nat.ne_of_beq_eq_false (a b : FExpr) : FExpr :=
  op₂ C.Nat_ne_of_beq_eq_false a b

end FExpr

namespace Decide.Inductive.EqNat

variable (F : FEnv) (hints : Array Export.Hints) (C : Consts)

@[fexpr_unfold]
def decEqMatch (P β yes no : FExpr) : FExpr :=
  let motive := .lam (bool C.Bool_) (FExpr.Decidable C P)
  let onTrue := .lam (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true))
    (FExpr.Decidable.ofBool C true P (.app yes (.bvar 0)))
  let onFalse := .lam (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ false))
    (FExpr.Decidable.ofBool C false P (.app no (.bvar 0)))
  .appList (.const C.Nat_decEq_match_1 #[.succ .zero]) [motive, β, onTrue, onFalse]

def propType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢ FExpr.Eq C (nat C.Nat_) y x : prop

def unfold : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.instDecidableEqNat C y x ≡
      decEqMatch C (FExpr.Eq C (nat C.Nat_) y x) (op₂ C.Nat_beq y x)
        (FExpr.Nat.eq_of_beq_eq_true C y x) (FExpr.Nat.ne_of_beq_eq_false C y x) :
    FExpr.Decidable C (FExpr.Eq C (nat C.Nat_) y x)

def yesType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.eq_of_beq_eq_true C y x :
    FExpr.Eq C (bool C.Bool_) (op₂ C.Nat_beq y x) (boolLit C.Bool_ true) ⟶
      FExpr.Eq C (nat C.Nat_) y x

def noType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.ne_of_beq_eq_false C y x :
    FExpr.Eq C (bool C.Bool_) (op₂ C.Nat_beq y x) (boolLit C.Bool_ false) ⟶
      FExpr.Not C (FExpr.Eq C (nat C.Nat_) y x)

def yesCongr : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) (β : bool C.Bool_) ⊢
    (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true) ⟶ FExpr.Eq C (nat C.Nat_) y x) : prop

def noCongr : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) (β : bool C.Bool_) ⊢
    (FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ false) ⟶
      FExpr.Not C (FExpr.Eq C (nat C.Nat_) y x)) :
    prop

def decideCongr : Schema :=
  schema% (P : prop) (β : bool C.Bool_)
      (yes : FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Eq C (bool C.Bool_) β (boolLit C.Bool_ false) ⟶ FExpr.Not C P) ⊢
    decEqMatch C P β yes no : FExpr.Decidable C P

def decideLit (v : Bool) : Schema :=
  schema% (P : prop)
      (yes : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ false) ⟶
        FExpr.Not C P) ⊢
    decEqMatch C P (boolLit C.Bool_ v) yes no ≡
      FExpr.Decidable.ofBool C v P
        (.app (cond v yes no) (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ v))) :
    FExpr.Decidable C P

def proofType (v : Bool) : Schema :=
  schema% (P : prop)
      (yes : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P)
      (no : FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ false) ⟶
        FExpr.Not C P) ⊢
    .app (cond v yes no) (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ v)) :
    cond v P (FExpr.Not C P)

structure Spec : Prop where
  propType : (propType C).Spec F
  unfold : (unfold C).Spec F
  yesType : (yesType C).Spec F
  noType : (noType C).Spec F
  yesCongr : (yesCongr C).Spec F
  noCongr : (noCongr C).Spec F
  decideCongr : (decideCongr C).Spec F
  decideLit : ∀ v, (decideLit C v).Spec F
  proofType : ∀ v, (proofType C v).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨propType⟩ ← (propType C).check F hints
  let ⟨unfold⟩ ← (unfold C).check F hints
  let ⟨yesType⟩ ← (yesType C).check F hints
  let ⟨noType⟩ ← (noType C).check F hints
  let ⟨yesCongr⟩ ← (yesCongr C).check F hints
  let ⟨noCongr⟩ ← (noCongr C).check F hints
  let ⟨decideCongr⟩ ← (decideCongr C).check F hints
  let ⟨decideLit⟩ ← checkBools fun v => (decideLit C v).check F hints
  let ⟨proofType⟩ ← checkBools fun v => (proofType C v).check F hints
  pure ⟨⟨propType, unfold, yesType, noType, yesCongr, noCongr, decideCongr, decideLit,
    proofType⟩⟩

variable {F C} {ζ : Sigs} {E : Env ζ}

theorem Spec.lit (h : Spec F C) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {P yes no : FExpr} (v : Bool) (hP : FEq E P P prop)
    (hyes : FEq E yes yes
      (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true) ⟶ P))
    (hno : FEq E no no
      (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ false) ⟶ FExpr.Not C P)) :
    FEq E (decEqMatch C P (boolLit C.Bool_ v) yes no)
      (FExpr.Decidable.ofBool C v P
        (.app (cond v yes no) (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ v))))
      (FExpr.Decidable C P) ∧
    FEq E (.app (cond v yes no) (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ v)))
      (.app (cond v yes no) (FExpr.Eq.refl C (bool C.Bool_) (boolLit C.Bool_ v)))
      (cond v P (FExpr.Not C P)) := by
  have hd := h.decideLit v
  have hp := h.proofType v
  cases v <;>
  · schema_have c := hd EqNat.decideLit #[P, yes, no] #[P, yes, no] using hP, hyes, hno
    schema_have hty := hp EqNat.proofType #[P, yes, no] #[P, yes, no] using hP, hyes, hno
    exact ⟨c, hty⟩

theorem Spec.eval (h : Spec F C) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F C.Nat_) (hbeq : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_beq Nat.beq) (a b : Nat) :
    FEq E (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b))
      (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b)) prop ∧
    ∃ p : FExpr,
      FEq E (FExpr.instDecidableEqNat C (.natLit C.Nat_ a) (.natLit C.Nat_ b))
        (FExpr.Decidable.ofBool C (Nat.beq a b) (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b))
          p)
        (FExpr.Decidable C (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b))) ∧
      FEq E p p (cond (Nat.beq a b) (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b))
        (FExpr.Not C (FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b)))) := by
  have hA := FEq.natLit hF hn a
  have hB := FEq.natLit hF hn b
  have hβ := FEq.boolOp hF hE hn hbeq a b
  schema_have hP := h.propType EqNat.propType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have hyes := h.yesType EqNat.yesType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have hno := h.noType EqNat.noType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have hyesT := h.yesCongr EqNat.yesCongr
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, op₂ C.Nat_beq (.natLit C.Nat_ a) (.natLit C.Nat_ b)]
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, boolLit C.Bool_ (Nat.beq a b)] using hA, hB, hβ
  schema_have hnoT := h.noCongr EqNat.noCongr
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, op₂ C.Nat_beq (.natLit C.Nat_ a) (.natLit C.Nat_ b)]
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, boolLit C.Bool_ (Nat.beq a b)] using hA, hB, hβ
  schema_have c₁ := h.unfold EqNat.unfold #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have c₂ := h.decideCongr EqNat.decideCongr
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b), op₂ C.Nat_beq (.natLit C.Nat_ a) (.natLit C.Nat_ b),
      FExpr.Nat.eq_of_beq_eq_true C (.natLit C.Nat_ a) (.natLit C.Nat_ b),
      FExpr.Nat.ne_of_beq_eq_false C (.natLit C.Nat_ a) (.natLit C.Nat_ b)]
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ b), boolLit C.Bool_ (Nat.beq a b),
      FExpr.Nat.eq_of_beq_eq_true C (.natLit C.Nat_ a) (.natLit C.Nat_ b),
      FExpr.Nat.ne_of_beq_eq_false C (.natLit C.Nat_ a) (.natLit C.Nat_ b)]
    using hP, hβ, hyes, hno
  have ⟨c₃, hp⟩ := h.lit hF hE (Nat.beq a b) hP (hyes.conv hyesT) (hno.conv hnoT)
  exact ⟨hP, _, c₁.trans (c₂.trans c₃), hp⟩

theorem Spec.decEqNat (h : Spec F C) (hd : Dite.Spec F C) (hn : NatSpec F C.Nat_)
    (hbeq : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_beq Nat.beq) :
    DecEqNat F C.toEqNatConsts := by
  intro a b _ _ hF hE _ _ ht he
  have ⟨hP, p, hdec, hp⟩ := h.eval hF hE hn hbeq a b
  exact ⟨p, hp, hd.reduces hF hE (Nat.beq a b) hP ht he hdec hp⟩

end EqNat

variable (F : FEnv) (hints : Array Export.Hints)

def verifyDecEqNat (D : Decide.EqNatConsts) (t : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecEqNat F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let C : EqNat.Consts := { D with
    Bool_ := beq.bool
    Nat_beq := beq.pos
    Nat_decEq_match_1 := ← t.const `Nat.decEq.match_1
    Nat_eq_of_beq_eq_true := ← t.const ``Nat.eq_of_beq_eq_true
    Nat_ne_of_beq_eq_false := ← t.const ``Nat.ne_of_beq_eq_false }
  let ⟨h⟩ ← EqNat.check F hints C
  let ⟨hd⟩ ← Dite.check F hints C
  let ⟨hbeq⟩ ← beq.at F C.Nat_ C.Bool_
  pure ⟨h.decEqNat hd hn hbeq⟩

end Decide.Inductive

end Metalean.Checker.Fast
