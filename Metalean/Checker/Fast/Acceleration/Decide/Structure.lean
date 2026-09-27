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

open Frontend (Failure Table)

namespace Decide.Structure

structure Consts extends toBoolConsts : Decide.BoolConsts where
  protected Bool_Reflects : Nat
  protected Decidable_reflects_decide : Nat

instance : CoeOut Consts Decide.BoolConsts := ⟨Consts.toBoolConsts⟩

end Decide.Structure

namespace FExpr

variable (C : Decide.Structure.Consts)

@[fexpr_unfold]
protected def Bool.Reflects (b p : FExpr) : FExpr :=
  op₂ C.Bool_Reflects b p

@[fexpr_unfold]
protected def Decidable.intro (p b r : FExpr) : FExpr :=
  .ctor C.Decidable_ 0 0 #[] #[p] #[b, r] #[]

@[fexpr_unfold]
protected def Decidable.reflects_decide (p d : FExpr) : FExpr :=
  .appList (.const C.Decidable_reflects_decide #[]) [p, d]

end FExpr

namespace Decide.Structure

variable (F : FEnv) (hints : PArray Export.Hints)

namespace Dite

variable (C : Consts)

def congr : Schema :=
  schema% (P : prop) (d : FExpr.Decidable C P) (t : P ⟶ nat C.Nat_)
      (e : FExpr.Not C P ⟶ nat C.Nat_) ⊢
    FExpr.dite C (nat C.Nat_) P d t e : nat C.Nat_

def intro : Schema :=
  schema% (P : prop) (β : bool C.Bool_) (r : FExpr.Bool.Reflects C β P) (t : P ⟶ nat C.Nat_)
      (e : FExpr.Not C P ⟶ nat C.Nat_) ⊢
    FExpr.dite C (nat C.Nat_) P (FExpr.Decidable.intro C P β r) t e : nat C.Nat_

def reflectsCongr : Schema :=
  schema% (P : prop) (β : bool C.Bool_) ⊢ FExpr.Bool.Reflects C β P : prop

def lit (v : Bool) : Schema :=
  schema% (P : prop) (r : FExpr.Bool.Reflects C (boolLit C.Bool_ v) P) (t : P ⟶ nat C.Nat_)
      (e : FExpr.Not C P ⟶ nat C.Nat_) ⊢
    FExpr.dite C (nat C.Nat_) P (FExpr.Decidable.intro C P (boolLit C.Bool_ v) r) t e ≡
      .app (cond v t e) r :
    nat C.Nat_

def reflectsLit (v : Bool) : Schema :=
  schema% (P : prop) ⊢
    FExpr.Bool.Reflects C (boolLit C.Bool_ v) P ≡ cond v P (FExpr.Not C P) : prop

structure Spec : Prop where
  congr : (congr C).Spec F
  intro : (intro C).Spec F
  reflectsCongr : (reflectsCongr C).Spec F
  lit : ∀ v, (lit C v).Spec F
  reflectsLit : ∀ v, (reflectsLit C v).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨congr⟩ ← (congr C).check F hints
  let ⟨intro⟩ ← (intro C).check F hints
  let ⟨reflectsCongr⟩ ← (reflectsCongr C).check F hints
  let ⟨lit⟩ ← checkBools fun v => (lit C v).check F hints
  let ⟨reflectsLit⟩ ← checkBools fun v => (reflectsLit C v).check F hints
  pure ⟨⟨congr, intro, reflectsCongr, lit, reflectsLit⟩⟩

variable {F C} {ζ : Sigs} {E : Env ζ}

theorem Spec.reduces (h : Spec F C) (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {P d β t e : FExpr} {v : Bool} (hP : FEq E P P prop)
    (ht : FEq E t t (P ⟶ nat C.Nat_)) (he : FEq E e e (FExpr.Not C P ⟶ nat C.Nat_))
    (hd : FEq E d (FExpr.Decidable.intro C P β (FExpr.Decidable.reflects_decide C P d))
      (FExpr.Decidable C P))
    (hr : FEq E (FExpr.Decidable.reflects_decide C P d)
      (FExpr.Decidable.reflects_decide C P d) (FExpr.Bool.Reflects C β P))
    (hβ : FEq E β (boolLit C.Bool_ v) (bool C.Bool_)) :
    ∃ p : FExpr, FEq E p p (cond v P (FExpr.Not C P)) ∧
      FEq E (FExpr.dite C (nat C.Nat_) P d t e) (.app (cond v t e) p) (nat C.Nat_) := by
  schema_have c₁ := h.congr Dite.congr #[P, d, t, e]
    #[P, FExpr.Decidable.intro C P β (FExpr.Decidable.reflects_decide C P d), t, e]
    using hP, hd, ht, he
  schema_have c₂ := h.intro Dite.intro #[P, β, FExpr.Decidable.reflects_decide C P d, t, e]
    #[P, boolLit C.Bool_ v, FExpr.Decidable.reflects_decide C P d, t, e]
    using hP, hβ, hr, ht, he
  schema_have hty := h.reflectsCongr Dite.reflectsCongr #[P, β] #[P, boolLit C.Bool_ v]
    using hP, hβ
  have hr' := hr.conv hty
  have hlit := h.lit v
  have hreflects := h.reflectsLit v
  cases v <;>
  · schema_have hty' := hreflects Dite.reflectsLit #[P] #[P] using hP
    schema_have c₃ := hlit Dite.lit #[P, FExpr.Decidable.reflects_decide C P d, t, e]
      #[P, FExpr.Decidable.reflects_decide C P d, t, e] using hP, hr', ht, he
    exact ⟨_, hr'.conv hty', c₁.trans (c₂.trans c₃)⟩

end Dite

namespace Le

structure Consts extends toLeConsts : Decide.LeConsts, toBase : Structure.Consts where
  protected Nat_ble : Nat

instance : CoeOut Consts Decide.LeConsts := ⟨Consts.toLeConsts⟩

instance : CoeOut Consts Structure.Consts := ⟨Consts.toBase⟩

variable (C : Consts)

def propType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢ FExpr.Nat.le C y x : prop

def unfold : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Nat.decLe C y x ≡
      FExpr.Decidable.intro C (FExpr.Nat.le C y x) (op₂ C.Nat_ble y x)
        (FExpr.Decidable.reflects_decide C (FExpr.Nat.le C y x) (FExpr.Nat.decLe C y x)) :
    FExpr.Decidable C (FExpr.Nat.le C y x)

def reflects : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Decidable.reflects_decide C (FExpr.Nat.le C y x) (FExpr.Nat.decLe C y x) :
    FExpr.Bool.Reflects C (op₂ C.Nat_ble y x) (FExpr.Nat.le C y x)

structure Spec : Prop where
  propType : (propType C).Spec F
  unfold : (unfold C).Spec F
  reflects : (reflects C).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨propType⟩ ← (propType C).check F hints
  let ⟨unfold⟩ ← (unfold C).check F hints
  let ⟨reflects⟩ ← (reflects C).check F hints
  pure ⟨⟨propType, unfold, reflects⟩⟩

variable {F C}

theorem Spec.decLe (h : Spec F C) (hd : Dite.Spec F C) (hn : NatSpec F C.Nat_)
    (hble : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_ble Nat.ble) :
    DecLe F C.toLeConsts := by
  intro b a _ _ hF hE _ _ ht he
  have hB := FEq.natLit hF hn b
  have hA := FEq.natLit hF hn a
  have hβ := FEq.boolOp hF hE hn hble b a
  schema_have hP := h.propType Le.propType #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have hdec := h.unfold Le.unfold #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  schema_have hr := h.reflects Le.reflects #[.natLit C.Nat_ b, .natLit C.Nat_ a] #[.natLit C.Nat_ b, .natLit C.Nat_ a]
    using hB, hA
  exact hd.reduces hF hE hP ht he hdec hr hβ

end Le

def verifyDecLe (D : Decide.LeConsts) (t : Table) (ble : BoolOp F Nat.ble) :
    EIO Failure (PLift (DecLe F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let C : Le.Consts := { D with
    Bool_ := ble.bool
    Nat_ble := ble.pos
    Bool_Reflects := ← t.const ``Bool.Reflects
    Decidable_reflects_decide := ← t.const ``Decidable.reflects_decide }
  let ⟨h⟩ ← Le.check F hints C
  let ⟨hd⟩ ← Dite.check F hints C
  let ⟨hble⟩ ← ble.at F C.Nat_ C.Bool_
  pure ⟨h.decLe hd hn hble⟩

namespace EqNat

structure Consts extends toEqNatConsts : Decide.EqNatConsts, toBase : Structure.Consts where
  protected Nat_beq : Nat

instance : CoeOut Consts Decide.EqNatConsts := ⟨Consts.toEqNatConsts⟩

instance : CoeOut Consts Structure.Consts := ⟨Consts.toBase⟩

variable (C : Consts)

def propType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢ FExpr.Eq C (nat C.Nat_) y x : prop

def unfold : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.instDecidableEqNat C y x ≡
      FExpr.Decidable.intro C (FExpr.Eq C (nat C.Nat_) y x) (op₂ C.Nat_beq y x)
        (FExpr.Decidable.reflects_decide C (FExpr.Eq C (nat C.Nat_) y x)
          (FExpr.instDecidableEqNat C y x)) :
    FExpr.Decidable C (FExpr.Eq C (nat C.Nat_) y x)

def reflects : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Decidable.reflects_decide C (FExpr.Eq C (nat C.Nat_) y x)
      (FExpr.instDecidableEqNat C y x) :
    FExpr.Bool.Reflects C (op₂ C.Nat_beq y x) (FExpr.Eq C (nat C.Nat_) y x)

structure Spec : Prop where
  propType : (propType C).Spec F
  unfold : (unfold C).Spec F
  reflects : (reflects C).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨propType⟩ ← (propType C).check F hints
  let ⟨unfold⟩ ← (unfold C).check F hints
  let ⟨reflects⟩ ← (reflects C).check F hints
  pure ⟨⟨propType, unfold, reflects⟩⟩

variable {F C}

theorem Spec.decEqNat (h : Spec F C) (hd : Dite.Spec F C) (hn : NatSpec F C.Nat_)
    (hbeq : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_beq Nat.beq) :
    DecEqNat F C.toEqNatConsts := by
  intro a b _ _ hF hE _ _ ht he
  have hA := FEq.natLit hF hn a
  have hB := FEq.natLit hF hn b
  have hβ := FEq.boolOp hF hE hn hbeq a b
  schema_have hP := h.propType EqNat.propType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have hdec := h.unfold EqNat.unfold #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  schema_have hr := h.reflects EqNat.reflects #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  exact hd.reduces hF hE hP ht he hdec hr hβ

end EqNat

def verifyDecEqNat (D : Decide.EqNatConsts) (t : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecEqNat F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let C : EqNat.Consts := { D with
    Bool_ := beq.bool
    Nat_beq := beq.pos
    Bool_Reflects := ← t.const ``Bool.Reflects
    Decidable_reflects_decide := ← t.const ``Decidable.reflects_decide }
  let ⟨h⟩ ← EqNat.check F hints C
  let ⟨hd⟩ ← Dite.check F hints C
  let ⟨hbeq⟩ ← beq.at F C.Nat_ C.Bool_
  pure ⟨h.decEqNat hd hn hbeq⟩

namespace EqBool

structure Consts extends toEqBoolConsts : Decide.EqBoolConsts, toBase : Structure.Consts

instance : CoeOut Consts Decide.EqBoolConsts := ⟨Consts.toEqBoolConsts⟩

instance : CoeOut Consts Structure.Consts := ⟨Consts.toBase⟩

variable (C : Consts)

def propType (β γ : Bool) : Schema :=
  schema% ⊢ FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ) : prop

def unfold (β γ : Bool) : Schema :=
  schema% ⊢
    FExpr.instDecidableEqBool C (boolLit C.Bool_ β) (boolLit C.Bool_ γ) ≡
      FExpr.Decidable.intro C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ))
        (boolLit C.Bool_ (β == γ))
        (FExpr.Decidable.reflects_decide C
          (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ))
          (FExpr.instDecidableEqBool C (boolLit C.Bool_ β) (boolLit C.Bool_ γ))) :
    FExpr.Decidable C (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ))

def reflects (β γ : Bool) : Schema :=
  schema% ⊢
    FExpr.Decidable.reflects_decide C
      (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ))
      (FExpr.instDecidableEqBool C (boolLit C.Bool_ β) (boolLit C.Bool_ γ)) :
    FExpr.Bool.Reflects C (boolLit C.Bool_ (β == γ))
      (FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ β) (boolLit C.Bool_ γ))

structure Spec : Prop where
  propType : ∀ β γ, (propType C β γ).Spec F
  unfold : ∀ β γ, (unfold C β γ).Spec F
  reflects : ∀ β γ, (reflects C β γ).Spec F
  boolLitType : ∀ v, (boolLitType C.Bool_ v).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨propType⟩ ← checkBools fun β => checkBools fun γ => (propType C β γ).check F hints
  let ⟨unfold⟩ ← checkBools fun β => checkBools fun γ => (unfold C β γ).check F hints
  let ⟨reflects⟩ ← checkBools fun β => checkBools fun γ => (reflects C β γ).check F hints
  let ⟨boolLitType⟩ ← checkBools fun v => (boolLitType C.Bool_ v).check F hints
  pure ⟨⟨propType, unfold, reflects, boolLitType⟩⟩

variable {F C}

theorem Spec.decEqBool (h : Spec F C) (hd : Dite.Spec F C) :
    DecEqBool F C.toEqBoolConsts := by
  intro β γ _ _ hF hE _ _ ht he
  exact hd.reduces hF hE (Schema.Spec.closed (h.propType β γ) hF hE) ht he
    (Schema.Spec.closed (h.unfold β γ) hF hE) (Schema.Spec.closed (h.reflects β γ) hF hE)
    (Schema.Spec.closed (h.boolLitType (β == γ)) hF hE)

end EqBool

def verifyDecEqBool (D : Decide.EqBoolConsts) (t : Table) :
    EIO Failure (PLift (DecEqBool F D)) := do
  let C : EqBool.Consts := { D with
    Bool_Reflects := ← t.const ``Bool.Reflects
    Decidable_reflects_decide := ← t.const ``Decidable.reflects_decide }
  let ⟨h⟩ ← EqBool.check F hints C
  let ⟨hd⟩ ← Dite.check F hints C
  pure ⟨h.decEqBool hd⟩

namespace DecideEqNat

structure Consts extends toDecideConsts : Decide.DecideConsts where
  protected Nat_beq : Nat

variable (C : Consts)

def unfold : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    FExpr.Decidable.decide C.toDecideConsts (FExpr.Eq C.toDecideConsts (nat C.Nat_) y x)
        (FExpr.instDecidableEqNat C.toDecideConsts y x) ≡
      op₂ C.Nat_beq y x :
    bool C.Bool_

structure Spec : Prop where
  unfold : (unfold C).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨unfold⟩ ← (unfold C).check F hints
  pure ⟨⟨unfold⟩⟩

variable {F C}

theorem Spec.decideEqNat (h : Spec F C) (hn : NatSpec F C.Nat_)
    (hbeq : BoolOpSpec F C.Nat_ C.Bool_ C.Nat_beq Nat.beq) :
    DecideEqNat F C.toDecideConsts := by
  intro _ _ hF hE a b
  have hA := FEq.natLit hF hn a
  have hB := FEq.natLit hF hn b
  schema_have c := h.unfold DecideEqNat.unfold #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using hA, hB
  exact c.trans (FEq.boolOp hF hE hn hbeq a b)

end DecideEqNat

def verifyDecideEqNat (D : Decide.DecideConsts) (_ : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecideEqNat F D)) := do
  let ⟨hn⟩ ← D.natSpec F
  let ⟨hbeq⟩ ← beq.at F D.Nat_ D.Bool_
  let C : DecideEqNat.Consts := { D with Nat_beq := beq.pos }
  let ⟨h⟩ ← DecideEqNat.check F hints C
  pure ⟨h.decideEqNat hn hbeq⟩

end Decide.Structure

end Metalean.Checker.Fast
