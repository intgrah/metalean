/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Fuel

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace NatFix

structure Consts extends toFuel : Fuel.Consts, toEqNatConsts : Decide.EqNatConsts,
    toEqBoolConsts : Decide.EqBoolConsts where
  protected PSigma_ : Nat
  protected PSigma_casesOn : Nat
  protected WellFounded_Nat_fix_go : Nat
  protected WellFounded_Nat_eager : Nat
  protected Nat_lt_of_lt_of_le : Nat
  protected Nat_le_of_lt_succ : Nat

instance : CoeOut Consts Fuel.Consts := ⟨Consts.toFuel⟩

instance : CoeOut Consts Decide.EqNatConsts := ⟨Consts.toEqNatConsts⟩

instance : CoeOut Consts Decide.EqBoolConsts := ⟨Consts.toEqBoolConsts⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    toFuel := ← Fuel.Consts.resolve t
    instDecidableEqNat := ← t.const ``instDecidableEqNat
    Bool_ := ← t.ind ``Bool
    instDecidableEqBool := ← t.const ``instDecidableEqBool
    PSigma_ := ← t.ind ``PSigma
    PSigma_casesOn := ← t.const ``PSigma.casesOn
    WellFounded_Nat_fix_go := ← t.const ``WellFounded.Nat.fix.go
    WellFounded_Nat_eager := ← t.const ``WellFounded.Nat.eager
    Nat_lt_of_lt_of_le := ← t.const ``Nat.lt_of_lt_of_le
    Nat_le_of_lt_succ := ← t.const ``Nat.le_of_lt_succ }

end NatFix

namespace FExpr

variable (C : NatFix.Consts)

/-- `PSigma` at `Sort 1`, `Sort 1` -/
@[fexpr_unfold]
protected def PSigma (α β : FExpr) : FExpr :=
  .ind C.PSigma_ 0 #[.succ .zero, .succ .zero] #[α, β] #[]

@[fexpr_unfold]
protected def PSigma.mk (α β a b : FExpr) : FExpr :=
  .ctor C.PSigma_ 0 0 #[.succ .zero, .succ .zero] #[α, β] #[a, b] #[]

/-- `PSigma.casesOn` into `Sort 1` -/
@[fexpr_unfold]
protected def PSigma.casesOn (α β motive t mk : FExpr) : FExpr :=
  .appList (.const C.PSigma_casesOn #[.succ .zero, .succ .zero, .succ .zero]) [α, β, motive, t, mk]

@[fexpr_unfold]
protected def WellFounded.Nat.fix.go (α motive h F fuel x hx : FExpr) : FExpr :=
  .appList (.const C.WellFounded_Nat_fix_go #[.succ .zero, .succ .zero])
    [α, motive, h, F, fuel, x, hx]

@[fexpr_unfold]
protected def WellFounded.Nat.eager (n : FExpr) : FExpr :=
  .app (.const C.WellFounded_Nat_eager #[]) n

@[fexpr_unfold]
protected def Nat.lt_of_lt_of_le (n m k h₁ h₂ : FExpr) : FExpr :=
  .appList (.const C.Nat_lt_of_lt_of_le #[]) [n, m, k, h₁, h₂]

@[fexpr_unfold]
protected def Nat.le_of_lt_succ (m n h : FExpr) : FExpr :=
  .appList (.const C.Nat_le_of_lt_succ #[]) [m, n, h]

end FExpr

namespace NatFix

scoped notation "Σℕ" => (_ : Nat) ×' Nat

scoped notation "μ₀" =>
  fun x : (_ : Nat) ×' Nat => PSigma.casesOn (motive := fun _ => Nat) x fun m _ => m

variable (F : FEnv) (C : Consts)

/-- `(_ : Nat) ×' Nat` -/
@[fexpr_unfold]
def sig : FExpr :=
  FExpr.PSigma C (nat C.Nat_) (.lam (nat C.Nat_) (nat C.Nat_))

@[fexpr_unfold]
def pair (m n : FExpr) : FExpr :=
  FExpr.PSigma.mk C (nat C.Nat_) (.lam (nat C.Nat_) (nat C.Nat_)) m n

/-- `fun x => PSigma.casesOn x fun m _ => m` -/
@[fexpr_unfold]
def measure : FExpr :=
  .lam (sig C) (FExpr.PSigma.casesOn C (nat C.Nat_) (.lam (nat C.Nat_) (nat C.Nat_))
    (.lam (sig C) (nat C.Nat_)) (.bvar 0) (.lam (nat C.Nat_) (.lam (nat C.Nat_) (.bvar 1))))

/-- `a < b` -/
@[fexpr_unfold]
def lt (a b : FExpr) : FExpr :=
  FExpr.Nat.le C (succ C.Nat_ a) b

@[fexpr_unfold]
def μ (x : FExpr) : FExpr :=
  .app (measure C) x

/-- `(y : (_ : Nat) ×' Nat) → μ y < μ x → Nat` -/
@[fexpr_unfold]
def recTy (x : FExpr) : FExpr :=
  sig C ⟶ lt C (μ C (.bvar 0)) (μ C x) ⟶ nat C.Nat_

/-- `(x : (_ : Nat) ×' Nat) → ((y : (_ : Nat) ×' Nat) → μ y < μ x → Nat) → Nat` -/
@[fexpr_unfold]
def funTy : FExpr :=
  sig C ⟶ recTy C (.bvar 1) ⟶ nat C.Nat_

@[fexpr_unfold]
def go (G fuel x h : FExpr) : FExpr :=
  FExpr.WellFounded.Nat.fix.go C (sig C) (.lam (sig C) (nat C.Nat_)) (measure C) G fuel x h

@[fexpr_unfold]
def recProof (k x hx y hy : FExpr) : FExpr :=
  FExpr.Nat.lt_of_lt_of_le C (μ C y) (μ C x) k hy (FExpr.Nat.le_of_lt_succ C (μ C x) k hx)

/-- `fun y hy => go G k y (recProof k x hx y hy)` -/
@[fexpr_unfold]
def recursion (G k x hx : FExpr) : FExpr :=
  .lam (sig C) (.lam (lt C (μ C (.bvar 0)) (μ C x))
    (go C G k (.bvar 1) (recProof C k x hx (.bvar 1) (.bvar 0))))

/-- `dite P d (fun _ => x) (fun _ => y)` at `Nat` -/
@[fexpr_unfold]
def cdite (P d x y : FExpr) : FExpr :=
  FExpr.dite C (nat C.Nat_) P d (.lam P x) (.lam (FExpr.Not C P) y)

/-- `if _ : t = true then x else y` at `Nat` -/
@[fexpr_unfold]
def ifTrue (t x y : FExpr) : FExpr :=
  cdite C (FExpr.Eq C (bool C.Bool_) t (boolLit C.Bool_ true))
    (FExpr.instDecidableEqBool C t (boolLit C.Bool_ true)) x y

/-- `fun m n R => G ⟨m, n⟩ R` -/
@[fexpr_unfold]
def stepLam (G : FExpr) : FExpr :=
  .lam (nat C.Nat_) (.lam (nat C.Nat_) (.lam (recTy C (pair C (.bvar 2) (.bvar 1)))
    (.appList G [pair C (.bvar 2) (.bvar 1), .bvar 0])))

@[fexpr_unfold]
def stepTy : FExpr :=
  nat C.Nat_ ⟶ nat C.Nat_ ⟶ recTy C (pair C (.bvar 2) (.bvar 1)) ⟶ nat C.Nat_

@[fexpr_unfold]
def fuelTy : FExpr :=
  nat C.Nat_ ⟶ nat C.Nat_ ⟶
  lt C (.bvar 1) (FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.bvar 1))) ⟶ nat C.Nat_

/-- `fun m n _ => op m n` -/
@[fexpr_unfold]
def opLam (pos : Nat) : FExpr :=
  .lam (nat C.Nat_) (.lam (nat C.Nat_)
    (.lam (lt C (.bvar 1) (FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.bvar 1))))
      (op₂ pos (.bvar 2) (.bvar 1))))

/-- `fun m n π => go G (eager (m + 1)) ⟨m, n⟩ π` -/
@[fexpr_unfold]
def goLam (G : FExpr) : FExpr :=
  .lam (nat C.Nat_) (.lam (nat C.Nat_)
    (.lam (lt C (.bvar 1) (FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.bvar 1))))
      (go C G (FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.bvar 2)))
        (pair C (.bvar 2) (.bvar 1)) (.bvar 0))))

@[fexpr_unfold]
def app₃ (f a b c : FExpr) : FExpr :=
  .appList f [a, b, c]

def goStep : Schema :=
  schema% (G : funTy C) (k : nat C.Nat_) (x : sig C) (hx : lt C (μ C x) (succ C.Nat_ k)) ⊢
    go C G (succ C.Nat_ k) x hx ≡ (.appList G [x, recursion C G k x hx]) : nat C.Nat_

def recursionType : Schema :=
  schema% (G : funTy C) (k : nat C.Nat_) (x : sig C) (hx : lt C (μ C x) (succ C.Nat_ k)) ⊢
    recursion C G k x hx : recTy C x

def recursionBeta : Schema :=
  schema% (G : funTy C) (k : nat C.Nat_) (x : sig C) (hx : lt C (μ C x) (succ C.Nat_ k))
      (y : sig C) (hy : lt C (μ C y) (μ C x)) ⊢
    (.appList (recursion C G k x hx) [y, hy]) ≡ go C G k y (recProof C k x hx y hy) : nat C.Nat_

def recProofType : Schema :=
  schema% (k : nat C.Nat_) (x : sig C) (hx : lt C (μ C x) (succ C.Nat_ k)) (y : sig C)
      (hy : lt C (μ C y) (μ C x)) ⊢
    recProof C k x hx y hy : lt C (μ C y) k

def goCongr : Schema :=
  schema% (G : funTy C) (k : nat C.Nat_) (x : sig C) (h : lt C (μ C x) k) ⊢
    go C G k x h : nat C.Nat_

def pairCongr : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_) ⊢ pair C m n : sig C

def ltCongr : Schema :=
  schema% (x : sig C) (k : nat C.Nat_) ⊢ lt C (μ C x) k : prop

def ltMeasure : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_) (k : nat C.Nat_) ⊢
    lt C (μ C (pair C m n)) k ≡ lt C m k : prop

def eagerUnfold (beq : Nat) : Schema :=
  schema% (x : nat C.Nat_) ⊢
    FExpr.WellFounded.Nat.eager C x ≡ ifTrue C (op₂ beq x x) x x : nat C.Nat_

def eagerCongr : Schema :=
  schema% (x : nat C.Nat_) ⊢ FExpr.WellFounded.Nat.eager C x : nat C.Nat_

def cditeCongr : Schema :=
  schema% (P : prop) (d : FExpr.Decidable C P) (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    cdite C P d x y : nat C.Nat_

def constLamType : Schema :=
  schema% (P : prop) (x : nat C.Nat_) ⊢ .lam P x : P ⟶ nat C.Nat_

def constBeta : Schema :=
  schema% (P : prop) (x : nat C.Nat_) (p : P) ⊢ .app (.lam P x) p ≡ x : nat C.Nat_

def notType : Schema :=
  schema% (P : prop) ⊢ FExpr.Not C P : prop

def eqNatType : Schema :=
  schema% (a : nat C.Nat_) (b : nat C.Nat_) ⊢ FExpr.Eq C (nat C.Nat_) a b : prop

def eqBoolType : Schema :=
  schema% (β : bool C.Bool_) (γ : bool C.Bool_) ⊢ FExpr.Eq C (bool C.Bool_) β γ : prop

def decEqBoolType : Schema :=
  schema% (β : bool C.Bool_) (γ : bool C.Bool_) ⊢
    FExpr.instDecidableEqBool C β γ : FExpr.Decidable C (FExpr.Eq C (bool C.Bool_) β γ)

def trueType : Schema :=
  schema% ⊢ boolLit C.Bool_ true : bool C.Bool_

def stepBeta : Schema :=
  schema% (G : funTy C) (m : nat C.Nat_) (n : nat C.Nat_) (R : recTy C (pair C m n)) ⊢
    app₃ (stepLam C G) m n R ≡ (.appList G [pair C m n, R]) : nat C.Nat_

def stepCongr : Schema :=
  schema% (f : stepTy C) (m : nat C.Nat_) (n : nat C.Nat_) (R : recTy C (pair C m n)) ⊢
    app₃ f m n R : nat C.Nat_

def goLamBeta : Schema :=
  schema% (G : funTy C) (m : nat C.Nat_) (n : nat C.Nat_)
      (π : lt C m (FExpr.WellFounded.Nat.eager C (succ C.Nat_ m))) ⊢
    app₃ (goLam C G) m n π ≡
      go C G (FExpr.WellFounded.Nat.eager C (succ C.Nat_ m)) (pair C m n) π :
    nat C.Nat_

def fuelCongr : Schema :=
  schema% (f : fuelTy C) (m : nat C.Nat_) (n : nat C.Nat_)
      (π : lt C m (FExpr.WellFounded.Nat.eager C (succ C.Nat_ m))) ⊢
    app₃ f m n π : nat C.Nat_

def opLamBeta (pos : Nat) : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_)
      (π : lt C m (FExpr.WellFounded.Nat.eager C (succ C.Nat_ m))) ⊢
    app₃ (opLam C pos) m n π ≡ op₂ pos m n : nat C.Nat_

def funType (G : FExpr) : Schema :=
  schema% ⊢ G : funTy C

def unfold (pos : Nat) (G : FExpr) : Schema :=
  schema% ⊢ opLam C pos ≡ goLam C G : fuelTy C

def step (G B : FExpr) : Schema :=
  schema% ⊢ stepLam C G ≡ B : stepTy C

structure Spec (beq : Nat) : Prop where
  goStep : (goStep C).Spec F
  recursionType : (recursionType C).Spec F
  recursionBeta : (recursionBeta C).Spec F
  recProofType : (recProofType C).Spec F
  goCongr : (goCongr C).Spec F
  pairCongr : (pairCongr C).Spec F
  ltCongr : (ltCongr C).Spec F
  ltMeasure : (ltMeasure C).Spec F
  eagerUnfold : (eagerUnfold C beq).Spec F
  eagerCongr : (eagerCongr C).Spec F
  cditeCongr : (cditeCongr C).Spec F
  constLamType : (constLamType C).Spec F
  constBeta : (constBeta C).Spec F
  notType : (notType C).Spec F
  eqNatType : (eqNatType C).Spec F
  eqBoolType : (eqBoolType C).Spec F
  decEqBoolType : (decEqBoolType C).Spec F
  trueType : (trueType C).Spec F
  stepBeta : (stepBeta C).Spec F
  stepCongr : (stepCongr C).Spec F
  goLamBeta : (goLamBeta C).Spec F
  fuelCongr : (fuelCongr C).Spec F

/-- `op` at `pos` unfolds to `WellFounded.Nat.fix` of `G`, whose step is `B` -/
structure FixSpec (pos : Nat) (G B : FExpr) : Prop where
  funType : (funType C G).Spec F
  unfold : (unfold C pos G).Spec F
  opLamBeta : (opLamBeta C pos).Spec F
  step : (step C G B).Spec F

variable (hints : Array Export.Hints)

def check (beq : Nat) : EIO Failure (PLift (Spec F C beq)) := do
  let ⟨goStep⟩ ← (goStep C).check F hints
  let ⟨recursionType⟩ ← (recursionType C).check F hints
  let ⟨recursionBeta⟩ ← (recursionBeta C).check F hints
  let ⟨recProofType⟩ ← (recProofType C).check F hints
  let ⟨goCongr⟩ ← (goCongr C).check F hints
  let ⟨pairCongr⟩ ← (pairCongr C).check F hints
  let ⟨ltCongr⟩ ← (ltCongr C).check F hints
  let ⟨ltMeasure⟩ ← (ltMeasure C).check F hints
  let ⟨eagerUnfold⟩ ← (eagerUnfold C beq).check F hints
  let ⟨eagerCongr⟩ ← (eagerCongr C).check F hints
  let ⟨cditeCongr⟩ ← (cditeCongr C).check F hints
  let ⟨constLamType⟩ ← (constLamType C).check F hints
  let ⟨constBeta⟩ ← (constBeta C).check F hints
  let ⟨notType⟩ ← (notType C).check F hints
  let ⟨eqNatType⟩ ← (eqNatType C).check F hints
  let ⟨eqBoolType⟩ ← (eqBoolType C).check F hints
  let ⟨decEqBoolType⟩ ← (decEqBoolType C).check F hints
  let ⟨trueType⟩ ← (trueType C).check F hints
  let ⟨stepBeta⟩ ← (stepBeta C).check F hints
  let ⟨stepCongr⟩ ← (stepCongr C).check F hints
  let ⟨goLamBeta⟩ ← (goLamBeta C).check F hints
  let ⟨fuelCongr⟩ ← (fuelCongr C).check F hints
  pure ⟨⟨goStep, recursionType, recursionBeta, recProofType, goCongr, pairCongr, ltCongr,
    ltMeasure, eagerUnfold, eagerCongr, cditeCongr, constLamType, constBeta, notType, eqNatType,
    eqBoolType, decEqBoolType, trueType, stepBeta, stepCongr, goLamBeta, fuelCongr⟩⟩

def checkFix (pos : Nat) (G B : FExpr) : EIO Failure (PLift (FixSpec F C pos G B)) := do
  let ⟨funType⟩ ← (funType C G).check F hints
  let ⟨unfold⟩ ← (unfold C pos G).check F hints
  let ⟨opLamBeta⟩ ← (opLamBeta C pos).check F hints
  let ⟨step⟩ ← (step C G B).check F hints
  pure ⟨⟨funType, unfold, opLamBeta, step⟩⟩

variable {ζ : Sigs} (E : Env ζ)

/-- `B` computes `f` on literals when `R` computes `f` on pairs of smaller measure -/
def BodyEval (B : FExpr) (f : Nat → Nat → Nat) : Prop :=
  ∀ a b R,
  FEq E R R (recTy C (pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b))) →
  (∀ ⦃y hy : FExpr⦄ ⦃a' b' : Nat⦄, a' < a →
    FEq E y (pair C (.natLit C.Nat_ a') (.natLit C.Nat_ b')) (sig C) →
    FEq E hy hy (lt C (μ C y) (μ C (pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b)))) →
    FEq E (.appList R [y, hy]) (.natLit C.Nat_ (f a' b')) (nat C.Nat_)) →
  FEq E (app₃ B (.natLit C.Nat_ a) (.natLit C.Nat_ b) R) (.natLit C.Nat_ (f a b)) (nat C.Nat_)

section

variable {F C E} {beq : Nat} (h : Spec F C beq) (hF : FEnv.Denotes F E) (hE : EnvWF E)
  (hn : NatSpec F C.Nat_)

include h hF hE in
theorem Spec.cditeReduce {P d x y : FExpr} {holds : Bool}
    (hr : Decide.Reduces F C P d holds) (hp : FEq E P P prop)
    (hx : FEq E x x (nat C.Nat_)) (hy : FEq E y y (nat C.Nat_)) :
    FEq E (cdite C P d x y) (cond holds x y) (nat C.Nat_) := by
  schema_have ht := h.constLamType NatFix.constLamType #[P, x] #[P, x] using hp, hx
  schema_have hnp := h.notType NatFix.notType #[P] #[P] using hp
  schema_have he := h.constLamType NatFix.constLamType #[FExpr.Not C P, y] #[FExpr.Not C P, y]
    using hnp, hy
  have ⟨q, hq, c⟩ := hr hF hE ht he
  cases holds with
  | false =>
    schema_have c' := h.constBeta NatFix.constBeta #[FExpr.Not C P, y, q] #[FExpr.Not C P, y, q]
      using hnp, hy, hq
    exact c.trans c'
  | true =>
    schema_have c' := h.constBeta NatFix.constBeta #[P, x, q] #[P, x, q] using hp, hx, hq
    exact c.trans c'

include h hF hE in
theorem Spec.ifTrueEval (hdb : Decide.DecEqBool F C) {t x y : FExpr} {v : Bool} {m n : Nat}
    (ht : FEq E t (boolLit C.Bool_ v) (bool C.Bool_))
    (hx : FEq E x (.natLit C.Nat_ m) (nat C.Nat_)) (hy : FEq E y (.natLit C.Nat_ n) (nat C.Nat_)) :
    FEq E (ifTrue C t x y) (.natLit C.Nat_ (cond v m n)) (nat C.Nat_) := by
  have htrue := Schema.Spec.closed h.trueType hF hE
  schema_have hp := h.eqBoolType NatFix.eqBoolType #[t, boolLit C.Bool_ true]
    #[boolLit C.Bool_ v, boolLit C.Bool_ true] using ht, htrue
  schema_have hd := h.decEqBoolType NatFix.decEqBoolType #[t, boolLit C.Bool_ true]
    #[boolLit C.Bool_ v, boolLit C.Bool_ true] using ht, htrue
  schema_have c₁ := h.cditeCongr NatFix.cditeCongr
    #[FExpr.Eq C (bool C.Bool_) t (boolLit C.Bool_ true),
      FExpr.instDecidableEqBool C t (boolLit C.Bool_ true), x, y]
    #[FExpr.Eq C (bool C.Bool_) (boolLit C.Bool_ v) (boolLit C.Bool_ true),
      FExpr.instDecidableEqBool C (boolLit C.Bool_ v) (boolLit C.Bool_ true), x, y]
    using hp, hd, hx.left, hy.left
  have c₂ := h.cditeReduce hF hE (hdb v true) hp.symm.left hx.left hy.left
  cases v
  · exact c₁.trans (c₂.trans hy)
  · exact c₁.trans (c₂.trans hx)

include h hF hE hn in
theorem Spec.goSucc {G x q : FExpr} (hg : FEq E G G (funTy C)) (hx : FEq E x x (sig C))
    (k : Nat) (hq : FEq E q q (lt C (μ C x) (.natLit C.Nat_ (k + 1)))) :
    ∃ R : FExpr, FEq E R R (recTy C x) ∧
      FEq E (go C G (.natLit C.Nat_ (k + 1)) x q) (.appList G [x, R]) (nat C.Nat_) ∧
      ∀ ⦃y₁ y₂ r : FExpr⦄, FEq E y₁ y₂ (sig C) →
        FEq E r r (lt C (μ C y₁) (μ C x)) →
        ∃ s : FExpr, FEq E s s (lt C (μ C y₂) (.natLit C.Nat_ k)) ∧
          FEq E (.appList R [y₁, r]) (go C G (.natLit C.Nat_ k) y₂ s) (nat C.Nat_) := by
  have hk := FEq.natLit hF hn k
  have hk₁ := (FEq.succLit hF hn k).symm
  schema_have hlt := h.ltCongr NatFix.ltCongr #[x, .natLit C.Nat_ (k + 1)] #[x, succ C.Nat_ (.natLit C.Nat_ k)]
    using hx, hk₁
  have hq' := hq.conv hlt
  schema_have c₀ := h.goCongr NatFix.goCongr #[G, .natLit C.Nat_ (k + 1), x, q]
    #[G, succ C.Nat_ (.natLit C.Nat_ k), x, q] using hg, hk₁, hx, hq
  schema_have c₁ := h.goStep NatFix.goStep #[G, .natLit C.Nat_ k, x, q] #[G, .natLit C.Nat_ k, x, q]
    using hg, hk, hx, hq'
  schema_have hr := h.recursionType NatFix.recursionType #[G, .natLit C.Nat_ k, x, q]
    #[G, .natLit C.Nat_ k, x, q] using hg, hk, hx, hq'
  refine ⟨_, hr, c₀.trans c₁, fun y₁ y₂ r hy hr => ?_⟩
  schema_have hs := h.recProofType NatFix.recProofType #[.natLit C.Nat_ k, x, q, y₁, r]
    #[.natLit C.Nat_ k, x, q, y₁, r] using hk, hx, hq', hy.left, hr
  schema_have hlt' := h.ltCongr NatFix.ltCongr #[y₁, .natLit C.Nat_ k] #[y₂, .natLit C.Nat_ k] using hy, hk
  schema_have c₂ := h.recursionBeta NatFix.recursionBeta #[G, .natLit C.Nat_ k, x, q, y₁, r]
    #[G, .natLit C.Nat_ k, x, q, y₁, r] using hg, hk, hx, hq', hy.left, hr
  schema_have c₃ := h.goCongr NatFix.goCongr #[G, .natLit C.Nat_ k, y₁, recProof C (.natLit C.Nat_ k) x q y₁ r]
    #[G, .natLit C.Nat_ k, y₂, recProof C (.natLit C.Nat_ k) x q y₁ r] using hg, hk, hy, hs
  exact ⟨_, hs.conv hlt', c₂.trans c₃⟩

include h hF hE hn in
theorem Spec.goEval {G B : FExpr} {f : Nat → Nat → Nat} (hg : FEq E G G (funTy C))
    (hstep : FEq E (stepLam C G) B (stepTy C)) (hbody : BodyEval C E B f)
    (k a b : Nat) (q : FExpr) (hak : a < k)
    (hq : FEq E q q (lt C (μ C (pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b))) (.natLit C.Nat_ k))) :
    FEq E (go C G (.natLit C.Nat_ k) (pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b)) q) (.natLit C.Nat_ (f a b))
      (nat C.Nat_) := by
  induction k generalizing a b q with
  | zero => omega
  | succ k ih =>
    have ha := FEq.natLit hF hn a
    have hb := FEq.natLit hF hn b
    schema_have hp := h.pairCongr NatFix.pairCongr #[.natLit C.Nat_ a, .natLit C.Nat_ b]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b] using ha, hb
    have ⟨R, hr, c₁, hrec⟩ := h.goSucc hF hE hn hg hp k hq
    schema_have c₂ := h.stepBeta NatFix.stepBeta #[G, .natLit C.Nat_ a, .natLit C.Nat_ b, R]
      #[G, .natLit C.Nat_ a, .natLit C.Nat_ b, R] using hg, ha, hb, hr
    schema_have c₃ := h.stepCongr NatFix.stepCongr #[stepLam C G, .natLit C.Nat_ a, .natLit C.Nat_ b, R]
      #[B, .natLit C.Nat_ a, .natLit C.Nat_ b, R] using hstep, ha, hb, hr
    have c₄ := hbody a b R hr fun y r a' b' ha' hy hr =>
      have ⟨s, hs, c⟩ := hrec hy hr
      c.trans (ih a' b' s (Nat.lt_of_lt_of_le ha' (Nat.le_of_lt_succ hak)) hs)
    exact c₁.trans (c₂.symm.trans (c₃.trans c₄))

variable (hf : Fuel.Spec F C) (hdb : Decide.DecEqBool F C)
  (hbeq : BoolOpSpec F C.Nat_ C.Bool_ beq Nat.beq)

include h hF hE hn hdb hbeq in
theorem Spec.eagerLit (k : Nat) :
    FEq E (FExpr.WellFounded.Nat.eager C (.natLit C.Nat_ k)) (.natLit C.Nat_ k) (nat C.Nat_) := by
  have hk := FEq.natLit hF hn k
  have hβ := FEq.boolOp hF hE hn hbeq k k
  rw [Nat.beq_refl] at hβ
  schema_have c := h.eagerUnfold NatFix.eagerUnfold #[.natLit C.Nat_ k] #[.natLit C.Nat_ k] using hk
  exact c.trans (h.ifTrueEval hF hE hdb hβ hk hk)

include h hf hF hE hn hdb hbeq in
theorem Spec.fixEval {pos : Nat} {G B : FExpr} {f : Nat → Nat → Nat}
    (hfix : FixSpec F C pos G B) (hbody : BodyEval C E B f) (a b : Nat) :
    FEq E (op₂ pos (.natLit C.Nat_ a) (.natLit C.Nat_ b)) (.natLit C.Nat_ (f a b)) (nat C.Nat_) := by
  have ha := FEq.natLit hF hn a
  have hb := FEq.natLit hF hn b
  have hg := Schema.Spec.closed hfix.funType hF hE
  have hsa := FEq.succLit hF hn a
  schema_have hs := h.eagerCongr NatFix.eagerCongr #[succ C.Nat_ (.natLit C.Nat_ a)] #[.natLit C.Nat_ (a + 1)]
    using hsa
  have hs := hs.trans (h.eagerLit hF hE hn hdb hbeq (a + 1))
  schema_have hπ₀ := hf.ltSuccSelfType Fuel.ltSuccSelfType #[.natLit C.Nat_ a] #[.natLit C.Nat_ a] using ha
  schema_have hlt₁ := hf.ltCongr Fuel.ltCongr #[.natLit C.Nat_ a, succ C.Nat_ (.natLit C.Nat_ a)]
    #[.natLit C.Nat_ a, FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.natLit C.Nat_ a))]
    using ha, hsa.trans hs.symm
  have hπ := hπ₀.conv hlt₁
  schema_have hp := h.pairCongr NatFix.pairCongr #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using ha, hb
  schema_have c₁ := hfix.opLamBeta NatFix.opLamBeta
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)] using ha, hb, hπ
  schema_have c₂ := h.fuelCongr NatFix.fuelCongr
    #[opLam C pos, .natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    #[goLam C G, .natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    using Schema.Spec.closed hfix.unfold hF hE, ha, hb, hπ
  schema_have c₃ := h.goLamBeta NatFix.goLamBeta
    #[G, .natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    #[G, .natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)] using hg, ha, hb, hπ
  schema_have hm := h.ltMeasure NatFix.ltMeasure
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.natLit C.Nat_ a))]
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.natLit C.Nat_ a))]
    using ha, hb, hs.left
  have hπ' := hπ.conv hm.symm
  schema_have c₄ := h.goCongr NatFix.goCongr
    #[G, FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.natLit C.Nat_ a)), pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b),
      FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    #[G, .natLit C.Nat_ (a + 1), pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b), FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
    using hg, hs, hp, hπ'
  schema_have hlt₂ := h.ltCongr NatFix.ltCongr
    #[pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b), FExpr.WellFounded.Nat.eager C (succ C.Nat_ (.natLit C.Nat_ a))]
    #[pair C (.natLit C.Nat_ a) (.natLit C.Nat_ b), .natLit C.Nat_ (a + 1)] using hp, hs
  have c₅ := h.goEval hF hE hn hg (Schema.Spec.closed hfix.step hF hE) hbody (a + 1) a b _
    (Nat.lt_succ_self a) (hπ'.conv hlt₂)
  exact c₁.symm.trans (c₂.trans (c₃.trans (c₄.trans c₅)))

end

end NatFix

end Metalean.Checker.Fast
