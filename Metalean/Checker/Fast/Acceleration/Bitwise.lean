/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.NatFix
import all Init.Data.Nat.Bitwise.Basic

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace Bitwise

structure Consts extends toNatFix : NatFix.Consts, toDecideConsts : Decide.DecideConsts where
  protected Nat_bitwise__unary : Nat
  protected Nat_bitwise_rec_lemma : Nat

instance : CoeOut Consts NatFix.Consts := ⟨Consts.toNatFix⟩

instance : CoeOut Consts Decide.DecideConsts := ⟨Consts.toDecideConsts⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    toNatFix := ← NatFix.Consts.resolve t
    Decidable_decide := ← t.const ``Decidable.decide
    Nat_bitwise__unary := ← t.const ``Nat.bitwise._unary
    Nat_bitwise_rec_lemma := ← t.const ``Nat.bitwise_rec_lemma }

structure LandConsts extends toBitwise : Consts where
  protected Bool_and : Nat

instance : CoeOut LandConsts Consts := ⟨LandConsts.toBitwise⟩

def LandConsts.resolve (t : Table) : Except Failure LandConsts := do
  pure { toBitwise := ← Consts.resolve t, Bool_and := ← t.const ``Bool.and }

structure LorConsts extends toBitwise : Consts where
  protected Bool_or : Nat

instance : CoeOut LorConsts Consts := ⟨LorConsts.toBitwise⟩

def LorConsts.resolve (t : Table) : Except Failure LorConsts := do
  pure { toBitwise := ← Consts.resolve t, Bool_or := ← t.const ``Bool.or }

structure XorConsts extends toBitwise : Consts where
  protected bne : Nat
  protected instBEqOfDecidableEq : Nat

instance : CoeOut XorConsts Consts := ⟨XorConsts.toBitwise⟩

def XorConsts.resolve (t : Table) : Except Failure XorConsts := do
  pure {
    toBitwise := ← Consts.resolve t
    bne := ← t.const ``bne
    instBEqOfDecidableEq := ← t.const ``instBEqOfDecidableEq }

end Bitwise

namespace FExpr

@[fexpr_unfold]
protected def Nat.bitwise_rec_lemma (C : Bitwise.Consts) (n h : FExpr) : FExpr :=
  .appList (.const C.Nat_bitwise_rec_lemma #[]) [n, h]

@[fexpr_unfold]
protected def Bool.and (C : Bitwise.LandConsts) : FExpr :=
  .const C.Bool_and #[]

@[fexpr_unfold]
protected def Bool.or (C : Bitwise.LorConsts) : FExpr :=
  .const C.Bool_or #[]

/-- `bne` at `Type` -/
@[fexpr_unfold]
protected def bne (C : Bitwise.XorConsts) (α inst : FExpr) : FExpr :=
  .appList (.const C.bne #[.zero]) [α, inst]

/-- `instBEqOfDecidableEq` at `Type` -/
@[fexpr_unfold]
protected def instBEqOfDecidableEq (C : Bitwise.XorConsts) (α d : FExpr) : FExpr :=
  .appList (.const C.instBEqOfDecidableEq #[.zero]) [α, d]

end FExpr

namespace Bitwise

open NatFix (sig pair μ lt recTy cdite ifTrue app₃)

open scoped NatFix

variable (F : FEnv) (C : Consts)

/-- `Bool → Bool → Bool` -/
@[fexpr_unfold]
def boolArrow₂ : FExpr :=
  bool C.Bool_ ⟶ bool C.Bool_ ⟶ bool C.Bool_

/-- `decide (x % 2 = 1)` -/
@[fexpr_unfold]
def decideOdd (mod : Nat) (x : FExpr) : FExpr :=
  FExpr.Decidable.decide C (FExpr.Eq C (nat C.Nat_) (op₂ mod x (.natLit C.Nat_ 2)) (.natLit C.Nat_ 1))
    (FExpr.instDecidableEqNat C (op₂ mod x (.natLit C.Nat_ 2)) (.natLit C.Nat_ 1))

/-- `R ⟨n / 2, m / 2⟩ (Nat.bitwise_rec_lemma h)` -/
@[fexpr_unfold]
def recCall (div : Nat) (R n m h : FExpr) : FExpr :=
  .appList R
    [pair C (op₂ div n (.natLit C.Nat_ 2)) (op₂ div m (.natLit C.Nat_ 2)),
      FExpr.Nat.bitwise_rec_lemma C n h]

/-- `if _ : f (decideOdd n) (decideOdd m) = true then r + r + 1 else r + r` for
`r = recCall R n m h` -/
@[fexpr_unfold]
def bitsBody (mod div add : Nat) (f : FExpr) (n m R h : Nat → FExpr) : FExpr :=
  ifTrue C (.appList f [decideOdd C mod (n 0), decideOdd C mod (m 0)])
    (op₂ add (op₂ add (recCall C div (R 1) (n 1) (m 1) (h 1))
      (recCall C div (R 1) (n 1) (m 1) (h 1))) (.natLit C.Nat_ 1))
    (op₂ add (recCall C div (R 1) (n 1) (m 1) (h 1)) (recCall C div (R 1) (n 1) (m 1) (h 1)))

/-- `if _ : m = 0 then (if _ : f true false = true then n else 0) else bitsBody n m R h` -/
@[fexpr_unfold]
def rightBody (mod div add : Nat) (f : FExpr) (n m R h : Nat → FExpr) : FExpr :=
  cdite C (FExpr.Eq C (nat C.Nat_) (m 0) (.natLit C.Nat_ 0))
    (FExpr.instDecidableEqNat C (m 0) (.natLit C.Nat_ 0))
    (ifTrue C (.appList f [boolLit C.Bool_ true, boolLit C.Bool_ false]) (n 2)
      (.natLit C.Nat_ 0))
    (bitsBody C mod div add f (fun d => n (d + 1)) (fun d => m (d + 1)) (fun d => R (d + 1))
      (fun d => h (d + 1)))

/-- `fun h => rightBody n m R h` -/
@[fexpr_unfold]
def onFalse (mod div add : Nat) (f : FExpr) (n m R : Nat → FExpr) : FExpr :=
  .lam (FExpr.Not C (FExpr.Eq C (nat C.Nat_) (n 0) (.natLit C.Nat_ 0)))
    (rightBody C mod div add f (fun d => n (d + 1)) (fun d => m (d + 1)) (fun d => R (d + 1))
      fun d => .bvar d)

/-- `if h : n = 0 then (if _ : f false true = true then m else 0) else rightBody n m R h` -/
@[fexpr_unfold]
def body (mod div add : Nat) (f : FExpr) (n m R : Nat → FExpr) : FExpr :=
  FExpr.dite C (nat C.Nat_) (FExpr.Eq C (nat C.Nat_) (n 0) (.natLit C.Nat_ 0))
    (FExpr.instDecidableEqNat C (n 0) (.natLit C.Nat_ 0))
    (.lam (FExpr.Eq C (nat C.Nat_) (n 0) (.natLit C.Nat_ 0))
      (ifTrue C (.appList f [boolLit C.Bool_ false, boolLit C.Bool_ true]) (m 2)
        (.natLit C.Nat_ 0)))
    (onFalse C mod div add f n m R)

@[fexpr_unfold]
def bodyLam (mod div add : Nat) (f : FExpr) : FExpr :=
  .lam (nat C.Nat_) (.lam (nat C.Nat_) (.lam (recTy C (pair C (.bvar 2) (.bvar 1)))
    (body C mod div add f (fun d => .bvar (d + 2)) (fun d => .bvar (d + 1)) fun d => .bvar d)))

def bodyBeta (mod div add : Nat) : Schema :=
  schema% (f : boolArrow₂ C) (n : nat C.Nat_) (m : nat C.Nat_) (R : recTy C (pair C n m)) ⊢
    app₃ (bodyLam C mod div add f) n m R ≡
      body C mod div add f (fun _ => n) (fun _ => m) (fun _ => R) :
    nat C.Nat_

def onFalseType (mod div add : Nat) : Schema :=
  schema% (f : boolArrow₂ C) (n : nat C.Nat_) (m : nat C.Nat_) (R : recTy C (pair C n m)) ⊢
    onFalse C mod div add f (fun _ => n) (fun _ => m) (fun _ => R) :
    FExpr.Not C (FExpr.Eq C (nat C.Nat_) n (.natLit C.Nat_ 0)) ⟶ nat C.Nat_

def onFalseBeta (mod div add : Nat) : Schema :=
  schema% (f : boolArrow₂ C) (n : nat C.Nat_) (m : nat C.Nat_) (R : recTy C (pair C n m))
      (h : FExpr.Not C (FExpr.Eq C (nat C.Nat_) n (.natLit C.Nat_ 0))) ⊢
    .app (onFalse C mod div add f (fun _ => n) (fun _ => m) (fun _ => R)) h ≡
      rightBody C mod div add f (fun _ => n) (fun _ => m) (fun _ => R) (fun _ => h) :
    nat C.Nat_

def recLemmaType (div : Nat) : Schema :=
  schema% (n : nat C.Nat_) (m : nat C.Nat_)
      (h : FExpr.Not C (FExpr.Eq C (nat C.Nat_) n (.natLit C.Nat_ 0))) ⊢
    FExpr.Nat.bitwise_rec_lemma C n h :
    lt C (μ C (pair C (op₂ div n (.natLit C.Nat_ 2)) (op₂ div m (.natLit C.Nat_ 2)))) (μ C (pair C n m))

def fApp : Schema :=
  schema% (f : boolArrow₂ C) (β : bool C.Bool_) (γ : bool C.Bool_) ⊢
    (.appList f [β, γ]) : bool C.Bool_

def decideCongr : Schema :=
  schema% (a : nat C.Nat_) (b : nat C.Nat_) ⊢
    FExpr.Decidable.decide C (FExpr.Eq C (nat C.Nat_) a b) (FExpr.instDecidableEqNat C a b) :
    bool C.Bool_

def addCongr (add : Nat) : Schema :=
  schema% (a : nat C.Nat_) (b : nat C.Nat_) ⊢ op₂ add a b : nat C.Nat_

def fType (f : FExpr) : Schema :=
  schema% ⊢ f : boolArrow₂ C

def fEval (f : FExpr) (β γ v : Bool) : Schema :=
  schema% ⊢ (.appList f [boolLit C.Bool_ β, boolLit C.Bool_ γ]) ≡ boolLit C.Bool_ v :
    bool C.Bool_

structure Spec (pos mod div add : Nat) (fn f : FExpr) (fl : Bool → Bool → Bool) : Prop where
  fix : NatFix.FixSpec F C pos (.app fn f) (bodyLam C mod div add f)
  bodyBeta : (bodyBeta C mod div add).Spec F
  onFalseType : (onFalseType C mod div add).Spec F
  onFalseBeta : (onFalseBeta C mod div add).Spec F
  recLemmaType : (recLemmaType C div).Spec F
  fApp : (fApp C).Spec F
  decideCongr : (decideCongr C).Spec F
  addCongr : (addCongr C add).Spec F
  fType : (fType C f).Spec F
  fEval : ∀ β γ, (fEval C f β γ (fl β γ)).Spec F

/-- The functional `fun f => G f` of `Nat.bitwise._unary = fun f => WellFounded.Nat.fix h (G f)` -/
def functional : Except Failure FExpr :=
  match F[C.Nat_bitwise__unary]? with
  | some (.def 0 _ (.lam t (.appList (.const _ _) [_, _, _, G]))) => pure (.lam t G)
  | _ => throw .internal

variable (hints : PArray Export.Hints)

def check (pos mod div add : Nat) (f : FExpr) (fl : Bool → Bool → Bool) :
    EIO Failure ((fn : FExpr) × PLift (Spec F C pos mod div add fn f fl)) := do
  let fn ← functional F C
  let ⟨fix⟩ ← NatFix.checkFix F C hints pos (.app fn f) (bodyLam C mod div add f)
  let ⟨bodyBeta⟩ ← (bodyBeta C mod div add).check F hints
  let ⟨onFalseType⟩ ← (onFalseType C mod div add).check F hints
  let ⟨onFalseBeta⟩ ← (onFalseBeta C mod div add).check F hints
  let ⟨recLemmaType⟩ ← (recLemmaType C div).check F hints
  let ⟨fApp⟩ ← (fApp C).check F hints
  let ⟨decideCongr⟩ ← (decideCongr C).check F hints
  let ⟨addCongr⟩ ← (addCongr C add).check F hints
  let ⟨fType⟩ ← (fType C f).check F hints
  let ⟨ff⟩ ← (fEval C f false false (fl false false)).check F hints
  let ⟨ft⟩ ← (fEval C f false true (fl false true)).check F hints
  let ⟨tf⟩ ← (fEval C f true false (fl true false)).check F hints
  let ⟨tt⟩ ← (fEval C f true true (fl true true)).check F hints
  pure ⟨fn, ⟨⟨fix, bodyBeta, onFalseType, onFalseBeta, recLemmaType, fApp, decideCongr, addCongr,
    fType, fun
      | false, false => ff
      | false, true => ft
      | true, false => tf
      | true, true => tt⟩⟩⟩

section

variable {F C} {pos mod div add beq : Nat} {fn f : FExpr} {fl : Bool → Bool → Bool}
  (h : Spec F C pos mod div add fn f fl) (hfix : NatFix.Spec F C beq) {ζ : Sigs} {E : Env ζ}
  (hF : FEnv.Denotes F E) (hE : EnvWF E) (hn : NatSpec F C.Nat_)
  (hd : Decide.DecEqNat F C) (hdb : Decide.DecEqBool F C) (hde : Decide.DecideEqNat F C)
  (hmod : NatOpSpec F C.Nat_ mod Nat.mod) (hdiv : NatOpSpec F C.Nat_ div Nat.div)
  (hadd : NatOpSpec F C.Nat_ add Nat.add)

include h hF hE hn hde hmod in
theorem Spec.decideOddEval (a : Nat) :
    FEq E (decideOdd C mod (.natLit C.Nat_ a)) (boolLit C.Bool_ (a % 2 == 1)) (bool C.Bool_) := by
  schema_have c := h.decideCongr Bitwise.decideCongr
    #[op₂ mod (.natLit C.Nat_ a) (.natLit C.Nat_ 2), .natLit C.Nat_ 1] #[.natLit C.Nat_ (a % 2), .natLit C.Nat_ 1]
    using FEq.natOp hF hE hn hmod a 2, FEq.natLit hF hn 1
  exact c.trans (hde hF hE (a % 2) 1)

include h hF hE hn hadd in
theorem Spec.addEval {x y : FExpr} {m n : Nat} (hx : FEq E x (.natLit C.Nat_ m) (nat C.Nat_))
    (hy : FEq E y (.natLit C.Nat_ n) (nat C.Nat_)) :
    FEq E (op₂ add x y) (.natLit C.Nat_ (m + n)) (nat C.Nat_) := by
  schema_have c := h.addCongr Bitwise.addCongr #[x, y] #[.natLit C.Nat_ m, .natLit C.Nat_ n] using hx, hy
  exact c.trans (FEq.natOp hF hE hn hadd m n)

include h hfix hF hE hn hd hdb hde hmod hdiv hadd in
theorem Spec.bodyEval : NatFix.BodyEval C E (bodyLam C mod div add f) (Nat.bitwise fl) := by
  intro a b R hr hrec
  have ha := FEq.natLit hF hn a
  have hb := FEq.natLit hF hn b
  have hz := FEq.natLit hF hn 0
  have hf := Schema.Spec.closed h.fType hF hE
  have hfl (β γ : Bool) := Schema.Spec.closed (h.fEval β γ) hF hE
  schema_have c₁ := h.bodyBeta Bitwise.bodyBeta #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R]
    #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R] using hf, ha, hb, hr
  schema_have heq := hfix.eqNatType NatFix.eqNatType #[.natLit C.Nat_ a, .natLit C.Nat_ 0]
    #[.natLit C.Nat_ a, .natLit C.Nat_ 0] using ha, hz
  have hx := hfix.ifTrueEval hF hE hdb (hfl false true) hb hz
  schema_have ht := hfix.constLamType NatFix.constLamType
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ 0),
      ifTrue C (.appList f [boolLit C.Bool_ false, boolLit C.Bool_ true]) (.natLit C.Nat_ b)
        (.natLit C.Nat_ 0)]
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ 0),
      ifTrue C (.appList f [boolLit C.Bool_ false, boolLit C.Bool_ true]) (.natLit C.Nat_ b)
        (.natLit C.Nat_ 0)]
    using heq, hx.left
  schema_have he := h.onFalseType Bitwise.onFalseType #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R]
    #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R] using hf, ha, hb, hr
  have ⟨p, hp, c₂⟩ := hd a 0 hF hE ht he
  by_cases ha₀ : a = 0
  · subst ha₀
    simp only [beq_self_eq_true, Bool.cond_true] at hp c₂
    schema_have c₃ := hfix.constBeta NatFix.constBeta
      #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ 0) (.natLit C.Nat_ 0),
        ifTrue C (.appList f [boolLit C.Bool_ false, boolLit C.Bool_ true]) (.natLit C.Nat_ b)
          (.natLit C.Nat_ 0), p]
      #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ 0) (.natLit C.Nat_ 0),
        ifTrue C (.appList f [boolLit C.Bool_ false, boolLit C.Bool_ true]) (.natLit C.Nat_ b)
          (.natLit C.Nat_ 0), p]
      using heq, hx.left, hp
    have e : Nat.bitwise fl 0 b = cond (fl false true) b 0 := by
      rw [Nat.bitwise.eq_def]
      cases fl false true <;> simp
    rw [e]
    exact c₁.trans (c₂.trans (c₃.trans hx))
  · rw [beq_eq_false_iff_ne.mpr ha₀, Bool.cond_false] at hp c₂
    schema_have c₃ := h.onFalseBeta Bitwise.onFalseBeta #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R, p]
      #[f, .natLit C.Nat_ a, .natLit C.Nat_ b, R, p] using hf, ha, hb, hr, hp
    schema_have hy := hfix.pairCongr NatFix.pairCongr
      #[op₂ div (.natLit C.Nat_ a) (.natLit C.Nat_ 2), op₂ div (.natLit C.Nat_ b) (.natLit C.Nat_ 2)]
      #[.natLit C.Nat_ (a / 2), .natLit C.Nat_ (b / 2)]
      using FEq.natOp hF hE hn hdiv a 2, FEq.natOp hF hE hn hdiv b 2
    schema_have hq := h.recLemmaType Bitwise.recLemmaType #[.natLit C.Nat_ a, .natLit C.Nat_ b, p]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b, p] using ha, hb, hp
    have hcall := hrec (Nat.div_lt_self (Nat.pos_of_ne_zero ha₀) (by decide)) hy hq
    have hdbl := h.addEval hF hE hn hadd hcall hcall
    have hdbl₁ := h.addEval hF hE hn hadd hdbl (FEq.natLit hF hn 1)
    schema_have hbits := h.fApp Bitwise.fApp
      #[f, decideOdd C mod (.natLit C.Nat_ a), decideOdd C mod (.natLit C.Nat_ b)]
      #[f, boolLit C.Bool_ (a % 2 == 1), boolLit C.Bool_ (b % 2 == 1)]
      using hf, h.decideOddEval hF hE hn hde hmod a, h.decideOddEval hF hE hn hde hmod b
    have hl := hfix.ifTrueEval hF hE hdb (hbits.trans (hfl _ _)) hdbl₁ hdbl
    have hy₀ := hfix.ifTrueEval hF hE hdb (hfl true false) ha hz
    schema_have heq' := hfix.eqNatType NatFix.eqNatType #[.natLit C.Nat_ b, .natLit C.Nat_ 0]
      #[.natLit C.Nat_ b, .natLit C.Nat_ 0] using hb, hz
    have c₄ := hfix.cditeReduce hF hE (hd b 0) heq' hy₀.left hl.left
    by_cases hb₀ : b = 0
    · subst hb₀
      simp only [beq_self_eq_true, Bool.cond_true] at c₄
      have e : Nat.bitwise fl a 0 = cond (fl true false) a 0 := by
        rw [Nat.bitwise.eq_def]
        cases fl true false <;> simp [ha₀]
      rw [e]
      exact c₁.trans (c₂.trans (c₃.trans (c₄.trans hy₀)))
    · rw [beq_eq_false_iff_ne.mpr hb₀, Bool.cond_false] at c₄
      have e : Nat.bitwise fl a b = cond (fl (a % 2 == 1) (b % 2 == 1))
          (Nat.bitwise fl (a / 2) (b / 2) + Nat.bitwise fl (a / 2) (b / 2) + 1)
          (Nat.bitwise fl (a / 2) (b / 2) + Nat.bitwise fl (a / 2) (b / 2)) := by
        rw [Nat.bitwise.eq_def]
        simp only [ha₀, hb₀, ↓reduceIte]
        change (if fl (a % 2 == 1) (b % 2 == 1) = true then _ else _) = _
        cases fl (a % 2 == 1) (b % 2 == 1) <;> rfl
      rw [e]
      exact c₁.trans (c₂.trans (c₃.trans (c₄.trans hl)))

end

def verify (f : FExpr) (fl : Bool → Bool → Bool) (hd : Decide.DecEqNat F C)
    (hdb : Decide.DecEqBool F C) (hde : Decide.DecideEqNat F C) (pos : Nat)
    (beq : BoolOp F Nat.beq) (mod : NatOp F Nat.mod) (div : NatOp F Nat.div)
    (add : NatOp F Nat.add) :
    EIO Failure (NatOp F (Nat.bitwise fl)) := do
  let ⟨hn⟩ ← natAt F C.Nat_
  let ⟨hbeq⟩ ← beq.at F C.Nat_ C.Bool_
  let ⟨hmod⟩ ← mod.at F C.Nat_
  let ⟨hdiv⟩ ← div.at F C.Nat_
  let ⟨hadd⟩ ← add.at F C.Nat_
  let ⟨hop⟩ ← constDef F pos
  let ⟨hf⟩ ← Fuel.check F C hints
  let ⟨hfix⟩ ← NatFix.check F C hints beq.pos
  let ⟨_, ⟨h⟩⟩ ← check F C hints pos mod.pos div.pos add.pos f fl
  pure ⟨C.Nat_, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE =>
    hfix.fixEval hF hE hn hf hdb hbeq h.fix
      (h.bodyEval hfix hF hE hn hd hdb hde hmod hdiv hadd)⟩

@[no_expose]
def verifyLand (C : LandConsts) (hints : PArray Export.Hints) (hd : Decide.DecEqNat F C)
    (hdb : Decide.DecEqBool F C) (hde : Decide.DecideEqNat F C) (pos : Nat)
    (beq : BoolOp F Nat.beq) (mod : NatOp F Nat.mod) (div : NatOp F Nat.div)
    (add : NatOp F Nat.add) :
    EIO Failure (NatOp F Nat.land) :=
  verify F C hints (FExpr.Bool.and C) and hd hdb hde pos beq mod div add

@[no_expose]
def verifyLor (C : LorConsts) (hints : PArray Export.Hints) (hd : Decide.DecEqNat F C)
    (hdb : Decide.DecEqBool F C) (hde : Decide.DecideEqNat F C) (pos : Nat)
    (beq : BoolOp F Nat.beq) (mod : NatOp F Nat.mod) (div : NatOp F Nat.div)
    (add : NatOp F Nat.add) :
    EIO Failure (NatOp F Nat.lor) :=
  verify F C hints (FExpr.Bool.or C) or hd hdb hde pos beq mod div add

@[no_expose]
def verifyXor (C : XorConsts) (hints : PArray Export.Hints) (hd : Decide.DecEqNat F C)
    (hdb : Decide.DecEqBool F C) (hde : Decide.DecideEqNat F C) (pos : Nat)
    (beq : BoolOp F Nat.beq) (mod : NatOp F Nat.mod) (div : NatOp F Nat.div)
    (add : NatOp F Nat.add) :
    EIO Failure (NatOp F Nat.xor) :=
  verify F C hints
    (FExpr.bne C (bool C.Bool_)
      (FExpr.instBEqOfDecidableEq C (bool C.Bool_) (.const C.instDecidableEqBool #[])))
    bne hd hdb hde pos beq mod div add

end Bitwise

end Metalean.Checker.Fast
