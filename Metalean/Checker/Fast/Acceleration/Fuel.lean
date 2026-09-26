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

namespace Fuel

structure Consts extends toLeConsts : Decide.LeConsts where
  protected Nat_sub : Nat
  protected Nat_lt_succ_self : Nat
  protected Nat_div_rec_fuel_lemma : Nat

instance : CoeOut Consts Decide.LeConsts := ⟨Consts.toLeConsts⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    toLeConsts := ← Decide.LeConsts.resolve t
    Nat_sub := ← t.const ``Nat.sub
    Nat_lt_succ_self := ← t.const ``Nat.lt_succ_self
    Nat_div_rec_fuel_lemma := ← t.const ``Nat.div_rec_fuel_lemma }

structure Rec where
  pos : Nat
  entry (x y : FExpr) : FExpr
  step (r : FExpr) : FExpr
  base (x : FExpr) : FExpr
  instFVarsCore_entry : ∀ args x y,
    (entry x y).instFVarsCore args = entry (x.instFVarsCore args) (y.instFVarsCore args)
  instFVarsCore_step : ∀ args r,
    (step r).instFVarsCore args = step (r.instFVarsCore args)
  instFVarsCore_base : ∀ args x,
    (base x).instFVarsCore args = base (x.instFVarsCore args)

@[fexpr_unfold]
def Rec.go (R : Rec) (y hy fuel x h : FExpr) : FExpr :=
  .appList (.const R.pos #[]) [y, hy, fuel, x, h]

end Fuel

namespace FExpr

variable (C : Fuel.Consts)

@[fexpr_unfold]
protected def Nat.lt_succ_self (x : FExpr) : FExpr :=
  .app (.const C.Nat_lt_succ_self #[]) x

@[fexpr_unfold]
protected def Nat.div_rec_fuel_lemma (x y fuel hy hle h : FExpr) : FExpr :=
  .appList (.const C.Nat_div_rec_fuel_lemma #[]) [x, y, fuel, hy, hle, h]

end FExpr

namespace Fuel

variable (F : FEnv) (C : Consts) (hints : Array Export.Hints)

def ltCongr : Schema :=
  schema% (x : nat C.Nat_) (fuel : nat C.Nat_) ⊢ FExpr.Nat.le C (succ C.Nat_ x) fuel : prop

def ltSuccSelfType : Schema :=
  schema% (x : nat C.Nat_) ⊢
    FExpr.Nat.lt_succ_self C x : FExpr.Nat.le C (succ C.Nat_ x) (succ C.Nat_ x)

def fuelLemmaType : Schema :=
  schema% (y : nat C.Nat_) (hy : FExpr.Nat.le C (.natLit C.Nat_ 1) y) (fuel : nat C.Nat_)
      (x : nat C.Nat_) (h : FExpr.Nat.le C (succ C.Nat_ x) (succ C.Nat_ fuel))
      (hle : FExpr.Nat.le C y x) ⊢
    FExpr.Nat.div_rec_fuel_lemma C x y fuel hy hle h :
    FExpr.Nat.le C (succ C.Nat_ (op₂ C.Nat_sub x y)) fuel

structure Spec : Prop where
  ltCongr : (ltCongr C).Spec F
  ltSuccSelfType : (ltSuccSelfType C).Spec F
  fuelLemmaType : (fuelLemmaType C).Spec F

def check : EIO Failure (PLift (Spec F C)) := do
  let ⟨ltCongr⟩ ← (ltCongr C).check F hints
  let ⟨ltSuccSelfType⟩ ← (ltSuccSelfType C).check F hints
  let ⟨fuelLemmaType⟩ ← (fuelLemmaType C).check F hints
  pure ⟨⟨ltCongr, ltSuccSelfType, fuelLemmaType⟩⟩

section

variable (R : Rec)

def onTrue (x y : FExpr) : FExpr :=
  .lam (FExpr.Nat.le C (.natLit C.Nat_ 1) y)
    (R.go y (.bvar 0) (succ C.Nat_ x) x (FExpr.Nat.lt_succ_self C x))

def onFalse (x y : FExpr) : FExpr :=
  .lam (FExpr.Not C (FExpr.Nat.le C (.natLit C.Nat_ 1) y)) (R.base x)

def stepTrue (y hy fuel x h : FExpr) : FExpr :=
  .lam (FExpr.Nat.le C y x)
    (R.step (R.go y hy fuel (op₂ C.Nat_sub x y)
      (FExpr.Nat.div_rec_fuel_lemma C x y fuel hy (.bvar 0) h)))

def stepFalse (y x : FExpr) : FExpr :=
  .lam (FExpr.Not C (FExpr.Nat.le C y x)) (R.base x)

def unfold : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    R.entry x y ≡
      FExpr.dite C (nat C.Nat_) (FExpr.Nat.le C (.natLit C.Nat_ 1) y)
        (FExpr.Nat.decLe C (.natLit C.Nat_ 1) y) (onTrue C R x y) (onFalse C R x y) :
    nat C.Nat_

def onTrueType : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    onTrue C R x y : FExpr.Nat.le C (.natLit C.Nat_ 1) y ⟶ nat C.Nat_

def onFalseType : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    onFalse C R x y : FExpr.Not C (FExpr.Nat.le C (.natLit C.Nat_ 1) y) ⟶ nat C.Nat_

def onTrueBeta : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) (p : FExpr.Nat.le C (.natLit C.Nat_ 1) y) ⊢
    .app (onTrue C R x y) p ≡ R.go y p (succ C.Nat_ x) x (FExpr.Nat.lt_succ_self C x) :
    nat C.Nat_

def onFalseBeta : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_)
      (p : FExpr.Not C (FExpr.Nat.le C (.natLit C.Nat_ 1) y)) ⊢
    .app (onFalse C R x y) p ≡ R.base x : nat C.Nat_

def step : Schema :=
  schema% (y : nat C.Nat_) (hy : FExpr.Nat.le C (.natLit C.Nat_ 1) y) (fuel : nat C.Nat_)
      (x : nat C.Nat_) (h : FExpr.Nat.le C (succ C.Nat_ x) (succ C.Nat_ fuel)) ⊢
    R.go y hy (succ C.Nat_ fuel) x h ≡
      FExpr.dite C (nat C.Nat_) (FExpr.Nat.le C y x) (FExpr.Nat.decLe C y x)
        (stepTrue C R y hy fuel x h) (stepFalse C R y x) :
    nat C.Nat_

def stepTrueType : Schema :=
  schema% (y : nat C.Nat_) (hy : FExpr.Nat.le C (.natLit C.Nat_ 1) y) (fuel : nat C.Nat_)
      (x : nat C.Nat_) (h : FExpr.Nat.le C (succ C.Nat_ x) (succ C.Nat_ fuel)) ⊢
    stepTrue C R y hy fuel x h : FExpr.Nat.le C y x ⟶ nat C.Nat_

def stepFalseType : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) ⊢
    stepFalse C R y x : FExpr.Not C (FExpr.Nat.le C y x) ⟶ nat C.Nat_

def stepTrueBeta : Schema :=
  schema% (y : nat C.Nat_) (hy : FExpr.Nat.le C (.natLit C.Nat_ 1) y) (fuel : nat C.Nat_)
      (x : nat C.Nat_) (h : FExpr.Nat.le C (succ C.Nat_ x) (succ C.Nat_ fuel))
      (p : FExpr.Nat.le C y x) ⊢
    .app (stepTrue C R y hy fuel x h) p ≡
      R.step (R.go y hy fuel (op₂ C.Nat_sub x y)
        (FExpr.Nat.div_rec_fuel_lemma C x y fuel hy p h)) :
    nat C.Nat_

def stepFalseBeta : Schema :=
  schema% (y : nat C.Nat_) (x : nat C.Nat_) (p : FExpr.Not C (FExpr.Nat.le C y x)) ⊢
    .app (stepFalse C R y x) p ≡ R.base x : nat C.Nat_

def goCongr : Schema :=
  schema% (y : nat C.Nat_) (hy : FExpr.Nat.le C (.natLit C.Nat_ 1) y) (fuel : nat C.Nat_)
      (x : nat C.Nat_) (h : FExpr.Nat.le C (succ C.Nat_ x) fuel) ⊢
    R.go y hy fuel x h : nat C.Nat_

def stepCongr : Schema :=
  schema% (r : nat C.Nat_) ⊢ R.step r : nat C.Nat_

structure RecSpec : Prop where
  unfold : (unfold C R).Spec F
  onTrueType : (onTrueType C R).Spec F
  onFalseType : (onFalseType C R).Spec F
  onTrueBeta : (onTrueBeta C R).Spec F
  onFalseBeta : (onFalseBeta C R).Spec F
  step : (step C R).Spec F
  stepTrueType : (stepTrueType C R).Spec F
  stepFalseType : (stepFalseType C R).Spec F
  stepTrueBeta : (stepTrueBeta C R).Spec F
  stepFalseBeta : (stepFalseBeta C R).Spec F
  goCongr : (goCongr C R).Spec F
  stepCongr : (stepCongr C R).Spec F

def checkRec : EIO Failure (PLift (RecSpec F C R)) := do
  let ⟨unfold⟩ ← (unfold C R).check F hints
  let ⟨onTrueType⟩ ← (onTrueType C R).check F hints
  let ⟨onFalseType⟩ ← (onFalseType C R).check F hints
  let ⟨onTrueBeta⟩ ← (onTrueBeta C R).check F hints
  let ⟨onFalseBeta⟩ ← (onFalseBeta C R).check F hints
  let ⟨step⟩ ← (step C R).check F hints
  let ⟨stepTrueType⟩ ← (stepTrueType C R).check F hints
  let ⟨stepFalseType⟩ ← (stepFalseType C R).check F hints
  let ⟨stepTrueBeta⟩ ← (stepTrueBeta C R).check F hints
  let ⟨stepFalseBeta⟩ ← (stepFalseBeta C R).check F hints
  let ⟨goCongr⟩ ← (goCongr C R).check F hints
  let ⟨stepCongr⟩ ← (stepCongr C R).check F hints
  pure ⟨⟨unfold, onTrueType, onFalseType, onTrueBeta, onFalseBeta, step, stepTrueType,
    stepFalseType, stepTrueBeta, stepFalseBeta, goCongr, stepCongr⟩⟩

structure Rec.Computes (f : Nat → Nat → Nat) : Prop where
  step : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
    FEnv.Denotes F E →
    NatSpec F C.Nat_ →
    ∀ a b, 0 < b → b ≤ a →
    FEq E (R.step (.natLit C.Nat_ (f (a - b) b))) (.natLit C.Nat_ (f a b)) (nat C.Nat_)
  base : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
    FEnv.Denotes F E →
    NatSpec F C.Nat_ →
    ∀ a b, b = 0 ∨ a < b →
    FEq E (R.base (.natLit C.Nat_ a)) (.natLit C.Nat_ (f a b)) (nat C.Nat_)

structure Eval (f : Nat → Nat → Nat) : Prop where
  natSpec : NatSpec F C.Nat_
  eq : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
    FEnv.Denotes F E →
    EnvWF E →
    ∀ a b, FEq E (R.entry (.natLit C.Nat_ a) (.natLit C.Nat_ b)) (.natLit C.Nat_ (f a b)) (nat C.Nat_)

end

section

variable {F C} {R : Rec} (hd : Decide.DecLe F C) (hf : Spec F C) (h : RecSpec F C R)
  {ζ : Sigs} {E : Env ζ} (hF : FEnv.Denotes F E) (hE : EnvWF E) (hn : NatSpec F C.Nat_)
  (hsub : NatOpSpec F C.Nat_ C.Nat_sub Nat.sub) {f : Nat → Nat → Nat} (hc : R.Computes F C f)

include hd hf h hF hE hn hsub hc in
theorem RecSpec.goEval {b : Nat} (hb : 0 < b) {hy : FExpr}
    (hhy : FEq E hy hy (FExpr.Nat.le C (.natLit C.Nat_ 1) (.natLit C.Nat_ b))) {k a : Nat} (ha : a < k)
    {hfuel : FExpr}
    (hh : FEq E hfuel hfuel (FExpr.Nat.le C (succ C.Nat_ (.natLit C.Nat_ a)) (.natLit C.Nat_ k))) :
    FEq E (R.go (.natLit C.Nat_ b) hy (.natLit C.Nat_ k) (.natLit C.Nat_ a) hfuel) (.natLit C.Nat_ (f a b))
      (nat C.Nat_) := by
  induction k generalizing a hfuel with
  | zero => omega
  | succ k ih =>
    have hb' := FEq.natLit hF hn b
    have ha' := FEq.natLit hF hn a
    have hk := FEq.natLit hF hn k
    have hk₁ := (FEq.succLit hF hn k).symm
    schema_have hlt := hf.ltCongr Fuel.ltCongr #[.natLit C.Nat_ a, .natLit C.Nat_ (k + 1)]
      #[.natLit C.Nat_ a, succ C.Nat_ (.natLit C.Nat_ k)] using ha', hk₁
    have hh' := hh.conv hlt
    schema_have c₀ := h.goCongr Fuel.goCongr
      #[.natLit C.Nat_ b, hy, .natLit C.Nat_ (k + 1), .natLit C.Nat_ a, hfuel]
      #[.natLit C.Nat_ b, hy, succ C.Nat_ (.natLit C.Nat_ k), .natLit C.Nat_ a, hfuel] using hb', hhy, hk₁, ha', hh
    schema_have c₁ := h.step Fuel.step #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel]
      #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel] using hb', hhy, hk, ha', hh'
      unfolding stepTrue, stepFalse, R.instFVarsCore_step, R.instFVarsCore_base
    schema_have ht := h.stepTrueType Fuel.stepTrueType
      #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel]
      #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel] using hb', hhy, hk, ha', hh'
      unfolding stepTrue, R.instFVarsCore_step
    schema_have he := h.stepFalseType Fuel.stepFalseType #[.natLit C.Nat_ b, .natLit C.Nat_ a]
      #[.natLit C.Nat_ b, .natLit C.Nat_ a] using hb', ha' unfolding stepFalse, R.instFVarsCore_base
    have ⟨p, hp, c₂⟩ := hd b a hF hE ht he
    by_cases hba : b ≤ a
    · simp only [hba, decide_true, Bool.cond_true] at hp c₂
      schema_have c₃ := h.stepTrueBeta Fuel.stepTrueBeta
        #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel, p]
        #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel, p]
        using hb', hhy, hk, ha', hh', hp unfolding stepTrue, R.instFVarsCore_step
      schema_have hp' := hf.fuelLemmaType Fuel.fuelLemmaType
        #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel, p]
        #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ a, hfuel, p]
        using hb', hhy, hk, ha', hh', hp
      have hs := FEq.natOp hF hE hn hsub a b
      schema_have hlt₂ := hf.ltCongr Fuel.ltCongr
        #[op₂ C.Nat_sub (.natLit C.Nat_ a) (.natLit C.Nat_ b), .natLit C.Nat_ k] #[.natLit C.Nat_ (a - b), .natLit C.Nat_ k]
        using hs, hk
      have c₄ : ∀ q,
          FEq E q q
            (FExpr.Nat.le C (succ C.Nat_ (op₂ C.Nat_sub (.natLit C.Nat_ a) (.natLit C.Nat_ b))) (.natLit C.Nat_ k)) →
          FEq E
            (R.step (R.go (.natLit C.Nat_ b) hy (.natLit C.Nat_ k) (op₂ C.Nat_sub (.natLit C.Nat_ a) (.natLit C.Nat_ b)) q))
            (.natLit C.Nat_ (f a b)) (nat C.Nat_) := by
        intro q hq
        schema_have c₅ := h.goCongr Fuel.goCongr
          #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, op₂ C.Nat_sub (.natLit C.Nat_ a) (.natLit C.Nat_ b), q]
          #[.natLit C.Nat_ b, hy, .natLit C.Nat_ k, .natLit C.Nat_ (a - b), q] using hb', hhy, hk, hs, hq
        schema_have c₆ := h.stepCongr Fuel.stepCongr
          #[R.go (.natLit C.Nat_ b) hy (.natLit C.Nat_ k) (op₂ C.Nat_sub (.natLit C.Nat_ a) (.natLit C.Nat_ b)) q]
          #[.natLit C.Nat_ (f (a - b) b)] using c₅.trans (ih (by omega) (hq.conv hlt₂))
          unfolding R.instFVarsCore_step
        exact c₆.trans (hc.step hF hn a b hb hba)
      exact c₀.trans (c₁.trans (c₂.trans (c₃.trans (c₄ _ hp'))))
    · simp only [hba, decide_false, Bool.cond_false] at hp c₂
      schema_have c₃ := h.stepFalseBeta Fuel.stepFalseBeta #[.natLit C.Nat_ b, .natLit C.Nat_ a, p]
        #[.natLit C.Nat_ b, .natLit C.Nat_ a, p] using hb', ha', hp unfolding stepFalse, R.instFVarsCore_base
      exact c₀.trans (c₁.trans (c₂.trans (c₃.trans
        (hc.base hF hn a b (.inr (Nat.lt_of_not_le hba))))))

include hd hf h hF hE hn hsub hc in
theorem RecSpec.eval (a b : Nat) :
    FEq E (R.entry (.natLit C.Nat_ a) (.natLit C.Nat_ b)) (.natLit C.Nat_ (f a b)) (nat C.Nat_) := by
  have ha' := FEq.natLit hF hn a
  have hb' := FEq.natLit hF hn b
  schema_have c₁ := h.unfold Fuel.unfold #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using ha', hb' unfolding onTrue, onFalse, R.instFVarsCore_entry, R.instFVarsCore_base
  schema_have ht := h.onTrueType Fuel.onTrueType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using ha', hb' unfolding onTrue
  schema_have he := h.onFalseType Fuel.onFalseType #[.natLit C.Nat_ a, .natLit C.Nat_ b] #[.natLit C.Nat_ a, .natLit C.Nat_ b]
    using ha', hb' unfolding onFalse, R.instFVarsCore_base
  have ⟨p, hp, c₂⟩ := hd 1 b hF hE ht he
  by_cases hb : 1 ≤ b
  · simp only [hb, decide_true, Bool.cond_true] at hp c₂
    schema_have c₃ := h.onTrueBeta Fuel.onTrueBeta #[.natLit C.Nat_ a, .natLit C.Nat_ b, p]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b, p] using ha', hb', hp unfolding onTrue
    have ha₁ := FEq.succLit hF hn a
    schema_have hlt := hf.ltSuccSelfType Fuel.ltSuccSelfType #[.natLit C.Nat_ a] #[.natLit C.Nat_ a] using ha'
    schema_have hlt₂ := hf.ltCongr Fuel.ltCongr #[.natLit C.Nat_ a, succ C.Nat_ (.natLit C.Nat_ a)]
      #[.natLit C.Nat_ a, .natLit C.Nat_ (a + 1)] using ha', ha₁
    schema_have c₄ := h.goCongr Fuel.goCongr
      #[.natLit C.Nat_ b, p, succ C.Nat_ (.natLit C.Nat_ a), .natLit C.Nat_ a, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
      #[.natLit C.Nat_ b, p, .natLit C.Nat_ (a + 1), .natLit C.Nat_ a, FExpr.Nat.lt_succ_self C (.natLit C.Nat_ a)]
      using hb', hp, ha₁, ha', hlt
    have c₅ := h.goEval hd hf hF hE hn hsub hc hb hp (Nat.lt_succ_self a) (hlt.conv hlt₂)
    exact c₁.trans (c₂.trans (c₃.trans (c₄.trans c₅)))
  · simp only [hb, decide_false, Bool.cond_false] at hp c₂
    schema_have c₃ := h.onFalseBeta Fuel.onFalseBeta #[.natLit C.Nat_ a, .natLit C.Nat_ b, p]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b, p] using ha', hb', hp unfolding onFalse, R.instFVarsCore_base
    exact c₁.trans (c₂.trans (c₃.trans (hc.base hF hn a b (.inl (by omega)))))

end

def verify (hd : Decide.DecLe F C) (R : Rec) (sub : NatOp F Nat.sub)
    {f : Nat → Nat → Nat} (hc : R.Computes F C f) :
    EIO Failure (PLift (Eval F C R f)) := do
  let ⟨hn⟩ ← natAt F C.Nat_
  let ⟨hsub⟩ ← sub.at F C.Nat_
  if hs : sub.pos = C.Nat_sub then
    let ⟨hf⟩ ← check F C hints
    let ⟨h⟩ ← checkRec F C hints R
    pure ⟨⟨hn, fun _ _ hF hE => h.eval hd hf hF hE hn (hs ▸ hsub) hc⟩⟩
  else throw .internal

end Fuel

end Metalean.Checker.Fast
