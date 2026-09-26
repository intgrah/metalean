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

open scoped FExpr

open Frontend (Failure Table)

namespace Mod

structure Consts extends toFuel : Fuel.Consts where
  protected Nat_modCore : Nat
  protected Nat_modCore_go : Nat

instance : CoeOut Consts Fuel.Consts := ⟨Consts.toFuel⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    toFuel := ← Fuel.Consts.resolve t
    Nat_modCore := ← t.const ``Nat.modCore
    Nat_modCore_go := ← t.const ``Nat.modCore.go }

end Mod

namespace FExpr

variable (C : Mod.Consts)

@[fexpr_unfold]
protected def Nat.modCore (x y : FExpr) : FExpr :=
  .appList (.const C.Nat_modCore #[]) [x, y]

end FExpr

namespace Mod

variable (F : FEnv) (C : Consts) (hints : Array Export.Hints)

def fuelRec : Fuel.Rec where
  pos := C.Nat_modCore_go
  entry := FExpr.Nat.modCore C
  step r := r
  base x := x
  instFVarsCore_entry _ _ _ := by simp [FExpr.Nat.modCore, instFVarsCore]
  instFVarsCore_step _ _ := rfl
  instFVarsCore_base _ _ := rfl

theorem computes : (fuelRec C).Computes F C HMod.hMod where
  step _ _ hF hn a b _ hba := by
    rw [Nat.mod_eq_sub_mod hba]
    exact FEq.natLit hF hn _
  base _ _ hF hn a b h := by
    rcases h with rfl | h
    · rw [Nat.mod_zero]
      exact FEq.natLit hF hn a
    · rw [Nat.mod_eq_of_lt h]
      exact FEq.natLit hF hn a

def onTrue (x y : FExpr) : FExpr :=
  .lam (FExpr.Nat.le C y x) (FExpr.Nat.modCore C x y)

def onFalse (x y : FExpr) : FExpr :=
  .lam (FExpr.Not C (FExpr.Nat.le C y x)) x

variable (pos : Nat)

def modCongr : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢ op₂ pos x y : nat C.Nat_

def zeroUnfold : Schema :=
  schema% (y : nat C.Nat_) ⊢ op₂ pos (zero C.Nat_) y ≡ zero C.Nat_ : nat C.Nat_

def succUnfold : Schema :=
  schema% (n : nat C.Nat_) (y : nat C.Nat_) ⊢
    op₂ pos (succ C.Nat_ n) y ≡
      FExpr.dite C (nat C.Nat_) (FExpr.Nat.le C y (succ C.Nat_ n))
        (FExpr.Nat.decLe C y (succ C.Nat_ n)) (onTrue C (succ C.Nat_ n) y)
        (onFalse C (succ C.Nat_ n) y) :
    nat C.Nat_

def diteCongr : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    FExpr.dite C (nat C.Nat_) (FExpr.Nat.le C y x) (FExpr.Nat.decLe C y x) (onTrue C x y)
      (onFalse C x y) :
    nat C.Nat_

def onTrueType : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    onTrue C x y : FExpr.Nat.le C y x ⟶ nat C.Nat_

def onFalseType : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) ⊢
    onFalse C x y : FExpr.Not C (FExpr.Nat.le C y x) ⟶ nat C.Nat_

def onTrueBeta : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) (p : FExpr.Nat.le C y x) ⊢
    .app (onTrue C x y) p ≡ FExpr.Nat.modCore C x y : nat C.Nat_

def onFalseBeta : Schema :=
  schema% (x : nat C.Nat_) (y : nat C.Nat_) (p : FExpr.Not C (FExpr.Nat.le C y x)) ⊢
    .app (onFalse C x y) p ≡ x : nat C.Nat_

structure Spec : Prop where
  modCongr : (modCongr C pos).Spec F
  zeroUnfold : (zeroUnfold C pos).Spec F
  succUnfold : (succUnfold C pos).Spec F
  diteCongr : (diteCongr C).Spec F
  onTrueType : (onTrueType C).Spec F
  onFalseType : (onFalseType C).Spec F
  onTrueBeta : (onTrueBeta C).Spec F
  onFalseBeta : (onFalseBeta C).Spec F

def check : EIO Failure (PLift (Spec F C pos)) := do
  let ⟨modCongr⟩ ← (modCongr C pos).check F hints
  let ⟨zeroUnfold⟩ ← (zeroUnfold C pos).check F hints
  let ⟨succUnfold⟩ ← (succUnfold C pos).check F hints
  let ⟨diteCongr⟩ ← (diteCongr C).check F hints
  let ⟨onTrueType⟩ ← (onTrueType C).check F hints
  let ⟨onFalseType⟩ ← (onFalseType C).check F hints
  let ⟨onTrueBeta⟩ ← (onTrueBeta C).check F hints
  let ⟨onFalseBeta⟩ ← (onFalseBeta C).check F hints
  pure ⟨⟨modCongr, zeroUnfold, succUnfold, diteCongr, onTrueType, onFalseType, onTrueBeta,
    onFalseBeta⟩⟩

section

variable {F C pos} (hd : Decide.DecLe F C) (h : Spec F C pos) {ζ : Sigs} {E : Env ζ}
  (hF : FEnv.Denotes F E) (hE : EnvWF E) (hr : Fuel.Eval F C (fuelRec C) HMod.hMod)

include hd h hF hE hr in
theorem Spec.modEval (a b : Nat) :
    FEq E (op₂ pos (.natLit C.Nat_ a) (.natLit C.Nat_ b)) (.natLit C.Nat_ (a % b)) (nat C.Nat_) := by
  have hn := hr.natSpec
  have hb' := FEq.natLit hF hn b
  cases a with
  | zero =>
    have h₀ := (FEq.zeroLit hF hn).symm
    schema_have c₁ := h.modCongr Mod.modCongr #[.natLit C.Nat_ 0, .natLit C.Nat_ b] #[zero C.Nat_, .natLit C.Nat_ b]
      using h₀, hb'
    schema_have c₂ := h.zeroUnfold Mod.zeroUnfold #[.natLit C.Nat_ b] #[.natLit C.Nat_ b] using hb'
    rw [Nat.zero_mod]
    exact c₁.trans (c₂.trans h₀.symm)
  | succ a =>
    have ha' := FEq.natLit hF hn a
    have ha₁' := FEq.natLit hF hn (a + 1)
    have ha₁ := FEq.succLit hF hn a
    schema_have c₁ := h.modCongr Mod.modCongr #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b]
      #[succ C.Nat_ (.natLit C.Nat_ a), .natLit C.Nat_ b] using ha₁.symm, hb'
    schema_have c₂ := h.succUnfold Mod.succUnfold #[.natLit C.Nat_ a, .natLit C.Nat_ b]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b] using ha', hb' unfolding onTrue, onFalse
    schema_have c₃ := h.diteCongr Mod.diteCongr #[succ C.Nat_ (.natLit C.Nat_ a), .natLit C.Nat_ b]
      #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b] using ha₁, hb' unfolding onTrue, onFalse
    schema_have ht := h.onTrueType Mod.onTrueType #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b]
      #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b] using ha₁', hb' unfolding onTrue
    schema_have he := h.onFalseType Mod.onFalseType #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b]
      #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b] using ha₁', hb' unfolding onFalse
    have ⟨p, hp, c₄⟩ := hd b (a + 1) hF hE ht he
    by_cases hba : b ≤ a + 1
    · simp only [hba, decide_true, Bool.cond_true] at hp c₄
      schema_have c₅ := h.onTrueBeta Mod.onTrueBeta #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b, p]
        #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b, p] using ha₁', hb', hp unfolding onTrue
      exact c₁.trans (c₂.trans (c₃.trans (c₄.trans (c₅.trans (hr.eq hF hE (a + 1) b)))))
    · simp only [hba, decide_false, Bool.cond_false] at hp c₄
      schema_have c₅ := h.onFalseBeta Mod.onFalseBeta #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b, p]
        #[.natLit C.Nat_ (a + 1), .natLit C.Nat_ b, p] using ha₁', hb', hp unfolding onFalse
      rw [Nat.mod_eq_of_lt (Nat.lt_of_not_le hba)]
      exact c₁.trans (c₂.trans (c₃.trans (c₄.trans c₅)))

end

def verify (hd : Decide.DecLe F C) (pos : Nat) (sub : NatOp F Nat.sub) :
    EIO Failure (NatOp F Nat.mod) := do
  let ⟨hop⟩ ← constDef F pos
  let ⟨hr⟩ ← Fuel.verify F C hints hd (fuelRec C) sub (computes F C)
  let ⟨h⟩ ← check F C hints pos
  pure ⟨C.Nat_, pos, NatOpSpec.ofFEq hr.natSpec hop fun _ _ hF hE => h.modEval hd hF hE hr⟩

end Mod

end Metalean.Checker.Fast
