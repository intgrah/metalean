/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.LiteralTyping

@[expose] public section

namespace Metalean.FastChecker.Literals

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {ηNat : Head ζ (.inductive Nat.sig)} {ηBool : Head ζ (.inductive Bool.sig)}
  {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}

def UnaryType (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηOp : Head ζ (.const kind 0)) : Prop :=
  ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n},
  E[Γ] ⊢ (.const ηOp ![] : Expr ζ ℓ n) ≡ .const ηOp ![] : natArrow ηNat

def BinaryType (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηOp : Head ζ (.const kind 0)) : Prop :=
  ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n},
  E[Γ] ⊢ (.const ηOp ![] : Expr ζ ℓ n) ≡ .const ηOp ![] : natArrow₂ ηNat

theorem natArrowDF :
    E[Γ] ⊢ (natArrow ηNat : Expr ζ ℓ n) ≡ natArrow ηNat :
      .sort (.imax ((E.get ηNat).block.level.inst ![]) ((E.get ηNat).block.level.inst ![])) :=
  .forallEDF natTypeDF natTypeDF natTypeDF

theorem natArrow_inst (a : Expr ζ ℓ n) :
    (natArrow ηNat : Expr ζ ℓ (n + 1)).inst a = natArrow ηNat := by
  change Expr.forallE ((natType ηNat).subst _) ((natType ηNat).subst _) = _
  simp [natType_subst]
  rfl

theorem natOp₁DF {a₁ a₂ : Expr ζ ℓ n} :
    UnaryType E ηNat ηOp →
    E[Γ] ⊢ a₁ ≡ a₂ : natType ηNat →
    E[Γ] ⊢ natOp₁ ηOp a₁ ≡ natOp₁ ηOp a₂ : natType ηNat := by
  intro htype h
  have happ := Defeq.appDF
    natTypeDF natTypeDF htype h (by rw [Expr.inst, Expr.inst, natType_subst, natType_subst]; exact natTypeDF)
  rwa [Expr.inst, natType_subst] at happ

theorem natOp₂DF {a₁ a₂ b₁ b₂ : Expr ζ ℓ n} :
    BinaryType E ηNat ηOp →
    E[Γ] ⊢ a₁ ≡ a₂ : natType ηNat →
    E[Γ] ⊢ b₁ ≡ b₂ : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp a₁ b₁ ≡ natOp₂ ηOp a₂ b₂ : natType ηNat := by
  intro htype ha hb
  have hfun := Defeq.appDF
    natTypeDF natArrowDF htype ha (by rw [natArrow_inst, natArrow_inst]; exact natArrowDF)
  rw [natArrow_inst] at hfun
  have happ := Defeq.appDF
    natTypeDF natTypeDF hfun hb (by rw [Expr.inst, Expr.inst, natType_subst, natType_subst]; exact natTypeDF)
  rwa [Expr.inst, natType_subst] at happ

structure AddEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηOp : Head ζ (.const kind 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ x : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡ natSucc ηNat (natOp₂ ηOp x y) : natType ηNat

theorem add_natLit (num₁ num₂ : Nat) :
    AddEqs E ηNat ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ + num₂) : natType ηNat := by
  intro h
  induction num₂ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact (h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans (natSuccDF ih)

structure PredEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηOp : Head ζ (.const kind 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} :
    E[Γ] ⊢ natOp₁ ηOp (natZero ηNat) ≡ natZero ηNat : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (y : Expr ζ ℓ n) :
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₁ ηOp (natSucc ηNat y) ≡ y : natType ηNat

theorem pred_natLit :
    (num : Nat) →
    PredEqs E ηNat ηOp →
    E[Γ] ⊢ natOp₁ ηOp (natLit ηNat num) ≡ natLit ηNat (num - 1) : natType ηNat
  | 0, h => h.zero
  | _ + 1, h => h.succ _ (natLit_typed _ _)

structure SubEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    {kind₁ kind₂ : ConstKind} (ηPred : Head ζ (.const kind₁ 0))
    (ηOp : Head ζ (.const kind₂ 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ x : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡ natOp₁ ηPred (natOp₂ ηOp x y) : natType ηNat

theorem sub_natLit {kind₁ : ConstKind} {ηPred : Head ζ (.const kind₁ 0)} (num₁ num₂ : Nat) :
    UnaryType E ηNat ηPred →
    PredEqs E ηNat ηPred →
    SubEqs E ηNat ηPred ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ - num₂) : natType ηNat := by
  intro htype hpred h
  induction num₂ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact ((h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans
      (natOp₁DF htype ih)).trans (pred_natLit _ hpred)

structure MulEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    {kind₁ kind₂ : ConstKind} (ηAdd : Head ζ (.const kind₁ 0))
    (ηOp : Head ζ (.const kind₂ 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ natZero ηNat : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡ natOp₂ ηAdd (natOp₂ ηOp x y) x : natType ηNat

theorem mul_natLit {kind₁ : ConstKind} {ηAdd : Head ζ (.const kind₁ 0)} (num₁ num₂ : Nat) :
    BinaryType E ηNat ηAdd →
    AddEqs E ηNat ηAdd →
    MulEqs E ηNat ηAdd ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ * num₂) : natType ηNat := by
  intro htype hadd h
  induction num₂ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact ((h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans
      (natOp₂DF htype ih (natLit_typed _ _))).trans (add_natLit _ _ hadd)

structure PowEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    {kind₁ kind₂ : ConstKind} (ηMul : Head ζ (.const kind₁ 0))
    (ηOp : Head ζ (.const kind₂ 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ natSucc ηNat (natZero ηNat) : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡ natOp₂ ηMul (natOp₂ ηOp x y) x : natType ηNat

theorem pow_natLit {kind₂ : ConstKind} {ηMul : Head ζ (.const kind₂ 0)}
    {kind₁ : ConstKind} {ηAdd : Head ζ (.const kind₁ 0)} (num₁ num₂ : Nat) :
    BinaryType E ηNat ηMul →
    BinaryType E ηNat ηAdd →
    AddEqs E ηNat ηAdd →
    MulEqs E ηNat ηAdd ηMul →
    PowEqs E ηNat ηMul ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ ^ num₂) : natType ηNat := by
  intro htype haddType hadd hmul h
  induction num₂ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact ((h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans
      (natOp₂DF htype ih (natLit_typed _ _))).trans (mul_natLit _ _ haddType hadd hmul)

structure ShiftLeftEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    {kind₁ kind₂ : ConstKind} (ηMul : Head ζ (.const kind₁ 0))
    (ηOp : Head ζ (.const kind₂ 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ x : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡
      natOp₂ ηOp (natOp₂ ηMul (natLit ηNat 2) x) y : natType ηNat

theorem shiftLeft_natLit {kind₁ : ConstKind} {ηAdd : Head ζ (.const kind₁ 0)}
    {kind₂ : ConstKind} {ηMul : Head ζ (.const kind₂ 0)} (num₁ num₂ : Nat) :
    BinaryType E ηNat ηOp →
    BinaryType E ηNat ηAdd →
    AddEqs E ηNat ηAdd →
    MulEqs E ηNat ηAdd ηMul →
    ShiftLeftEqs E ηNat ηMul ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ <<< num₂) : natType ηNat := by
  intro htype haddType hadd hmul h
  induction num₂ generalizing num₁ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact ((h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans
      (natOp₂DF htype (mul_natLit 2 num₁ haddType hadd hmul) (natLit_typed _ _))).trans
      (ih (2 * num₁))

structure ShiftRightEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    {kind₁ kind₂ : ConstKind} (ηDiv : Head ζ (.const kind₁ 0))
    (ηOp : Head ζ (.const kind₂ 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natZero ηNat) ≡ x : natType ηNat
  succ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp x (natSucc ηNat y) ≡
      natOp₂ ηDiv (natOp₂ ηOp x y) (natLit ηNat 2) : natType ηNat

theorem shiftRight_natLit {kind₁ : ConstKind} {ηDiv : Head ζ (.const kind₁ 0)}
    (num₁ num₂ : Nat) :
    BinaryType E ηNat ηDiv →
    (∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (num₃ num₄ : Nat),
      E[Γ] ⊢ natOp₂ ηDiv (natLit ηNat num₃) (natLit ηNat num₄) ≡
        natLit ηNat (num₃ / num₄) : natType ηNat) →
    ShiftRightEqs E ηNat ηDiv ηOp →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      natLit ηNat (num₁ >>> num₂) : natType ηNat := by
  intro hdivType hdiv h
  induction num₂ with
  | zero => exact h.zero _ (natLit_typed _ _)
  | succ num₂ ih =>
    exact ((h.succ _ _ (natLit_typed _ _) (natLit_typed _ _)).trans
      (natOp₂DF hdivType ih (natLit_typed _ _))).trans (hdiv _ 2)

structure BeqEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηBool : Head ζ (.inductive Bool.sig)) (ηOp : Head ζ (.const kind 0)) : Prop where
  zeroZero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} :
    E[Γ] ⊢ natOp₂ ηOp (natZero ηNat) (natZero ηNat) ≡ boolTrue ηBool : boolType ηBool
  zeroSucc {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (y : Expr ζ ℓ n) :
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natZero ηNat) (natSucc ηNat y) ≡ boolFalse ηBool : boolType ηBool
  succZero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natSucc ηNat x) (natZero ηNat) ≡ boolFalse ηBool : boolType ηBool
  succSucc {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natSucc ηNat x) (natSucc ηNat y) ≡ natOp₂ ηOp x y : boolType ηBool

theorem beq_natLit {ηBool : Head ζ (.inductive Bool.sig)} (h : BeqEqs E ηNat ηBool ηOp) :
    (num₁ num₂ : Nat) →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      boolLit ηBool (Nat.beq num₁ num₂) : boolType ηBool
  | 0, 0 => h.zeroZero
  | 0, _ + 1 => h.zeroSucc _ (natLit_typed _ _)
  | _ + 1, 0 => h.succZero _ (natLit_typed _ _)
  | num₁ + 1, num₂ + 1 =>
    (h.succSucc _ _ (natLit_typed _ _) (natLit_typed _ _)).trans (beq_natLit h num₁ num₂)

structure BleEqs (E : Env ζ) (ηNat : Head ζ (.inductive Nat.sig))
    (ηBool : Head ζ (.inductive Bool.sig)) (ηOp : Head ζ (.const kind 0)) : Prop where
  zero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (y : Expr ζ ℓ n) :
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natZero ηNat) y ≡ boolTrue ηBool : boolType ηBool
  succZero {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natSucc ηNat x) (natZero ηNat) ≡ boolFalse ηBool : boolType ηBool
  succSucc {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} (x y : Expr ζ ℓ n) :
    E[Γ] ⊢ x : natType ηNat →
    E[Γ] ⊢ y : natType ηNat →
    E[Γ] ⊢ natOp₂ ηOp (natSucc ηNat x) (natSucc ηNat y) ≡ natOp₂ ηOp x y : boolType ηBool

theorem ble_natLit {ηBool : Head ζ (.inductive Bool.sig)} (h : BleEqs E ηNat ηBool ηOp) :
    (num₁ num₂ : Nat) →
    E[Γ] ⊢ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
      boolLit ηBool (Nat.ble num₁ num₂) : boolType ηBool
  | 0, _ => h.zero _ (natLit_typed _ _)
  | _ + 1, 0 => h.succZero _ (natLit_typed _ _)
  | num₁ + 1, num₂ + 1 =>
    (h.succSucc _ _ (natLit_typed _ _) (natLit_typed _ _)).trans (ble_natLit h num₁ num₂)

end Metalean.FastChecker.Literals
