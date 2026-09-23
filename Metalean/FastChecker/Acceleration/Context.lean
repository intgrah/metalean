/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Spec
public import Metalean.FastChecker.LiteralTyping
import Metalean.Typing.Substitution
import Metalean.Typing.InstLevel

@[expose] public section

namespace Metalean.FastChecker

variable (L : Literals)

def natCtx : FCtx :=
  #[.nat L, .nat L]

variable {L} {ζ : Sigs} {ℓ n k : Nat} {ηNat : Head ζ (.inductive Literals.Nat.sig)}
  {ηBool : Head ζ (.inductive Literals.Bool.sig)}

variable {F : FEnv} {E : Env ζ}

def natCtx' (ηNat : Head ζ (.inductive Literals.Nat.sig)) : Ctx ζ ℓ 0 2 :=
  (Ctx.nil.snoc (Literals.natType ηNat)).snoc (Literals.natType ηNat)

theorem natCtxSem (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    EnvWF E →
    FEnv.Denotes L F E →
    L.NatTrust E →
    Sem L F (natCtx L) E (natCtx' (ℓ := 0) ηNat) := fun hE hF htr =>
  ((Sem.nil hF hE htr).snoc (.nat hη) Literals.natTypeDF).snoc (.nat hη) Literals.natTypeDF

def natSubst {ℓ n : Nat} (x y : Expr ζ ℓ n) : Subst ζ ℓ 2 n :=
  (Subst.extend (fun v => v.elim0) x).extend y

theorem natCtx'_instL {ℓ : Nat} (ls : Param 0 → Level ℓ) :
    (natCtx' (ℓ := 0) ηNat){ls} = natCtx' (ℓ := ℓ) ηNat := by
  simp [natCtx', Literals.natType_instL]

theorem natSubstWF {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {x y : Expr ζ ℓ n} :
    E[Γ] ⊢ x : Literals.natType ηNat →
    E[Γ] ⊢ y : Literals.natType ηNat →
    E[Γ] ⊢ natSubst x y ⊣ natCtx' ηNat := by
  intro hx hy
  refine SubstWF.extend ?_ (SubstWF.extend ?_ fun v => v.elim0)
  · rwa [Literals.natType_subst]
  · rwa [Literals.natType_subst]

structure Instantiated (L : Literals) {ζ : Sigs} (E : Env ζ) {ℓ n : Nat} (x y : Expr ζ ℓ n) (fe : FExpr)
    (e : Expr ζ ℓ n) where
  base : Expr ζ 0 2
  denotes : FExpr.Denotes L ⟨ζ, E⟩ 0 fe base
  inst : base{fun p : Param 0 => (p.elim0 : Level ℓ)}.subst (natSubst x y) = e

variable {x y : Expr ζ ℓ n}

def Instantiated.natType (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Instantiated L E x y (FExpr.nat L) (Literals.natType ηNat) :=
  ⟨_, FExpr.Denotes.nat hη, by
    simp [Literals.natType_instL, Literals.natType_subst]⟩

def Instantiated.boolType (hη : ζ.lookup L.bool = some ⟨.inductive Literals.Bool.sig, ηBool⟩) :
    Instantiated L E x y (FExpr.bool L) (Literals.boolType ηBool) :=
  ⟨_, FExpr.Denotes.boolType hη, by
    simp [Literals.boolType_instL, Literals.boolType_subst]⟩

def Instantiated.natArrow (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Instantiated L E x y (FExpr.natArrow L) (Literals.natArrow ηNat) :=
  ⟨_, .natArrow hη, by
    simp [Literals.natArrow_instL, Literals.natArrow_subst]⟩

def Instantiated.natArrow₂ (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Instantiated L E x y (FExpr.natArrow₂ L) (Literals.natArrow₂ ηNat) :=
  ⟨_, .natArrow₂ hη, by
    simp [Literals.natArrow₂_instL, Literals.natArrow₂_subst]⟩

def Instantiated.zero (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Instantiated L E x y (FExpr.zero L) (Literals.natZero ηNat) :=
  ⟨Literals.natZero ηNat, FExpr.Denotes.zero hη, by
    simp [Literals.natZero_instL, Literals.natZero_subst]⟩

def Instantiated.boolLit (hη : ζ.lookup L.bool = some ⟨.inductive Literals.Bool.sig, ηBool⟩)
    (b : Bool) :
    Instantiated L E x y (FExpr.boolLit L b) (Literals.boolLit ηBool b) :=
  ⟨_, FExpr.Denotes.boolLit hη b, by
    simp [Literals.boolLit_instL, Literals.boolLit_subst]⟩

def Instantiated.succ (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩)
    {fe : FExpr} {e : Expr ζ ℓ n} (h : Instantiated L E x y fe e) :
    Instantiated L E x y (FExpr.succ L fe) (Literals.natSucc ηNat e) :=
  ⟨_, FExpr.Denotes.succ hη h.denotes, by
    simp [Literals.natSucc_instL, Literals.natSucc_subst, h.inst]⟩

def Instantiated.op {pos : Nat} {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}
    (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩) {fe₁ fe₂ : FExpr} {e₁ e₂ : Expr ζ ℓ n}
    (h₁ : Instantiated L E x y fe₁ e₁) (h₂ : Instantiated L E x y fe₂ e₂) :
    Instantiated L E x y (FExpr.op₂ pos fe₁ fe₂) (Literals.natOp₂ ηOp e₁ e₂) :=
  ⟨_, FExpr.Denotes.op₂ hη h₁.denotes h₂.denotes, by
    simp [Literals.natOp₂_instL, Literals.natOp₂_subst, h₁.inst, h₂.inst]⟩

def Instantiated.op1 {pos : Nat} {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}
    (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩) {fe : FExpr} {e : Expr ζ ℓ n}
    (h : Instantiated L E x y fe e) :
    Instantiated L E x y (FExpr.op₁ pos fe) (Literals.natOp₁ ηOp e) :=
  ⟨_, FExpr.Denotes.op₁ hη h.denotes, by
    simp [Literals.natOp₁_instL, Literals.natOp₁_subst, h.inst]⟩

def Instantiated.const {pos : Nat} {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}
    (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩) :
    Instantiated L E x y (.const pos #[]) (.const ηOp ![]) :=
  ⟨.const ηOp ![], FExpr.Denotes.const₀ hη, congr(.const ηOp $(funext nofun))⟩

def Instantiated.natLit (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩)
    (num : Nat) :
    Instantiated L E x y (.natLit num) (Literals.natLit ηNat num) :=
  ⟨_, .natLit hη, by
    simp [Literals.instL_natLit, Literals.subst_natLit]⟩

def Instantiated.varX : Instantiated L E x y (.fvar 0) x :=
  ⟨.var ⟨0, by omega⟩, .fvar (by omega), rfl⟩

def Instantiated.varY : Instantiated L E x y (.fvar 1) y :=
  ⟨.var ⟨1, by omega⟩, .fvar (by omega), rfl⟩

structure NatAt (L : Literals) (F : FEnv) {ζ : Sigs} (E : Env ζ)
    (ηNat : Head ζ (.inductive Literals.Nat.sig)) {ℓ n : Nat} (Γ : Ctx ζ ℓ 0 n)
    (x y : Expr ζ ℓ n) : Prop where
  env : FEnv.Denotes L F E
  wf : EnvWF E
  trust : L.NatTrust E
  nat : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩
  varX : E[Γ] ⊢ x : Literals.natType ηNat
  varY : E[Γ] ⊢ y : Literals.natType ηNat

theorem NatAt.eq {Γ : Ctx ζ ℓ 0 n} {ft fe₁ fe₂ : FExpr} {t e₁ e₂ : Expr ζ ℓ n} :
    NatAt L F E ηNat Γ x y →
    DefEqAtSpec L F 0 (natCtx L) ft fe₁ fe₂ →
    Instantiated L E x y ft t →
    Instantiated L E x y fe₁ e₁ →
    Instantiated L E x y fe₂ e₂ →
    E[Γ] ⊢ e₁ ≡ e₂ : t := by
  intro ha h ht h₁ h₂
  have hlev := (h (natCtxSem ha.nat ha.wf ha.env ha.trust) ht.denotes h₁.denotes h₂.denotes).instLevel
    (fun p : Param 0 => (p.elim0 : Level ℓ))
  rw [natCtx'_instL] at hlev
  have hres := hlev.substitution (natSubstWF ha.varX ha.varY)
  rw [ht.inst, h₁.inst, h₂.inst] at hres
  exact hres

end Metalean.FastChecker
