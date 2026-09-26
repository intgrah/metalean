/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Prelude
public import Metalean.Checker.Fast.Acceleration.Schema

@[expose] public section

namespace Metalean.Checker.Fast

open Acceleration

syntax "schema_args " ident " using " term,* : tactic

macro_rules
  | `(tactic| schema_args $s:ident using $hs,*) =>
    `(tactic| (
      intro i hi
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | (simp [$s:ident] at hi <;> omega)
        | (fexpr_simp [$s:ident]; first $[| exact $hs]*)))

syntax "schema_inst " term:max ident term:max term:max " using " term,* : tactic

set_option hygiene false in
macro_rules
  | `(tactic| schema_inst $h $s:ident $as $bs using $hs,*) =>
    `(tactic| (
      have this := ($h).inst hF hE (as := $as) (bs := $bs) rfl rfl
        (by schema_args $s using $hs,*)
      fexpr_simp [$s:ident] at this ⊢
      exact this))

syntax "schema_have " ident " := " term:max ident term:max term:max " using " term,*
  (" unfolding " ident,*)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| schema_have $c := $h $s $as $bs using $hs,* $[unfolding $us,*]?) => do
    let us := (us.map (·.getElems)).getD #[]
    `(tactic| (
      have $c := ($h).inst hF hE (as := $as) (bs := $bs) rfl rfl
        (by schema_args $s using $hs,*)
      fexpr_simp [$s:ident, $[$us:ident],*] at $c:ident))

variable {F : FEnv} {ζ : Sigs} {E : Env ζ} {p : Nat}

theorem FExpr.NoProj.nat (p : Nat) : (FExpr.nat p).NoProj :=
  .ind (by simp) (by simp)

theorem FExpr.NoProj.bool (b : Nat) : (FExpr.bool b).NoProj :=
  .ind (by simp) (by simp)

theorem FExpr.NoProj.boolLit (b : Nat) (v : Bool) : (FExpr.boolLit b v).NoProj := by
  cases v <;> exact .ctor (by simp) (by simp) (by simp)

theorem FExpr.NoProj.zero (p : Nat) : (FExpr.zero p).NoProj :=
  .ctor (by simp) (by simp) (by simp)

theorem FExpr.NoProj.succ (p : Nat) {fe : FExpr} (h : fe.NoProj) : (FExpr.succ p fe).NoProj :=
  .ctor (by simp) (by simp) (by simp [h])

theorem FExpr.NoProj.op₂ (pos : Nat) {fe₁ fe₂ : FExpr} (h₁ : fe₁.NoProj) (h₂ : fe₂.NoProj) :
    (FExpr.op₂ pos fe₁ fe₂).NoProj :=
  .app (.app (.const _ _) h₁) h₂

theorem FEq.left {a b t : FExpr} :
    FEq E a b t →
    FEq E a a t :=
  fun h => h.trans h.symm

theorem FEq.natLit (hF : FEnv.Denotes F E) (hn : NatSpec F p) (a : Nat) :
    FEq E (.natLit p a) (.natLit p a) (FExpr.nat p) :=
  have ⟨_, hnat⟩ := hn.sig
  have ⟨η, hη, _⟩ := hF.inductive hnat
  ⟨.natLit p a, .natLit p a, .nat p, fun _ _ _ =>
    ⟨_, _, _, .natLit hη, .natLit hη, .nat hη, Expr.natLit_typed η a⟩⟩

theorem FEq.natOp {pos : Nat} {f : Nat → Nat → Nat} (hF : FEnv.Denotes F E) (hE : EnvWF E)
    (hn : NatSpec F p) (h : NatOpSpec F p pos f) (a b : Nat) :
    FEq E (FExpr.op₂ pos (.natLit p a) (.natLit p b)) (.natLit p (f a b)) (FExpr.nat p) :=
  have ⟨_, hnat⟩ := hn.sig
  have ⟨_, hη, _⟩ := hF.inductive hnat
  have ⟨_, hηOp⟩ := ConstHeadSpec.ofDef h.opDef hF
  ⟨.op₂ pos (.natLit p a) (.natLit p b), .natLit _ _, .nat p, fun _ _ _ =>
    ⟨_, _, _, .op₂ hηOp (.natLit hη) (.natLit hη), .natLit hη, .nat hη,
      h.eq hF hE hη hηOp _ a b⟩⟩

theorem FEq.boolOp {bool pos : Nat} {f : Nat → Nat → Bool} (hF : FEnv.Denotes F E)
    (hE : EnvWF E) (hn : NatSpec F p) (h : BoolOpSpec F p bool pos f) (a b : Nat) :
    FEq E (FExpr.op₂ pos (.natLit p a) (.natLit p b)) (FExpr.boolLit bool (f a b))
      (FExpr.bool bool) :=
  have ⟨_, hnat⟩ := hn.sig
  have ⟨_, hη, _⟩ := hF.inductive hnat
  have ⟨_, hbool⟩ := h.boolSig
  have ⟨_, hηBool, _⟩ := hF.inductive hbool
  have ⟨_, hηOp⟩ := ConstHeadSpec.ofDef h.opDef hF
  ⟨.op₂ pos (.natLit p a) (.natLit p b), .boolLit bool _, .bool bool,
    fun _ _ _ => ⟨_, _, _, .op₂ hηOp (.natLit hη) (.natLit hη), .boolLit hηBool _,
      .boolType hηBool, h.eq hF hE hη hηBool hηOp _ a b⟩⟩

theorem FEq.zeroLit (hF : FEnv.Denotes F E) (hn : NatSpec F p) :
    FEq E (FExpr.zero p) (.natLit p 0) (FExpr.nat p) :=
  have ⟨_, hnat⟩ := hn.sig
  have ⟨η, hη, _⟩ := hF.inductive hnat
  ⟨.zero p, .natLit p 0, .nat p, fun _ _ _ =>
    ⟨_, _, _, .zero hη, .natLit hη, .nat hη, Expr.natLit_typed η 0⟩⟩

theorem FEq.succLit (hF : FEnv.Denotes F E) (hn : NatSpec F p) (a : Nat) :
    FEq E (FExpr.succ p (.natLit p a)) (.natLit p (a + 1)) (FExpr.nat p) :=
  have ⟨_, hnat⟩ := hn.sig
  have ⟨η, hη, _⟩ := hF.inductive hnat
  ⟨.succ p (.natLit p a), .natLit _ _, .nat p,
    fun _ _ _ => ⟨_, _, _, .succLit hη, .natLit hη, .nat hη,
      Expr.natLit_typed η (a + 1)⟩⟩

theorem NatOpSpec.ofFEq {pos : Nat} {f : Nat → Nat → Nat} (hn : NatSpec F p)
    (hop : ∃ t v, F[pos]? = some (.def 0 t v))
    (h : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄, FEnv.Denotes F E → EnvWF E → ∀ a b,
      FEq E (FExpr.op₂ pos (.natLit p a) (.natLit p b)) (.natLit p (f a b)) (FExpr.nat p)) :
    NatOpSpec F p pos f where
  natSig := hn.sig
  opDef := hop
  eq {_ E _ _ _} hF hE hη hηOp _ _ Γ a b := by
    have ⟨ea, eb, et, hda, hdb, hdt, d⟩ := (h hF hE a b).defeq Γ
    obtain rfl := hda.unique (.op₂ hηOp (.natLit hη) (.natLit hη))
      (.op₂ _ (.natLit _ _) (.natLit _ _))
    obtain rfl := hdb.unique (.natLit hη) (.natLit _ _)
    obtain rfl := hdt.unique (.nat hη) (.nat _)
    exact d

theorem BoolOpSpec.ofFEq {bool pos : Nat} {f : Nat → Nat → Bool} (hn : NatSpec F p)
    (hbool : ∃ I : FInductive, F[bool]? = some (.inductive Bool.sig I))
    (hop : ∃ t v, F[pos]? = some (.def 0 t v))
    (h : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄, FEnv.Denotes F E → EnvWF E → ∀ a b,
      FEq E (FExpr.op₂ pos (.natLit p a) (.natLit p b)) (FExpr.boolLit bool (f a b))
        (FExpr.bool bool)) :
    BoolOpSpec F p bool pos f where
  natSig := hn.sig
  boolSig := hbool
  opDef := hop
  eq {_ E _ _ _ _} hF hE hη hηBool hηOp _ _ Γ a b := by
    have ⟨ea, eb, et, hda, hdb, hdt, d⟩ := (h hF hE a b).defeq Γ
    obtain rfl := hda.unique (.op₂ hηOp (.natLit hη) (.natLit hη))
      (.op₂ _ (.natLit _ _) (.natLit _ _))
    obtain rfl := hdb.unique (.boolLit hηBool _) (.boolLit _ _)
    obtain rfl := hdt.unique (.boolType hηBool) (.bool _)
    exact d

end Metalean.Checker.Fast
