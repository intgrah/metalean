/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
public import Metalean.TypeTheory.NaturalModel.False

@[expose] public noncomputable section

namespace Metalean.TypeTheory

open CategoryTheory Opposite NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  {ℓ : Nat} [HasSorts Ty Tm ℓ] [HasPi Ty Tm] {ζ : Sigs} {X Z : C}

abbrev Value (Ty Tm : Cᵒᵖ ⥤ Type u) [NaturalModel Ty Tm] (X : C) : Type u :=
  Σ A : yoneda.obj X ⟶ Ty, Sect A

def Value.subst (σ : Z ⟶ X) (V : Value Ty Tm X) : Value Ty Tm Z :=
  ⟨y σ ≫ V.1, Sect.pullbackAlong σ V.2⟩

def generic (A : y X ⟶ Ty) : Value Ty Tm (ext A) :=
  ⟨y (disp A) ≫ A, Sect.ofTerm _ (genericTerm A) (genericTerm_typing A)⟩

def extend (Ty Tm : Cᵒᵖ ⥤ Type u) [NaturalModel Ty Tm] {n : Nat} {X : C}
    (ρ : Var n → Value Ty Tm X) (A : y X ⟶ Ty) :
    Var (n + 1) → Value Ty Tm (ext A) :=
  Fin.snoc (fun v => (ρ v).subst (disp A)) (generic A)

mutual

inductive Denotes : {n : Nat} → {X : C} →
    (Var n → Value Ty Tm X) → Expr ζ ℓ n → Value Ty Tm X → Prop where
  | var {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} (v : Var n) :
    Denotes ρ (.var v) (ρ v)
  | sort {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {l : Level ℓ} {t : Tm.obj (op X)}
    {ht : ℳ.typing.app (op X) t = yonedaEquiv (HasSorts.sort l.succ X)} :
    HasSorts.el l.succ t ht = HasSorts.sort l X →
    Denotes ρ (.sort l) ⟨HasSorts.sort l.succ X, Sect.ofTerm _ t ht⟩
  | forallE {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {e : Expr ζ ℓ n}
    {e' : Expr ζ ℓ (n + 1)} {v₁ v₂ : Level ℓ} {A : y X ⟶ Ty} {B : y (ext A) ⟶ Ty}
    {t : Tm.obj (op X)}
    {ht : ℳ.typing.app (op X) t = yonedaEquiv (HasSorts.sort (v₁.imax v₂) X)} :
    DenotesTy ρ e v₁ A →
    DenotesTy (extend Ty Tm ρ A) e' v₂ B →
    HasSorts.el (v₁.imax v₂) t ht = piCode A B →
    Denotes ρ (.forallE e e') ⟨HasSorts.sort (v₁.imax v₂) X, Sect.ofTerm _ t ht⟩
  | lam {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {e : Expr ζ ℓ n} {e' : Expr ζ ℓ (n + 1)}
    {v : Level ℓ} {A : y X ⟶ Ty} {B : y (ext A) ⟶ Ty} {b : Sect B} :
    DenotesTy ρ e v A →
    Denotes (extend Ty Tm ρ A) e' ⟨B, b⟩ →
    Denotes ρ (.lam e e') ⟨piCode A B, lamSect A B b⟩
  | app {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {e₁ e₂ : Expr ζ ℓ n}
    {A : y X ⟶ Ty} {B : y (ext A) ⟶ Ty} {f : Sect (piCode A B)} {a : Sect A} :
    Denotes ρ e₁ ⟨piCode A B, f⟩ →
    Denotes ρ e₂ ⟨A, a⟩ →
    Denotes ρ (.app e₁ e₂)
      ⟨y a.hom ≫ B, Sect.pullbackAlong a.hom
        (Sect.ofTerm B (appTerm A B f.term f.term_typing)
          (appTerm_typing A B f.term f.term_typing))⟩
  | letE {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {e₁ e₂ : Expr ζ ℓ n}
    {e' : Expr ζ ℓ (n + 1)} {v : Level ℓ} {A : y X ⟶ Ty} {a : Sect A} {W : Value Ty Tm X} :
    DenotesTy ρ e₁ v A →
    Denotes ρ e₂ ⟨A, a⟩ →
    Denotes (Fin.snoc ρ ⟨A, a⟩) e' W →
    Denotes ρ (.letE e₁ e₂ e') W

inductive DenotesTy : {n : Nat} → {X : C} →
    (Var n → Value Ty Tm X) → Expr ζ ℓ n → Level ℓ → (y X ⟶ Ty) → Prop where
  | intro {n : Nat} {X : C} {ρ : Var n → Value Ty Tm X} {e : Expr ζ ℓ n} {v : Level ℓ}
    {t : Tm.obj (op X)} {ht : ℳ.typing.app (op X) t = yonedaEquiv (HasSorts.sort v X)} :
    Denotes ρ e ⟨HasSorts.sort v X, Sect.ofTerm _ t ht⟩ →
    DenotesTy ρ e v (HasSorts.el v t ht)

end

def Agrees (Ty Tm : Cᵒᵖ ⥤ Type u) [NaturalModel Ty Tm] [HasSorts Ty Tm ℓ] [HasPi Ty Tm]
    {n : Nat} {X : C} (ρ : Var n → Value Ty Tm X) (Γ : Ctx ζ ℓ 0 n) : Prop :=
  ∀ v : Var n, ∃ u : Level ℓ, DenotesTy ρ (Γ.get v) u (ρ v).1

def Valid (Ty Tm : Cᵒᵖ ⥤ Type u) [NaturalModel Ty Tm] [HasSorts Ty Tm ℓ] [HasPi Ty Tm]
    {n : Nat} (Γ : Ctx ζ ℓ 0 n) (e₁ e₂ t : Expr ζ ℓ n) : Prop :=
  ∀ {X : C} (ρ : Var n → Value Ty Tm X),
  Agrees Ty Tm ρ Γ →
  ∃ (u : Level ℓ) (A : y X ⟶ Ty) (a : Sect A),
    DenotesTy ρ t u A ∧ Denotes ρ e₁ ⟨A, a⟩ ∧ Denotes ρ e₂ ⟨A, a⟩

theorem soundness {E : Env ζ} {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    Valid Ty Tm Γ e₁ e₂ t :=
  sorry

theorem denotesTy_falseTy {X : C} {u : Level ℓ} {A : yoneda.obj X ⟶ Ty}
    (hsort : ∀ {Z : C}, (X ⟶ Z) → ∀ {v₁ v₂ : Level ℓ},
      HasSorts.sort (Ty := Ty) v₁ Z = HasSorts.sort v₂ Z → v₁ = v₂) :
    DenotesTy (Fin.elim0 : Var 0 → Value Ty Tm X) (Expr.falseTy : Expr ζ ℓ 0) u A →
    A = falseType Ty ℓ X :=
  sorry

theorem con {E : Env ζ} {X : C} [HasSorts Ty Tm 0]
    (hsort : ∀ {Z : C}, (X ⟶ Z) → ∀ {v₁ v₂ : Level 0},
      HasSorts.sort (Ty := Ty) v₁ Z = HasSorts.sort v₂ Z → v₁ = v₂)
    (hempty : IsEmpty (Sect (falseType Ty 0 X))) :
    E.Con := by
  intro hall
  have ⟨e, he⟩ := hall Expr.falseTy (Expr.falseTy_isType E)
  have ⟨u, A, a, hA, hden, _⟩ :=
    soundness (Ty := Ty) he (X := X) Fin.elim0 fun v => v.elim0
  exact hempty.elim (Sect.convert (denotesTy_falseTy hsort hA) a)

end Metalean.TypeTheory
