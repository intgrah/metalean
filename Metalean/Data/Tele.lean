/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

@[expose] public section

universe u v

inductive Tele (T : Nat → Type u) : Nat → Nat → Type u
  | nil {a} : Tele T a a
  | snoc {a b} : Tele T a b → T b → Tele T a (b + 1)

syntax "#t[" term,* "]" : term

macro_rules
  | `(#t[$elements,*]) => do
    let mut result ← `(Tele.nil)
    for element in elements.getElems do
      result ← `(($result).snoc $element)
    pure result

namespace Tele

open CategoryTheory MonoidalCategory

variable {T : Nat → Type u} {S : Nat → Type v}

def map {a b} (f : {d : Nat} → Tele T a d → T d → S d) : Tele T a b → Tele S a b
  | nil => nil
  | snoc Δ A => snoc (map f Δ) (f Δ A)

@[simp] theorem map_nil {a} (f : {d : Nat} → Tele T a d → T d → S d) :
    map f nil = nil :=
  rfl

@[simp] theorem map_snoc {a b} (f : {d : Nat} → Tele T a d → T d → S d)
    (Δ : Tele T a b) (A : T b) : map f (Δ.snoc A) = (map f Δ).snoc (f Δ A) :=
  rfl

def foldr {a b} (f : {d : Nat} → T d → S (d + 1) → S d) (s : S b) : Tele T a b → S a
  | nil => s
  | snoc Δ A => foldr f (f A s) Δ

@[simp] theorem foldr_nil {a} (f : {d : Nat} → T d → S (d + 1) → S d)
    (s : S a) : foldr f s nil = s :=
  rfl

@[simp] theorem foldr_snoc {a b} (f : {d : Nat} → T d → S (d + 1) → S d)
    (s : S (b + 1)) (Δ : Tele T a b) (A : T b) :
    foldr f s (Δ.snoc A) = foldr f (f A s) Δ :=
  rfl

def append {a b c} (Γ : Tele T a b) : Tele T b c → Tele T a c
  | nil => Γ
  | snoc Δ A => snoc (append Γ Δ) A

@[reducible] instance {a b c} : HAppend (Tele T a b) (Tele T b c) (Tele T a c) :=
  ⟨append⟩

@[simp] theorem append_nil {a b} (Γ : Tele T a b) : Γ ++ (nil : Tele T b b) = Γ :=
  rfl

@[simp] theorem append_snoc {a b c} (Γ : Tele T a b) (Δ : Tele T b c) (A : T c) :
    Γ ++ Δ.snoc A = (Γ ++ Δ).snoc A :=
  rfl

theorem foldr_append {a b c} (f : {d : Nat} → T d → S (d + 1) → S d) (s : S c)
    (Γ : Tele T a b) (Δ : Tele T b c) :
    foldr f s (Γ ++ Δ) = foldr f (foldr f s Δ) Γ := by
  induction Δ with
  | nil => rfl
  | snoc Δ A ih => exact ih (f A s)

theorem append_assoc {a b c d} (Γ : Tele T a b)
    (Δ : Tele T b c) (Ε : Tele T c d) :
    Γ ++ Δ ++ Ε = Γ ++ (Δ ++ Ε) := by
  induction Ε with
  | nil => rfl
  | snoc Ε A ih => simp [ih]

@[simp] theorem nil_append {a b} (Δ : Tele T a b) : (nil : Tele T a a) ++ Δ = Δ := by
  induction Δ with
  | nil => rfl
  | snoc Δ A ih => simp [ih]

@[reducible] def category (T : Nat → Type u) : Category.{u} Nat where
  Hom := Tele T
  id _ := .nil
  comp := append
  id_comp := nil_append
  comp_id := append_nil
  assoc := append_assoc

@[reducible] def functor (a b : Nat) : (Nat → Type u) ⥤ Type u where
  obj T := Tele T a b
  map f := ↾map fun {d} _ => f d
  map_id T := by
    ext Δ
    induction Δ with
    | nil => rfl
    | snoc Δ A ih => exact congr(snoc $ih A)
  map_comp f₁ f₂ := by
    ext Δ
    induction Δ with
    | nil => rfl
    | snoc Δ A ih => exact congr(snoc $ih (f₂ _ (f₁ _ A)))

@[reducible] def mapFunctor {T S : Nat → Type u} (f : T ⟶ S) :
    @Functor Nat (category T) Nat (category S) :=
  @CategoryTheory.Functor.mk Nat (category T) Nat (category S) id (fun {_ _} Δ => Δ.map fun _ => f _) (fun _ => rfl) (by
    intro a b c Γ Δ
    induction Δ with
    | nil => rfl
    | snoc Δ A ih => exact congrArg (snoc · (f _ A)) ih)

@[reducible] def foldNatTrans {C : Type v} [Category C] (T S : Nat → C ⥤ Type u)
    (α : ∀ n, T n ⊗ S (n + 1) ⟶ S n) (a b : Nat) :
    (Functor.pi' T ⋙ functor a b) ⊗ S b ⟶ S a where
  app X := ↾fun ⟨Δ, s⟩ => foldr (fun {d} t s => (α d).app X ⟨t, s⟩) s Δ
  naturality {X₁ X₂} f := by
    ext ⟨Δ, s⟩
    induction Δ with
    | nil => rfl
    | snoc Δ t ih =>
      exact (congrArg
        (fun s => foldr
          (fun {d} t s => (α d).app X₂ ⟨t, s⟩) s
          (Δ.map fun {d} _ => (T d).map f))
        ((α _).naturality_apply f ⟨t, s⟩)).trans (ih ((α _).app X₁ ⟨t, s⟩))

theorem le {a b} : Tele T a b → a ≤ b
  | nil => Nat.le_refl a
  | snoc ts _ => Nat.le_trans ts.le (Nat.le_succ _)

theorem heq_nil {a b} (Δ : Tele T a b) (h : b ≤ a) :
    Δ ≍ (nil : Tele T a a) := by
  cases Δ with
  | nil => rfl
  | snoc Δ _ => have := Δ.le; omega

@[elab_as_elim] def addInduction {a}
    {motive : {k : Nat} → Tele T a (a + k) → Sort v}
    (nil : @motive 0 nil)
    (snoc : ∀ k (Δ : Tele T a (a + k)) (A : T (a + k)),
      motive Δ → @motive (k + 1) (Δ.snoc A))
    {k : Nat} (Δ : Tele T a (a + k)) :
    motive Δ := by
  induction k with
  | zero =>
    cases Δ with
    | nil => exact nil
    | snoc Γ _ => exact absurd Γ.le (Nat.not_succ_le_self _)
  | succ k ih =>
    have .snoc Γ A := Δ
    exact snoc k Γ A (ih Γ)

@[elab_as_elim] def suffixInduction {a b} (h : a ≤ b)
    {motive : {k : Nat} → Tele T a (b + k) → Sort v}
    (zero : (Δ : Tele T a b) → @motive 0 Δ)
    (snoc : ∀ k (Δ : Tele T a (b + k)) (A : T (b + k)),
      motive Δ → @motive (k + 1) (Δ.snoc A))
    {k} (Δ : Tele T a (b + k)) :
    motive Δ := by
  induction k with
  | zero => exact zero Δ
  | succ k ih =>
    cases Δ with
    | nil => omega
    | snoc Γ A => exact snoc k Γ A (ih Γ)

def split {a b} (h : a ≤ b) : (k : Nat) → Tele T a (b + k) → Tele T a b × Tele T b (b + k)
  | 0, Γ => ⟨Γ, .nil⟩
  | k + 1, Δ => by
    cases Δ with
    | nil => omega
    | snoc Δ t => exact (split h k Δ).map id (snoc · t)

theorem split_append {a b} (h : a ≤ b) (Γ : Tele T a b) {k} (Δ : Tele T b (b + k)) :
    split h k (Γ ++ Δ) = (Γ, Δ) := by
  induction Δ using addInduction with
  | nil => rfl
  | snoc k Δ t ih => exact congrArg (Prod.map id (snoc · t)) ih

theorem append_split {a b} (h : a ≤ b) {k} (Δ : Tele T a (b + k)) :
    Function.uncurry append (split h k Δ) = Δ := by
  induction Δ using suffixInduction h with
  | zero Δ => rfl
  | snoc k Δ t ih => exact congrArg (snoc · t) ih

@[reducible] def appendIso {a b} (h : a ≤ b) (k : Nat) :
    Tele T a b × Tele T b (b + k) ≅ Tele T a (b + k) where
  hom := ↾Function.uncurry append
  inv := ↾split h k
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun ⟨Γ, Δ⟩ => split_append h Γ Δ
  inv_hom_id := ConcreteCategory.hom_ext _ _ (append_split h)

variable {a} (P : {b : Nat} → Tele T a b → T b → Prop) in
inductive Forall : {b : Nat} → Tele T a b → Prop
  | nil : Forall nil
  | snoc {b} {Δ : Tele T a b} {A : T b} : Forall Δ → P Δ A → Forall (snoc Δ A)

namespace Forall

variable {a b : Nat} {P : {b : Nat} → Tele T a b → T b → Prop}
  {Δ : Tele T a b} {A : T b}

theorem init (h : Forall P (Δ.snoc A)) : Forall P Δ := by
  cases h with
  | snoc h _ => exact h

theorem last (h : Forall P (Δ.snoc A)) : P Δ A := by
  cases h with
  | snoc _ h => exact h

end Forall

variable {a} (R : {b : Nat} → Tele T a b → Tele S a b → T b → S b → Prop) in
inductive Forall₂ : {b : Nat} → Tele T a b → Tele S a b → Prop
  | nil : Forall₂ nil nil
  | snoc {b} {Δ : Tele T a b} {Θ : Tele S a b} {A : T b} {B : S b} :
    Forall₂ Δ Θ → R Δ Θ A B → Forall₂ (snoc Δ A) (snoc Θ B)

end Tele
