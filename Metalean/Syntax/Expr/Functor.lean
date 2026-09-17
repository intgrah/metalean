module

public import Metalean.Syntax.Expr
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

@[expose] public section

namespace Metalean

open CategoryTheory MonoidalCategory

namespace Subst

variable {ζ : Sigs} {ℓ : Nat}

@[reducible] def category (ζ : Sigs) (ℓ : Nat) : SmallCategory Nat where
  Hom := Subst ζ ℓ
  id _ := Subst.id
  comp := Subst.comp
  id_comp _ := rfl
  comp_id σ := funext fun v => Expr.subst_id (σ v)
  assoc σ₁ σ₂ σ₃ := funext fun v => Expr.subst_subst σ₂ σ₃ (σ₁ v)

attribute [local instance] Ren.category in
@[reducible] def kleisli (ζ : Sigs) (ℓ : Nat) : @Functor Nat (category ζ ℓ) (Expr.relativeMonad ζ ℓ).Kleisli _ :=
  letI := category ζ ℓ
  { obj n := letI := Ren.category; ⟨n⟩
    map σ := letI := Ren.category; ⟨↾σ⟩ }

abbrev functor (ζ : Sigs) (ℓ : Nat) : @Functor Nat (category ζ ℓ) Type _ :=
  letI := category ζ ℓ
  kleisli ζ ℓ ⋙ @RelativeMonad.extension _ _ Ren.category _ _ (Expr.relativeMonad ζ ℓ)

@[reducible] def shift (k : Nat) : @Functor Nat (category ζ ℓ) Nat (category ζ ℓ) :=
  letI := category ζ ℓ
  { obj n := n + k
    map σ := σ.liftN k
    map_id _ := liftN_id k
    map_comp σ₁ σ₂ := (liftN_comp σ₁ σ₂ k).symm }

@[reducible] def wkNNatTrans (k : Nat) :
    letI := category ζ ℓ
    functor ζ ℓ ⟶ shift k ⋙ functor ζ ℓ :=
  letI := category ζ ℓ
  { app _ := ↾fun e => e.wkN k
    naturality _ _ σ := by
      ext e
      induction k with
      | zero => rfl
      | succ k ih => exact (congrArg Expr.wk ih).trans (Expr.wk_subst_lift _ _).symm }

end Subst

namespace Expr

variable {ζ : Sigs} {ℓ : Nat}

attribute [local instance] Level.category in
abbrev family (n : Nat) : Sigs ⥤ @Functor Nat Level.category Type _ :=
  trifunctor ⋙ (Functor.whiskeringRight _ _ _).obj letI := Ren.category; (evaluation Nat Type).obj n

attribute [local instance] Level.category in
@[reducible] def forallHom (n : Nat) : family n ⊗ family (n + 1) ⟶ family n where
  app _ := { app _ := ↾fun ⟨t, e⟩ => .forallE t e, naturality _ _ _ := rfl }
  naturality {_ _} _ := rfl

attribute [local instance] Level.category in
@[reducible] def lamHom (n : Nat) : family n ⊗ family (n + 1) ⟶ family n where
  app _ := { app _ := ↾fun ⟨t, e⟩ => .lam t e, naturality _ _ _ := rfl }
  naturality _ _ _ := rfl

@[reducible] def forallSubstHom :
    letI := Subst.category ζ ℓ
    Subst.functor ζ ℓ ⊗ (Subst.shift 1 ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ :=
  letI := Subst.category ζ ℓ
  { app _ := ↾fun ⟨t, e⟩ => .forallE t e
    naturality {_ _} _ := rfl }

@[reducible] def lamSubstHom :
    letI := Subst.category ζ ℓ
    Subst.functor ζ ℓ ⊗ (Subst.shift 1 ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ :=
  letI := Subst.category ζ ℓ
  { app _ := ↾fun ⟨t, e⟩ => .lam t e
    naturality {_ _} _ := rfl }

end Expr

end Metalean
