module

public import Metalean.Syntax.Expr.Functor
public import Metalean.CategoryTheory.Functor.Fold

@[expose] public section

namespace Metalean.Expr

open CategoryTheory MonoidalCategory

attribute [local instance] Level.category

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n m k : Nat}

@[reducible] def appHom : functor ℓ n ⊗ functor ℓ n ⟶ functor ℓ n where
  app _ := ↾fun ⟨e, a⟩ => .app e a
  naturality {_ _} _ := rfl

@[reducible] def appLevelHom :
    (family n).obj ζ ⊗ (family n).obj ζ ⟶ (family n).obj ζ where
  app _ := ↾fun ⟨e, a⟩ => .app e a
  naturality {_ _} _ := rfl

@[reducible] def appSubstHom :
    letI := Subst.category ζ ℓ
    Subst.functor ζ ℓ ⊗ Subst.functor ζ ℓ ⟶ Subst.functor ζ ℓ :=
  letI := Subst.category ζ ℓ
  { app _ := ↾fun ⟨e, a⟩ => .app e a
    naturality {_ _} _ := rfl }

def apps {k} (η : Expr ζ ℓ n) (args : Fin k → Expr ζ ℓ n) : Expr ζ ℓ n :=
  Fin.foldl k (fun η i => .app η (args i)) η

@[simp] theorem apps_zero (η : Expr ζ ℓ n) (args : Fin 0 → Expr ζ ℓ n) :
    η.apps args = η :=
  Fin.foldl_zero ..

theorem apps_eq_self_of_zero (h : k = 0) (η : Expr ζ ℓ n)
    (args : Fin k → Expr ζ ℓ n) :
    η.apps args = η := by
  subst k
  rfl

theorem apps_succ (η : Expr ζ ℓ n) (args : Fin (k + 1) → Expr ζ ℓ n) :
    η.apps args = (η.app (args 0)).apps fun i => args i.succ :=
  Fin.foldl_succ ..

theorem apps_last (η : Expr ζ ℓ n) (args : Fin (k + 1) → Expr ζ ℓ n) :
    η.apps args = (η.apps fun i => args i.castSucc).app (args (Fin.last k)) :=
  Fin.foldl_succ_last ..

@[simp] theorem map_apps (pre : ζ₁ ⟶ ζ₂)
    (η : Expr ζ₁ ℓ n) (args : Fin k → Expr ζ₁ ℓ n) :
    (η.apps args).map pre =
      (η.map pre).apps fun i => (args i).map pre :=
  (appHom.finFold k).naturality_apply pre ⟨η, args⟩ |>.symm

@[simp] theorem instL_apps (levelSubst : Param ℓ → Level ℓ')
    (η : Expr ζ ℓ n) (args : Fin k → Expr ζ ℓ n) :
    (η.apps args).instL levelSubst =
      (η.instL levelSubst).apps fun i => (args i).instL levelSubst :=
  (appLevelHom.finFold k).naturality_apply levelSubst ⟨η, args⟩ |>.symm

def appList (η : Expr ζ ℓ n) (args : List (Expr ζ ℓ n)) : Expr ζ ℓ n :=
  args.foldl .app η

@[simp] theorem map_appList (pre : ζ₁ ⟶ ζ₂)
    (η : Expr ζ₁ ℓ n) (args : List (Expr ζ₁ ℓ n)) :
    (η.appList args).map pre =
      (η.map pre).appList (args.map (Expr.map pre)) :=
  appHom.listFold.naturality_apply pre ⟨η, args⟩ |>.symm

@[simp] theorem instL_appList (levelSubst : Param ℓ → Level ℓ')
    (η : Expr ζ ℓ n) (args : List (Expr ζ ℓ n)) :
    (η.appList args).instL levelSubst =
      (η.instL levelSubst).appList (args.map (Expr.instL levelSubst)) :=
  appLevelHom.listFold.naturality_apply levelSubst ⟨η, args⟩ |>.symm

theorem applyBound_eq_apps (e : Expr ζ ℓ n) (k : Nat) :
    e.applyBound k = (e.wkN k).apps fun i : Fin k => .var (Fin.natAdd n i) := by
  let := Subst.category ζ ℓ
  have hwk {n k : Nat} (e : Expr ζ ℓ n) (args : Fin k → Expr ζ ℓ n) :
      (e.apps args).wk = e.wk.apps fun i => (args i).wk :=
    (subst_vars (Ren.wkFrom n) (e.apps args)).symm.trans
      (((appSubstHom.finFold k).naturality_apply (fun v => .var (Ren.wkFrom n v)) ⟨e, args⟩).symm.trans
        (congrArg₂ apps (subst_vars _ e) (funext fun i => subst_vars _ (args i))))
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [applyBound, ih, hwk, apps_last]
    congr 2
    funext i
    simp [wk, wkFrom, rename, Ren.wkFrom, Fin.natAdd]

end Metalean.Expr
