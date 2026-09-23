/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Sig
public import Metalean.Syntax.Ren
public import Metalean.Level.Quot.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Pi.Basic
public import Metalean.CategoryTheory.RelativeMonad
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n m p a b k nsorts : Nat} {ι : IndSig}

/--
Core expressions.

Some notes:
- `ζ : Sigs` is the skeletal shape of the environment, which says in
  what ways one can legally index in to the environment. This means
  that lookups are completely total operations.
- `ℓ : Nat` is the maximum universe level, which means that universe
  variables are well-scoped.
- `n : Nat` is the size of the local context, which means that bound
  variables are well-scoped.

Expressions are functorial in `ζ`, `ℓ`, and `n`. These represent
- `ζ`: weakening along environment. `Sigs` forms a category whose
  morphisms are environment extensions.
- `ℓ`: universe instantiation. The category instance has objects
  Natural numbers, and morphisms as well-scoped universe substitutions.
- `n`: renaming via a well-scoped renaming operation.

We automatically derive `CategoryTheory.Functor` definitions.

We take inductive/quotient type formers, constructors, and eliminators to
be primitive term formers. This means that they carry their subterms,
instead of having to use an `app` node. This means that, when parsing
the input, we have to saturate partially applied constants with lambdas.
As a result, this subtly supporting function η in more cases.

Projections (.1, .2, etc.) are not included, since they are definitionally
equal to eliminators of structures.
-/
@[derive_functor ζ,
  derive_functor ℓ instL levelFunctor via Level.category,
  derive_functor n rename renFunctor via Ren.category]
inductive Expr (ζ : Sigs) (ℓ : Nat) : (n : Nat) → Type
  /-- De Bruijn index -/
  | var {n : Nat} (x : Var n) : Expr ζ ℓ n
  /-- Sort u -/
  | sort {n : Nat} (l : Level ℓ) : Expr ζ ℓ n
  /-- def, opaque, axiom -/
  | const {n : Nat} {kind : ConstKind} {nlevels : Nat}
      (η : Head ζ (.const kind nlevels))
      (ls : Fin nlevels → Level ℓ) : Expr ζ ℓ n
  /-- Inductive type former -/
  | ind {n : Nat} {ι : IndSig}
      (η : Head ζ (.inductive ι))
      (s : Fin ι.nsorts)
      (ls : Fin ι.nlevels → Level ℓ)
      (ps : Fin ι.nparams → Expr ζ ℓ n)
      (is : Fin (ι.nindices s) → Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Inductive type constructor -/
  | ctor {n : Nat} {ι : IndSig}
      (η : Head ζ (.inductive ι))
      (s : Fin ι.nsorts)
      (c : Fin (ι.nctors s))
      (ls : Fin ι.nlevels → Level ℓ)
      (ps : Fin ι.nparams → Expr ζ ℓ n)
      (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
      (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Inductive type eliminator -/
  | recr {n : Nat} {ι : IndSig}
      (η : Head ζ (.inductive ι))
      (s : Fin ι.nsorts)
      (ls : Fin ι.nlevels → Level ℓ)
      (l : Level ℓ)
      (ps : Fin ι.nparams → Expr ζ ℓ n)
      (ms : Fin ι.nsorts → Expr ζ ℓ n)
      (mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
        Expr ζ ℓ n)
      (is : Fin (ι.nindices s) → Expr ζ ℓ n)
      (maj : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Quotient type former -/
  | quot {n : Nat} (η : Head ζ .quot) (l : Level ℓ)
      (α r : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Quotient type constructor -/
  | quotMk {n : Nat} (η : Head ζ .quot) (l : Level ℓ)
      (α r a : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Quotient type lift -/
  | quotLift {n : Nat} (η : Head ζ .quot) (l₁ l₂ : Level ℓ)
      (α r β f h a : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Quotient type induction -/
  | quotInd {n : Nat} (η : Head ζ .quot) (l : Level ℓ)
      (α r β f a : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Function type eliminator -/
  | app {n : Nat} (e₁ e₂ : Expr ζ ℓ n) : Expr ζ ℓ n
  /-- Function type constructor -/
  | lam {n : Nat} (e : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) : Expr ζ ℓ n
  /-- Function type former -/
  | forallE {n : Nat} (e : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) : Expr ζ ℓ n
  /-- Local definition -/
  | letE {n : Nat} (e₁ e₂ : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) : Expr ζ ℓ n

syntax:max "#" num : term

macro_rules | `(#$i:num) => `(Expr.var ⟨$i, by decide⟩)

namespace Expr

abbrev prop : Expr ζ ℓ n := .sort .zero

/-- `∀ P : Prop, P` -/
def falseTy : Expr ζ ℓ 0 := .forallE .prop (.var (Fin.last 0))

-- TODO
-- abbrev Expr.type (l : Level ℓ) : Expr ζ ℓ n := .type (.succ l)

instance : Inhabited (Expr ζ ℓ n) := ⟨.prop⟩

attribute [local instance] Ren.category in
@[simp] theorem rename_id (e : Expr ζ ℓ n) : e.rename Ren.id = e :=
  (renFunctor ζ ℓ).map_id_apply n e

attribute [local instance] Ren.category in
@[simp] theorem rename_rename (ρ₂ : Ren n k) (ρ₁ : Ren m n) (e : Expr ζ ℓ m) :
    (e.rename ρ₁).rename ρ₂ = e.rename (ρ₂.comp ρ₁) :=
  ((renFunctor ζ ℓ).map_comp_apply ρ₁ ρ₂ e).symm

def wkFrom (cut : Nat) (e : Expr ζ ℓ n) : Expr ζ ℓ (n + 1) :=
  e.rename (Ren.wkFrom cut)

def wk (e : Expr ζ ℓ n) : Expr ζ ℓ (n + 1) := e.wkFrom n

def wkN (e : Expr ζ ℓ n) : (k : Nat) → Expr ζ ℓ (n + k)
  | 0 => e
  | k + 1 => (e.wkN k).wk

theorem wkN_eq_rename (e : Expr ζ ℓ n) (k : Nat) :
    e.wkN k = e.rename (Ren.wkN k) := by
  induction k with
  | zero =>
      change e = e.rename Ren.id
      rw [rename_id]
  | succ k ih =>
      rw [wkN, ih, wk, wkFrom, rename_rename]
      congr 1
      funext v
      ext
      simp [Ren.comp, Ren.wkN, Ren.wkFrom, show v.val < n + k by omega]

theorem wkN_ind (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) (k : Nat) :
    (Expr.ind η s ls ps is).wkN k =
      Expr.ind η s ls (fun i => (ps i).wkN k)
        fun i => (is i).wkN k := by
  simp only [wkN_eq_rename, rename]

@[simp] theorem var_wkN (i : Fin n) (count : Nat) :
    (Expr.var i : Expr ζ ℓ n).wkN count =
      Expr.var (i.castAdd count) := by
  rw [wkN_eq_rename]
  rfl

theorem vars_wkN (count : Nat) :
    (fun i : Fin n => (Expr.var i : Expr ζ ℓ n).wkN count) =
      fun i => Expr.var (i.castLE (Nat.le_add_right _ _)) :=
  funext fun i => var_wkN i count

def wkClosed (e : Expr ζ ℓ 0) : {n : Nat} → Expr ζ ℓ n
  | 0 => e
  | _ + 1 => e.wkClosed.wk

@[simp] theorem wkClosed_sort (l : Level ℓ) :
    (.sort l : Expr ζ ℓ 0).wkClosed (n := n) = .sort l := by
  induction n <;> simp_all! [wk, wkFrom]

@[simp] theorem map_rename (pre : ζ₁ ⟶ ζ₂) (ρ : Ren m n)
    (e : Expr ζ₁ ℓ m) :
    (e.rename ρ).map pre = (e.map pre).rename ρ := by
  induction e generalizing n <;> simp [rename, map, *]

@[simp] theorem map_wkFrom (pre : ζ₁ ⟶ ζ₂) (cut : Nat)
    (e : Expr ζ₁ ℓ n) :
    (e.wkFrom cut).map pre = (e.map pre).wkFrom cut :=
  map_rename pre (Ren.wkFrom cut) e

@[simp] theorem map_wk (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n) :
    e.wk.map pre = (e.map pre).wk :=
  map_wkFrom pre n e

@[simp] theorem map_wkN (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n)
    (k : Nat) : (e.wkN k).map pre = (e.map pre).wkN k := by
  induction k <;> simp_all!

@[simp] theorem map_wkClosed (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ 0) :
    {n : Nat} → e.wkClosed (n := n).map pre =
      (e.map pre).wkClosed (n := n)
  | 0 => rfl
  | n + 1 => by rw [wkClosed, map_wk, map_wkClosed pre e, wkClosed]

instance : InstLevel (Param ℓ → Level ℓ') (Expr ζ ℓ n) (Expr ζ ℓ' n) where
  inst ls e := e.instL ls

@[simp] theorem inst_var (ls : Param ℓ → Level ℓ') (v : Var n) :
    (var v : Expr ζ ℓ n){ls} = .var v := rfl

@[simp] theorem inst_sort (ls : Param ℓ → Level ℓ') (l : Level ℓ) :
    (sort l : Expr ζ ℓ n){ls} = .sort l{ls} := rfl

@[simp] theorem inst_const {kind : ConstKind} {nlevels : Nat}
    (ls : Param ℓ → Level ℓ')
    (η : Head ζ (.const kind nlevels)) (us : Fin nlevels → Level ℓ) :
    (const η us : Expr ζ ℓ n){ls} = .const η us{ls} := rfl

@[simp] theorem inst_ind (ls : Param ℓ → Level ℓ')
    (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (us : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    (ind η s us ps is){ls} = .ind η s us{ls} ps{ls} is{ls} := rfl

@[simp] theorem inst_ctor (ls : Param ℓ → Level ℓ')
    (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (us : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n) :
    (ctor η s c us ps fds recFds){ls} =
      .ctor η s c us{ls} ps{ls} fds{ls} recFds{ls} := rfl

@[simp] theorem inst_recr (ls : Param ℓ → Level ℓ')
    (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (us : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) (maj : Expr ζ ℓ n) :
    (recr η s us l ps ms mins is maj){ls} =
      .recr η s us{ls} l{ls} ps{ls} ms{ls}
        (fun s c => (mins s c){ls}) is{ls} maj{ls} := rfl

@[simp] theorem inst_quot (ls : Param ℓ → Level ℓ')
    (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n) :
    (quot η l α r){ls} = .quot η l{ls} α{ls} r{ls} := rfl

@[simp] theorem inst_quotMk (ls : Param ℓ → Level ℓ')
    (η : Head ζ .quot) (l : Level ℓ) (α r a : Expr ζ ℓ n) :
    (quotMk η l α r a){ls} = .quotMk η l{ls} α{ls} r{ls} a{ls} := rfl

@[simp] theorem inst_quotLift (ls : Param ℓ → Level ℓ')
    (η : Head ζ .quot) (l₁ l₂ : Level ℓ)
    (α r β f h a : Expr ζ ℓ n) :
    (quotLift η l₁ l₂ α r β f h a){ls} =
      .quotLift η l₁{ls} l₂{ls} α{ls} r{ls} β{ls} f{ls} h{ls} a{ls} := rfl

@[simp] theorem inst_quotInd (ls : Param ℓ → Level ℓ')
    (η : Head ζ .quot) (l : Level ℓ)
    (α r β f a : Expr ζ ℓ n) :
    (quotInd η l α r β f a){ls} =
      .quotInd η l{ls} α{ls} r{ls} β{ls} f{ls} a{ls} := rfl

@[simp] theorem instL_app (ls : Param ℓ → Level ℓ') (e₁ e₂ : Expr ζ ℓ n) :
    (e₁.app e₂){ls} = .app e₁{ls} e₂{ls} := rfl

@[simp] theorem inst_lam (ls : Param ℓ → Level ℓ')
    (e : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) :
    (e.lam e'){ls} = .lam e{ls} e'{ls} := rfl

@[simp] theorem inst_forallE (ls : Param ℓ → Level ℓ')
    (e : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) :
    (e.forallE e'){ls} = .forallE e{ls} e'{ls} := rfl

@[simp] theorem inst_letE (ls : Param ℓ → Level ℓ')
    (e₁ e₂ : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) :
    (e₁.letE e₂ e'){ls} = .letE e₁{ls} e₂{ls} e'{ls} := rfl

@[simp] theorem map_instL (pre : ζ₁ ⟶ ζ₂)
    (ls : Param ℓ → Level ℓ') (e : Expr ζ₁ ℓ n) :
    e{ls}.map pre = (e.map pre){ls} := by
  induction e <;> simp [map, funext_iff, *]

end Expr

abbrev Subst (ζ : Sigs) (ℓ m n : Nat) : Type := Var m → Expr ζ ℓ n

namespace Subst

def id : Subst ζ ℓ n n := .var

def lift (σ : Subst ζ ℓ m n) : Subst ζ ℓ (m + 1) (n + 1) := fun v =>
  if h : v.val < m then (σ ⟨v.val, h⟩).wk else .var (Fin.last n)

@[simp] theorem lift_castSucc (σ : Subst ζ ℓ m n) (v : Var m) :
    σ.lift v.castSucc = (σ v).wk := by
  simp [lift]

@[simp] theorem lift_last (σ : Subst ζ ℓ m n) :
    σ.lift (Fin.last m) = .var (Fin.last n) := by
  simp [lift]

def extend (σ : Subst ζ ℓ m n) (value : Expr ζ ℓ n) : Subst ζ ℓ (m + 1) n :=
  Fin.snoc σ value

@[simp] theorem extend_castSucc (σ : Subst ζ ℓ m n) (value : Expr ζ ℓ n)
    (v : Var m) :
    σ.extend value v.castSucc = σ v := by
  simp [extend]

@[simp] theorem extend_last (σ : Subst ζ ℓ m n) (value : Expr ζ ℓ n) :
    σ.extend value (Fin.last m) = value := by
  simp [extend]

def liftN (σ : Subst ζ ℓ m n) : (k : Nat) → Subst ζ ℓ (m + k) (n + k)
  | 0 => σ
  | k + 1 => (σ.liftN k).lift

@[simp] theorem liftN_last (σ : Subst ζ ℓ m n) (k : Nat) :
    σ.liftN (k + 1) (Fin.last (m + k)) = .var (Fin.last (n + k)) := by
  rw [liftN, lift_last]

def map (pre : ζ₁ ⟶ ζ₂) (σ : Subst ζ₁ ℓ m n) :
    Subst ζ₂ ℓ m n := fun v => (σ v).map pre

@[simp] theorem map_append {a b : Nat} (pre : ζ₁ ⟶ ζ₂)
    (σ₁ : Subst ζ₁ ℓ a n) (σ₂ : Subst ζ₁ ℓ b n) :
    map pre (Fin.append σ₁ σ₂) =
      Fin.append (fun i => (σ₁ i).map pre) fun i => (σ₂ i).map pre :=
  Fin.append_comp σ₁ σ₂ (Expr.map pre)

@[simp] theorem map_apply {m n : Nat} (pre : ζ₁ ⟶ ζ₂) (σ : Subst ζ₁ ℓ m n)
    (v : Var m) : σ.map pre v = (σ v).map pre := rfl

def rename (ρ : Ren n k) (σ : Subst ζ ℓ m n) : Subst ζ ℓ m k :=
  fun v => (σ v).rename ρ

def precomp (σ : Subst ζ ℓ n k) (ρ : Ren m n) : Subst ζ ℓ m k :=
  fun v => σ (ρ v)

@[simp] theorem rename_lift (ρ : Ren n k) (σ : Subst ζ ℓ m n) :
    rename ρ.lift σ.lift = (rename ρ σ).lift := by
  funext v
  by_cases h : v.val < m
  · simp [rename, lift, h, Expr.wk, Expr.wkFrom]
  · obtain rfl : v = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    simp [rename, lift, Expr.rename]

@[simp] theorem lift_vars (ρ : Ren m n) :
    Subst.lift (fun v => Expr.var (ρ v) : Subst ζ ℓ m n) =
      fun v => Expr.var (ρ.lift v) := by
  funext v
  by_cases h : v.val < m
  · have hr := (ρ ⟨v.val, h⟩).isLt
    simp [Subst.lift, Ren.lift, Ren.wkFrom, h, hr,
      Expr.wk, Expr.wkFrom, Expr.rename]
  · obtain rfl : v = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    simp [Subst.lift, Ren.lift]

@[simp] theorem liftN_vars (ρ : Ren m n) (count : Nat) :
    Subst.liftN (fun v => Expr.var (ρ v) : Subst ζ ℓ m n) count =
      fun v => Expr.var (ρ.liftN count v) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Subst.liftN, Ren.liftN, ih, Subst.lift_vars]
      rfl

@[simp] theorem precomp_lift (σ : Subst ζ ℓ n k) (ρ : Ren m n) :
    precomp σ.lift ρ.lift = (precomp σ ρ).lift := by
  funext v
  by_cases h : v.val < m
  · have hr := (ρ ⟨v.val, h⟩).isLt
    simp [precomp, lift, Ren.lift, h, hr]
  · obtain rfl : v = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    simp [precomp, lift, Ren.lift]

@[simp] theorem map_lift (pre : ζ₁ ⟶ ζ₂) (σ : Subst ζ₁ ℓ m n) :
    σ.lift.map pre = (σ.map pre).lift := by
  funext v
  simp [map, lift]
  split
  · rw [Expr.map_wk]
  · rfl

@[simp] theorem map_liftN (pre : ζ₁ ⟶ ζ₂) (σ : Subst ζ₁ ℓ m n)
    (k : Nat) : (σ.liftN k).map pre = (σ.map pre).liftN k := by
  induction k <;> simp_all!

@[simp] theorem map_id (pre : ζ₁ ⟶ ζ₂) :
    (id : Subst ζ₁ ℓ n n).map pre = id := by
  funext v
  rfl

@[simp] theorem map_extend (pre : ζ₁ ⟶ ζ₂) (σ : Subst ζ₁ ℓ m n)
    (e : Expr ζ₁ ℓ n) :
    (σ.extend e).map pre =
      (σ.map pre).extend (e.map pre) :=
  Fin.comp_snoc (Expr.map pre) σ e

@[simp] theorem lift_id :
    Subst.id (ζ := ζ) (ℓ := ℓ) (n := n).lift = Subst.id := by
  funext v
  by_cases h : v.val < n
  · simp [Subst.lift, Subst.id, h, Expr.wk, Expr.wkFrom, Expr.rename,
      Ren.wkFrom]
  · have hv : v = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    rw [hv]
    simp [Subst.lift, Subst.id]

@[simp] theorem liftN_id (k : Nat) :
    Subst.id (ζ := ζ) (ℓ := ℓ) (n := n).liftN k = Subst.id := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Subst.liftN, ih, Subst.lift_id]

end Subst

namespace CtorSig

def liftFieldSubst (csig : CtorSig nsorts) (σ : Subst ζ ℓ m n) :
    Subst ζ ℓ (m + csig.nfields + csig.nrecFields)
      (n + csig.nfields + csig.nrecFields) :=
  (σ.liftN csig.nfields).liftN csig.nrecFields

def liftCaseSubst (csig : CtorSig nsorts) (σ : Subst ζ ℓ m n) :
    Subst ζ ℓ (m + csig.nfields + csig.nrecFields + csig.nrecFields)
      (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
  ((σ.liftN csig.nfields).liftN csig.nrecFields).liftN csig.nrecFields

def caseSubst (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n) :
    Subst ζ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields) n :=
  Fin.append (Fin.append (Fin.append (Subst.id : Subst ζ ℓ n n) fds) recFds) ihs

@[simp] theorem caseSubst_ordinary (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n)
    (f : Fin csig.nfields) :
    csig.caseSubst fds recFds ihs
        (((f.natAdd n).castAdd csig.nrecFields).castAdd csig.nrecFields) =
      fds f := by
  simp [caseSubst]

@[simp] theorem caseSubst_recursive (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n)
    (f : Fin csig.nrecFields) :
    csig.caseSubst fds recFds ihs
        ((f.natAdd (n + csig.nfields)).castAdd csig.nrecFields) =
      recFds f := by
  simp [caseSubst]

end CtorSig

namespace Expr

def subst {n m : Nat} (σ : Subst ζ ℓ m n) : Expr ζ ℓ m → Expr ζ ℓ n
  | .var v => σ v
  | .sort u => .sort u
  | .const η ls => .const η ls
  | .ind η s ls ps is =>
    .ind η s ls (fun i => (ps i).subst σ) fun i => (is i).subst σ
  | .ctor η s c ls ps fds recFds =>
    .ctor η s c ls (fun i => (ps i).subst σ)
      (fun i => (fds i).subst σ) fun i => (recFds i).subst σ
  | .recr η s ls u ps ms mins is maj =>
    .recr η s ls u
      (fun i => (ps i).subst σ)
      (fun s => (ms s).subst σ)
      (fun s c => (mins s c).subst σ)
      (fun i => (is i).subst σ)
      (maj.subst σ)
  | .quot η l α r => .quot η l (α.subst σ) (r.subst σ)
  | .quotMk η l α r a =>
    .quotMk η l (α.subst σ) (r.subst σ) (a.subst σ)
  | .quotLift η l₁ l₂ α r β f h a =>
    .quotLift η l₁ l₂ (α.subst σ) (r.subst σ) (β.subst σ)
      (f.subst σ) (h.subst σ) (a.subst σ)
  | .quotInd η l α r β f a =>
    .quotInd η l (α.subst σ) (r.subst σ) (β.subst σ)
      (f.subst σ) (a.subst σ)
  | .app e₁ e₂ => .app (e₁.subst σ) (e₂.subst σ)
  | .lam dom body => .lam (dom.subst σ) (body.subst σ.lift)
  | .forallE dom cod => .forallE (dom.subst σ) (cod.subst σ.lift)
  | .letE type value body =>
      .letE (type.subst σ) (value.subst σ) (body.subst σ.lift)

@[simp] theorem subst_id (e : Expr ζ ℓ n) : e.subst Subst.id = e := by
  induction e with
  | var => rfl
  | _ => simp [Expr.subst, *]

@[simp] theorem subst_vars (ρ : Ren m n) (e : Expr ζ ℓ m) :
    e.subst (fun v => .var (ρ v)) = e.rename ρ := by
  induction e generalizing n <;> simp [Expr.subst, Expr.rename, *]

@[simp] theorem subst_rename (ρ : Ren n k) (σ : Subst ζ ℓ m n)
    (e : Expr ζ ℓ m) :
    (e.subst σ).rename ρ = e.subst (σ.rename ρ) := by
  induction e generalizing n k <;>
    simp [subst, rename, Subst.rename, *]

@[simp] theorem rename_subst (σ : Subst ζ ℓ n k) (ρ : Ren m n)
    (e : Expr ζ ℓ m) :
    (e.rename ρ).subst σ = e.subst (σ.precomp ρ) := by
  induction e generalizing n k <;>
    simp [subst, rename, Subst.precomp, *]

@[simp] theorem map_subst (pre : ζ₁ ⟶ ζ₂)
    (σ : Subst ζ₁ ℓ m n) (e : Expr ζ₁ ℓ m) :
    (e.subst σ).map pre =
      (e.map pre).subst (σ.map pre) := by
  induction e generalizing n <;>
    simp [subst, map, Subst.map, *]

def inst (e' : Expr ζ ℓ (n + 1)) (value : Expr ζ ℓ n) : Expr ζ ℓ n :=
  e'.subst (Subst.id.extend value)

@[simp] theorem map_inst (pre : ζ₁ ⟶ ζ₂)
    (e' : Expr ζ₁ ℓ (n + 1)) (value : Expr ζ₁ ℓ n) :
    (e'.inst value).map pre =
      (e'.map pre).inst (value.map pre) := by
  unfold inst
  rw [map_subst, Subst.map_extend, Subst.map_id]

def boundVars (ambient count suffix : Nat) :
    Fin count → Expr ζ ℓ (ambient + count + suffix) :=
  fun i => .var ((Fin.natAdd ambient i).castAdd suffix)

@[simp] theorem map_boundVars_apply (pre : ζ₁ ⟶ ζ₂)
    (ambient count suffix : Nat) (i : Fin count) :
    (boundVars (ambient := ambient) (count := count) (suffix := suffix) i :
      Expr ζ₁ ℓ _).map pre =
      boundVars ambient count suffix i := rfl

def applyBound (η : Expr ζ ℓ n) : (k : Nat) → Expr ζ ℓ (n + k)
  | 0 => η
  | k + 1 => .app (η.applyBound k).wk (.var (Fin.last (n + k)))

@[simp] theorem map_applyBound (pre : ζ₁ ⟶ ζ₂)
    (η : Expr ζ₁ ℓ n) (k : Nat) :
    (η.applyBound k).map pre = (η.map pre).applyBound k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [applyBound, map, map_wk, ih, applyBound]
      rfl

def isVar : Expr ζ ℓ n → Option Nat
  | .var v => some v.val
  | _ => none

theorem eq_var_of_isVar (e : Expr ζ ℓ n) (v : Fin n)
    (h : e.isVar = some v.val) :
    e = .var v := by
  cases e <;> simp [isVar] at h
  rename_i actual
  congr 1
  exact Fin.ext h

@[simp] theorem isVar_map (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n) :
    (e.map pre).isVar = e.isVar := by
  cases e <;> rfl

@[simp] theorem instL_rename (ls : Param ℓ → Level ℓ') (ρ : Ren m n)
    (e : Expr ζ ℓ m) :
    (e.rename ρ){ls} = e{ls}.rename ρ := by
  induction e generalizing n <;> simp [rename, funext_iff, *]

@[simp] theorem instL_wkFrom (ls : Param ℓ → Level ℓ') (cut : Nat)
    (e : Expr ζ ℓ n) :
    (e.wkFrom cut){ls} = e{ls}.wkFrom cut :=
  instL_rename ls (Ren.wkFrom cut) e

@[simp] theorem instL_wk (ls : Param ℓ → Level ℓ') (e : Expr ζ ℓ n) :
    e.wk{ls} = e{ls}.wk :=
  instL_wkFrom ls n e

@[simp] theorem instL_wkClosed (ls : Param ℓ → Level ℓ') (e : Expr ζ ℓ 0) :
    {n : Nat} → e.wkClosed (n := n){ls} = e{ls}.wkClosed (n := n)
  | 0 => rfl
  | n + 1 => by
      rw [wkClosed, instL_wk, instL_wkClosed ls e, wkClosed]

end Expr

namespace Subst

@[simp] theorem instL_append {a b : Nat} (ls : Param ℓ → Level ℓ')
    (σ₁ : Subst ζ ℓ a n) (σ₂ : Subst ζ ℓ b n) :
    (Fin.append σ₁ σ₂){ls} = Fin.append σ₁{ls} σ₂{ls} :=
  Fin.append_comp σ₁ σ₂ (·{ls})

@[simp] theorem instL_id (ls : Param ℓ → Level ℓ') :
    (id : Subst ζ ℓ n n){ls} = id :=
  rfl

@[simp] theorem instL_lift (ls : Param ℓ → Level ℓ') (σ : Subst ζ ℓ m n) :
    σ.lift{ls} = Subst.lift σ{ls} := by
  funext v
  simp [lift, Expr.wk, Expr.wkFrom]
  split
  · exact Expr.instL_rename ls _ _
  · rfl

@[simp] theorem instL_liftN (ls : Param ℓ → Level ℓ') (σ : Subst ζ ℓ m n) (k : Nat) :
    (σ.liftN k){ls} = Subst.liftN σ{ls} k := by
  induction k <;> simp_all!

@[simp] theorem instL_extend (ls : Param ℓ → Level ℓ') (σ : Subst ζ ℓ m n)
    (e : Expr ζ ℓ n) :
    (σ.extend e){ls} = Subst.extend σ{ls} e{ls} :=
  Fin.comp_snoc (·{ls}) σ e

end Subst

namespace Expr

@[simp] theorem instL_subst (ls : Param ℓ → Level ℓ') (σ : Subst ζ ℓ m n)
    (e : Expr ζ ℓ m) :
    (e.subst σ){ls} = e{ls}.subst σ{ls} := by
  induction e generalizing n <;> simp! [funext_iff, *]

@[simp] theorem instL_inst (ls : Param ℓ → Level ℓ') (e' : Expr ζ ℓ (n + 1))
    (e : Expr ζ ℓ n) :
    (e'.inst e){ls} = e'{ls}.inst e{ls} := by
  rw [inst, instL_subst, inst, Subst.instL_extend]
  congr 1

attribute [local instance] Level.category in
@[simp] theorem instL_instL (ls₁ : Param ℓ → Level ℓ') (ls₂ : Param ℓ' → Level k)
    (e : Expr ζ ℓ n) :
    e{ls₁}{ls₂} = e{ls₁{ls₂}} :=
  ((levelFunctor ζ n).map_comp_apply ls₁ ls₂ e).symm

@[simp] theorem wkN_instL (ls : Param ℓ → Level ℓ') (e : Expr ζ ℓ n) (k : Nat) :
    (e.wkN k){ls} = e{ls}.wkN k := by
  induction k <;> simp_all!

@[simp] theorem instL_boundVars (ls : Param ℓ → Level ℓ')
    (ambient count suffix : Nat) (i : Fin count) :
    (boundVars (ζ := ζ) (ℓ := ℓ) ambient count suffix i){ls} =
      boundVars (ζ := ζ) (ℓ := ℓ') ambient count suffix i := rfl

@[simp] theorem instL_var_tuple (ls : Param ℓ → Level ℓ') (f : Fin m → Fin n) :
    (fun i => (Expr.var (f i) : Expr ζ ℓ n)){ls} =
      fun i => Expr.var (f i) := by
  funext i
  simp

@[simp] theorem instL_applyBound (ls : Param ℓ → Level ℓ')
    (η : Expr ζ ℓ n) (k : Nat) :
    (η.applyBound k){ls} = η{ls}.applyBound k := by
  induction k <;> simp_all!

attribute [local instance] Level.category in
@[simp] theorem instL_param (e : Expr ζ ℓ n) :
    e{(Level.param : Param ℓ → Level ℓ)} = e :=
  (levelFunctor ζ n).map_id_apply ℓ e

@[simp] theorem wkN_sort (u : Level ℓ) (k scope : Nat) :
    (Expr.sort u : Expr ζ ℓ scope).wkN k = .sort u := by
  simp [wkN_eq_rename, rename]

end Expr

@[reducible] def Subst.comp (σ₁ : Subst ζ ℓ m n) (σ₂ : Subst ζ ℓ n p) : Subst ζ ℓ m p :=
  fun v => (σ₁ v).subst σ₂

@[simp] theorem Subst.id_comp (σ : Subst ζ ℓ m n) :
    Subst.id.comp σ = σ := rfl

@[simp] theorem Subst.comp_id (σ : Subst ζ ℓ m n) :
    σ.comp Subst.id = σ :=
  funext fun v => Expr.subst_id (σ v)

theorem Expr.wk_subst_lift (σ : Subst ζ ℓ m n) (e : Expr ζ ℓ m) :
    e.wk.subst σ.lift = (e.subst σ).wk := by
  rw [Expr.wk, Expr.wkFrom, Expr.rename_subst, Expr.wk, Expr.wkFrom, Expr.subst_rename]
  congr 1
  funext v
  simp [Subst.precomp, Subst.rename, Ren.wkFrom, Expr.wk, Expr.wkFrom]

@[simp] theorem Subst.lift_comp (σ₁ : Subst ζ ℓ m n) (σ₂ : Subst ζ ℓ n p) :
    σ₁.lift.comp σ₂.lift = (σ₁.comp σ₂).lift := by
  funext v
  by_cases h : v.val < m
  · simp [Subst.lift, Subst.comp, h, Expr.wk_subst_lift]
  · have hv : v = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    subst v
    simp [Subst.lift, Subst.comp, Expr.subst]

@[simp] theorem Subst.liftN_comp (σ₁ : Subst ζ ℓ m n) (σ₂ : Subst ζ ℓ n p) (k : Nat) :
    (σ₁.liftN k).comp (σ₂.liftN k) = (σ₁.comp σ₂).liftN k := by
  induction k <;> simp_all!

@[simp] theorem Expr.subst_subst (σ₁ : Subst ζ ℓ m n) (σ₂ : Subst ζ ℓ n p)
    (e : Expr ζ ℓ m) :
    (e.subst σ₁).subst σ₂ = e.subst (σ₁.comp σ₂) := by
  induction e generalizing n p with
  | var => rfl
  | _ => simp [Expr.subst, *]

namespace Expr

attribute [local instance] Ren.category in
@[reducible] def relativeMonad (ζ : Sigs) (ℓ : Nat) : RelativeMonad Ren.functor where
  obj n := Expr ζ ℓ n
  unit _ := ↾var
  bind σ := ↾subst σ
  unit_bind _ := rfl
  bind_unit _ := ConcreteCategory.hom_ext _ _ subst_id
  bind_bind σ₁ σ₂ := ConcreteCategory.hom_ext _ _ fun e => subst_subst σ₁ σ₂ e

attribute [local instance] Ren.category in
@[reducible] def relativeFunctor : Sigs ⥤ @Functor Nat Level.category (RelativeMonad Ren.functor) _ where
  obj ζ :=
    letI := Level.category
    { obj ℓ := relativeMonad ζ ℓ
      map σ :=
        letI := Ren.category
        { app _ := ↾instL σ
          unit_app _ := rfl
          bind_app τ := ConcreteCategory.hom_ext _ _ fun e => instL_subst σ τ e }
      map_id _ := by
        let := Ren.category
        ext n e
        exact instL_param e
      map_comp σ₁ σ₂ := by
        let := Ren.category
        ext n e
        exact (instL_instL σ₁ σ₂ e).symm }
  map ε :=
    letI := Level.category
    { app _ :=
        letI := Ren.category
        { app _ := ↾map ε
          unit_app _ := rfl
          bind_app τ := ConcreteCategory.hom_ext _ _ fun e => map_subst ε τ e }
      naturality _ _ σ := by
        let := Ren.category
        ext n e
        exact map_instL ε σ e }
  map_id ζ := by
    apply NatTrans.ext
    funext ℓ
    let := Ren.category
    ext n e
    exact (functor ℓ n).map_id_apply ζ e
  map_comp ε₁ ε₂ := by
    apply NatTrans.ext
    funext ℓ
    let := Ren.category
    ext n e
    exact (functor ℓ n).map_comp_apply ε₁ ε₂ e

attribute [local instance] Ren.category in
abbrev trifunctor : Sigs ⥤ @Functor Nat Level.category (@Functor Nat Ren.category Type _) _ :=
  relativeFunctor ⋙ (@Functor.whiskeringRight Nat Level.category _ _ _ _).obj RelativeMonad.forget

end Expr

end Metalean
