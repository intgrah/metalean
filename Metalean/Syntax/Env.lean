/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Basic
public import Metalean.Frontend.Lookup
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory

@[derive_functor ζ]
inductive Entry (ζ : Sigs) : Sig → Type
  | axiom {ℓ : Nat} (t : Expr ζ ℓ 0) : Entry ζ (.const .axiom ℓ)
  | opaque {ℓ : Nat} (t : Expr ζ ℓ 0) : Entry ζ (.const .opaque ℓ)
  | def {ℓ : Nat} (t e : Expr ζ ℓ 0) : Entry ζ (.const .def ℓ)
  | inductive {ι : IndSig} (I : Inductive ζ ι) : Entry ζ (.inductive ι)
  | quot (η : Head ζ (.inductive Eq.sig)) : Entry ζ .quot

variable {sig sig₁ sig₂ : Sig} {ζ ζ₁ ζ₂ ζ₃ : Sigs}
  {nlevels : Nat} {ι : IndSig} {kind : ConstKind}

namespace Entry

def weakenEnv (entry : Entry ζ sig) : Entry (.snoc ζ sig₁) sig :=
  entry.map (.step .refl)

def constType : Entry ζ (.const kind nlevels) → Expr ζ nlevels 0
  | .axiom t | .opaque t | .def t _ => t

def defValue : Entry ζ (.const .def nlevels) → Expr ζ nlevels 0
  | .def _ e => e

def block : Entry ζ (.inductive ι) → Inductive ζ ι
  | .inductive I => I

def eqHead : Entry ζ .quot → Head ζ (.inductive Eq.sig)
  | .quot η => η

@[simp] theorem block_map (entry : Entry ζ₁ (.inductive ι)) (pre : ζ₁ ⟶ ζ₂) :
    (entry.map pre).block = entry.block.map pre := by
  cases entry
  rfl

@[reducible] def constTypeNatTrans (kind : ConstKind) (nlevels : Nat) :
    functor (.const kind nlevels) ⟶ Expr.functor nlevels 0 where
  app ζ := ↾constType
  naturality {_ _} pre := by ext (_ | _) <;> rfl

@[reducible] def defValueNatTrans (nlevels : Nat) :
    functor (.const .def nlevels) ⟶ Expr.functor nlevels 0 where
  app ζ := ↾defValue
  naturality {_ _} pre := by ext (_ | _); rfl

@[reducible] def blockNatTrans (ι : IndSig) : functor (.inductive ι) ⟶ Inductive.functor ι where
  app ζ := ↾block
  naturality {_ _} pre := by ext (_ | _); rfl

@[reducible] def eqHeadNatTrans : functor .quot ⟶ Head.functor (.inductive Eq.sig) where
  app ζ := ↾eqHead
  naturality {_ _} pre := by ext (_ | _); rfl

end Entry

/-- Custom snoc list of `Sig` -/
inductive Env : Sigs → Type
  | nil : Env .nil
  | snoc {ζ : Sigs} {sig : Sig} :
    Env ζ → Entry ζ sig → Env (ζ.snoc sig)

namespace Env

abbrev as (E : Env ζ) : Σ ζ, Env ζ := ⟨ζ, E⟩

/-- This has to be data not a Prop -/
inductive Prefix : {ζ₁ ζ₂ : Sigs} → Env ζ₁ → Env ζ₂ → Type
  | refl {ζ : Sigs} {E : Env ζ} :
    Prefix E E
  | step {ζ₁ ζ₂ : Sigs} {sig : Sig} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
      {entry : Entry ζ₂ sig} :
    Prefix E₁ E₂ → Prefix E₁ (E₂.snoc entry)

inductive Prefix.Forall (p : ∀ {ζ sig}, Entry ζ sig → Prop) :
    {ζ₁ ζ₂ : Sigs} → {E₁ : Env ζ₁} → {E₂ : Env ζ₂} → Prefix E₁ E₂ → Prop
  | refl {ζ : Sigs} {E : Env ζ} : Forall p (Prefix.refl : Prefix E E)
  | step {ζ₁ ζ₂ : Sigs} {sig : Sig} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    {entry : Entry ζ₂ sig} {pre : Prefix E₁ E₂} :
    Forall p pre → p entry → Forall p (pre.step : Prefix E₁ (E₂.snoc entry))

def Prefix.sigs {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} : Prefix E₁ E₂ → (ζ₁ ⟶ ζ₂)
  | .refl => .refl
  | .step pre => .step pre.sigs

def Prefix.trans {ζ₁ ζ₂ ζ₃ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    {E₃ : Env ζ₃} :
    Prefix E₁ E₂ → Prefix E₂ E₃ → Prefix E₁ E₃
  | pre, .refl => pre
  | pre, .step suffix => .step (pre.trans suffix)

instance : SmallCategory (Σ ζ, Env ζ) where
  Hom | ⟨_, E₁⟩, ⟨_, E₂⟩ => Prefix E₁ E₂
  id _ := .refl
  comp := Prefix.trans
  id_comp := by
    intro ⟨ζ₁, E₁⟩ ⟨ζ₂, E₂⟩ pre
    induction pre with
    | refl => rfl
    | step pre ih => simp [Prefix.trans, ih]
  comp_id _ := rfl
  assoc := by
    intro ⟨ζ₁, E₁⟩ ⟨ζ₂, E₂⟩ ⟨ζ₃, E₃⟩ ⟨ζ₄, E₄⟩ pre₁ pre₂ pre₃
    induction pre₃ with
    | refl => rfl
    | step pre₃ ih => simp [Prefix.trans, ih]

@[reducible] def forget : (Σ ζ, Env ζ) ⥤ Sigs where
  obj E := E.1
  map := Prefix.sigs
  map_id _ := rfl
  map_comp := by
    intro ⟨ζ₁, E₁⟩ ⟨ζ₂, E₂⟩ ⟨ζ₃, E₃⟩ pre₁ pre₂
    induction pre₂ with
    | refl => rfl
    | step pre₂ ih => exact congrArg Sigs.Prefix.step (ih pre₁)

variable {E : Env ζ} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {E₃ : Env ζ₃}

/-- TOTAL environment lookup -/
def get {ζ : Sigs} {sig : Sig} : Env ζ → Head ζ sig → Entry ζ sig
  | .snoc _ entry, .here => entry.weakenEnv
  | .snoc pre _, .there η => (pre.get η).weakenEnv

@[simp] theorem get_map_step (E : Env ζ) (entry : Entry ζ sig)
    (η : Head ζ sig₂) :
    (E.snoc entry).get (η.map (.step .refl)) =
      (E.get η).map (.step .refl) := rfl

theorem get_map (pre : Prefix E₁ E₂) (η : Head ζ₁ sig) :
    E₂.get (η.map pre.sigs) = (E₁.get η).map pre.sigs := by
  induction pre with
  | refl => exact ((Entry.functor sig).map_id_apply _ (get _ η)).symm
  | step pre ih =>
    change (Env.get _ (η.map pre.sigs)).map (.step .refl) = _
    rw [ih]
    exact ((Entry.functor sig).map_comp_apply pre.sigs (.step .refl) _).symm

@[reducible] def lookup (sig : Sig) : forget ⋙ Head.functor sig ⟶ forget ⋙ Entry.functor sig where
  app E := ↾E.2.get
  naturality := by
    intro ⟨ζ₁, E₁⟩ ⟨ζ₂, E₂⟩ pre
    ext η
    exact get_map pre η

@[reducible, functor] def headFunctor (sig : Sig) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Head.functor sig

@[reducible, functor] def exprFunctor (ℓ n : Nat) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Expr.functor ℓ n

@[reducible, functor] def ctxFunctor (ℓ a b : Nat) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Ctx.functor ℓ a b

@[reducible, functor] def fieldFunctor (ι : IndSig) (nfields : Nat) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Field.functor ι nfields

@[reducible, functor] def recFieldFunctor (ι : IndSig) (nfields arity : Nat)
    (target : Fin ι.nsorts) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ RecField.functor ι nfields arity target

@[reducible, functor] def ctorFunctor (ι : IndSig) (s : Fin ι.nsorts) (csig : CtorSig ι.nsorts) :
    (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Ctor.functor ι s csig

@[reducible, functor] def inductiveFunctor (ι : IndSig) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Inductive.functor ι

@[reducible, functor] def entryFunctor (sig : Sig) : (Σ ζ, Env ζ) ⥤ Type :=
  forget ⋙ Entry.functor sig

@[transport] theorem lookup_map {E₁ E₂ : Σ ζ, Env ζ} (pre : E₁ ⟶ E₂) {p : Nat}
    {η : Head E₁.1 sig} :
    E₁.1.lookup p = some ⟨sig, η⟩ →
    E₂.1.lookup p = some ⟨sig, η.map (Prefix.sigs pre)⟩ :=
  Sigs.lookup_map (Prefix.sigs pre)

end Env

end Metalean
