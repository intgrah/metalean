/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.FCtx
public import Metalean.Syntax.Eq
public import Metalean.Syntax.Env
import Metalean.Meta.DeriveFunctor
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.FastChecker

open CategoryTheory

structure FField where
  type : FExpr
  level : FLevel
deriving DecidableEq

structure FRecField where
  tele : FCtx
  indices : Array FExpr
deriving DecidableEq

structure FCtor where
  ordinary : Array FField
  recursive : Array FRecField
  targetIndices : Array FExpr
deriving DecidableEq

structure FInductive where
  params : FCtx
  indices : Array FCtx
  level : FLevel
  ctors : Array (Array FCtor)
deriving DecidableEq

inductive FEntry where
  | axiom (nlevels : Nat) (ft : FExpr)
  | opaque (nlevels : Nat) (ft : FExpr)
  | def (nlevels : Nat) (ft fv : FExpr)
  | inductive (ι : IndSig) (I : FInductive)
  | quot (eqPos : Nat)

def FEntry.sig : FEntry → Sig
  | .axiom nlevels _ => .const .axiom nlevels
  | .opaque nlevels _ => .const .opaque nlevels
  | .def nlevels _ _ => .const .def nlevels
  | .inductive ι _ => .inductive ι
  | .quot _ => .quot

def FEntry.constType? : FEntry → Option (Nat × FExpr)
  | .axiom nlevels ft | .opaque nlevels ft | .def nlevels ft _ => some (nlevels, ft)
  | .inductive _ _ | .quot _ => none

abbrev FEnv := Array FEntry

variable (L : Literals) {ℓ : Nat}

@[derive_functor E]
structure FField.Denotes (E : Σ ζ, Env ζ) {ι : IndSig} {nfields : Nat} (ffd : FField)
    (fd : Field E.1 ι nfields) : Prop where
  type : FExpr.Denotes L E 0 ffd.type fd.type
  level : ∃ l, FLevel.Denotes ffd.level l ∧ ⟦l⟧ = fd.level

@[derive_functor E]
structure FRecField.Denotes (E : Σ ζ, Env ζ) {ι : IndSig} {nfields arity : Nat}
    {target : Fin ι.nsorts}
    (ffd : FRecField) (fd : RecField E.1 ι nfields arity target) : Prop where
  tele : FCtx.Denotes L E ffd.tele fd.tele
  size : ffd.indices.size = ι.nindices target
  indices : ∀ i,
    FExpr.Denotes L E 0 (ffd.indices[i.val]'(size.symm ▸ i.isLt)) (fd.indices i)

@[derive_functor E]
structure FCtor.Denotes (E : Σ ζ, Env ζ) {ι : IndSig} {s : Fin ι.nsorts}
    {csig : CtorSig ι.nsorts}
    (fctor : FCtor) (ctor : Ctor E.1 ι s csig) : Prop where
  ordinarySize : fctor.ordinary.size = csig.nfields
  ordinary : ∀ f,
    FField.Denotes L E (fctor.ordinary[f.val]'(ordinarySize.symm ▸ f.isLt)) (ctor.ordinary f)
  recursiveSize : fctor.recursive.size = csig.nrecFields
  recursive : ∀ f,
    FRecField.Denotes L E (fctor.recursive[f.val]'(recursiveSize.symm ▸ f.isLt))
      (ctor.recursive f)
  targetSize : fctor.targetIndices.size = ι.nindices s
  targetIndices : ∀ i,
    FExpr.Denotes L E 0
      (fctor.targetIndices[i.val]'(targetSize.symm ▸ i.isLt)) (ctor.targetIndices i)

@[derive_functor E]
structure FInductive.Denotes (E : Σ ζ, Env ζ) {ι : IndSig} (fI : FInductive)
    (I : Inductive E.1 ι) :
    Prop where
  params : FCtx.Denotes L E fI.params I.params
  indicesSize : fI.indices.size = ι.nsorts
  indices : ∀ s,
    FCtx.Denotes L E (fI.indices[s.val]'(indicesSize.symm ▸ s.isLt)) (I.indices s)
  level : ∃ l, FLevel.Denotes fI.level l ∧ ⟦l⟧ = I.level
  ctorsSize : fI.ctors.size = ι.nsorts
  ctorsRow : ∀ s, (fI.ctors[s.val]'(ctorsSize.symm ▸ s.isLt)).size = ι.nctors s
  ctors : ∀ s c,
    FCtor.Denotes L E
      ((fI.ctors[s.val]'(ctorsSize.symm ▸ s.isLt))[c.val]'((ctorsRow s).symm ▸ c.isLt))
      (I.ctors s c)

@[derive_functor E]
judgement FEntry.Denotes (L : Literals) (E : Σ ζ, Env ζ) :
    (fentry : FEntry) → (entry : Entry E.1 fentry.sig) → Prop where

  FExpr.Denotes L E 0 ft t
  ──────────────────── «axiom» {nlevels ft t}
  Denotes L E (.axiom nlevels ft) (.axiom t)

  FExpr.Denotes L E 0 ft t
  ──────────────────── «opaque» {nlevels ft t}
  Denotes L E (.opaque nlevels ft) (.opaque t)

  FExpr.Denotes L E 0 ft t
  FExpr.Denotes L E 0 fv v
  ──────────────────── «def» {nlevels ft fv t v}
  Denotes L E (.def nlevels ft fv) (.def t v)

  FInductive.Denotes L E fI I
  ──────────────────── «inductive» {ι : IndSig} {fI : FInductive} {I : Inductive E.1 ι}
  Denotes L E (.inductive ι fI) (.inductive I)

  E.1.lookup eqPos = some ⟨.inductive Eq.sig, η⟩
  ──────────────────── quot {eqPos} {η : Head E.1 (.inductive Eq.sig)}
  Denotes L E (.quot eqPos) (.quot η)

judgement FEnv.Denotes (L : Literals) : (F : FEnv) → {ζ : Sigs} → (E : Env ζ) → Prop where

  ──────────────────── nil
  Denotes L #[] .nil

  Denotes L F E
  FEntry.Denotes L ⟨ζ, E⟩ fentry entry
  ──────────────────── snoc {F ζ} {E : Env ζ} {fentry entry}
  Denotes L (F.push fentry) (E.snoc entry)

variable {L} {ζ : Sigs}

theorem FEnv.Denotes.size {F : FEnv} {E : Env ζ} :
    FEnv.Denotes L F E →
    F.size = ζ.length := by
  intro h
  induction h with
  | nil => rfl
  | snoc _ _ ih => simp [Sigs.length, ih]

theorem FEnv.Denotes.get {F : FEnv} {E : Env ζ} {pos : Nat} {fentry : FEntry}
    (hfe : F[pos]? = some fentry) :
    FEnv.Denotes L F E →
    ∃ η : Head ζ fentry.sig, ζ.lookup pos = some ⟨fentry.sig, η⟩ ∧
      FEntry.Denotes L ⟨ζ, E⟩ fentry (E.get η) := by
  intro h
  induction h with
  | nil => simp at hfe
  | @snoc F ζ E fentry₀ entry hE he ih =>
    rw [Array.getElem?_push] at hfe
    by_cases hpos : pos = F.size
    · simp only [hpos, ↓reduceIte, Option.some.injEq] at hfe
      subst hfe
      refine ⟨.here, by simp [Sigs.lookup, hpos, hE.size], ?_⟩
      exact he.map (target := ⟨_, E.snoc entry⟩) (Env.Prefix.step .refl)
    · simp only [hpos] at hfe
      have ⟨η, hη, hden⟩ := ih hfe
      refine ⟨η.there,
        by simp [Sigs.lookup, hη, show pos ≠ ζ.length by rw [← hE.size]; exact hpos], ?_⟩
      exact hden.map (target := ⟨_, E.snoc entry⟩) (Env.Prefix.step .refl)

theorem FEnv.Denotes.lookup {E : Σ ζ, Env ζ} {F : FEnv} (hE : FEnv.Denotes L F E.2) {pos : Nat}
    {fe : FEntry} (hfe : F[pos]? = some fe) {sig : Sig} (hsig : fe.sig = sig) :
    ∃ η : Head E.1 sig, E.1.lookup pos = some ⟨sig, η⟩ := by
  have ⟨η, hη, _⟩ := hE.get hfe
  subst hsig
  exact ⟨η, hη⟩

theorem FEnv.Denotes.inductive {F : FEnv} {E : Env ζ} {pos : Nat} {ι : IndSig} {I : FInductive}
    (hfe : F[pos]? = some (.inductive ι I)) :
    FEnv.Denotes L F E →
    ∃ η : Head ζ (.inductive ι), ζ.lookup pos = some ⟨.inductive ι, η⟩ ∧
      FInductive.Denotes L ⟨ζ, E⟩ I (E.get η).block := by
  intro hE
  have ⟨η, hη, hden⟩ := hE.get hfe
  generalize hentry : E.get η = entry at hden
  have .«inductive» hI := hden
  have hentry' : E.get (sig := .inductive ι) η = .inductive _ := hentry
  exact ⟨η, hη, by rw [hentry']; exact hI⟩

theorem FEnv.Denotes.constType {F : FEnv} {E : Σ ζ, Env ζ} {pos : Nat} {fe : FEntry}
    (hfe : F[pos]? = some fe) {nlevels : Nat} {ft : FExpr}
    (ht : fe.constType? = some (nlevels, ft)) :
    FEnv.Denotes L F E.2 →
    ∃ (kind : ConstKind) (η : Head E.1 (.const kind nlevels)),
      E.1.lookup pos = some ⟨.const kind nlevels, η⟩ ∧
        FExpr.Denotes L E 0 ft (E.2.get η).constType := by
  intro hE
  have ⟨η, hη, hden⟩ := hE.get hfe
  generalize hentry : E.2.get η = entry at hden
  cases hden with
  | «axiom» ht' =>
    cases ht
    exact ⟨_, η, hη, hentry ▸ ht'⟩
  | «opaque» ht' =>
    cases ht
    exact ⟨_, η, hη, hentry ▸ ht'⟩
  | «def» ht' _ =>
    cases ht
    exact ⟨_, η, hη, hentry ▸ ht'⟩
  | «inductive» => cases ht
  | quot => cases ht

theorem FEnv.Denotes.quot {F : FEnv} {E : Σ ζ, Env ζ} {pos eqPos : Nat}
    (hfe : F[pos]? = some (.quot eqPos)) :
    FEnv.Denotes L F E.2 →
    ∃ η : Head E.1 .quot, E.1.lookup pos = some ⟨.quot, η⟩ ∧
      E.1.lookup eqPos = some ⟨.inductive Eq.sig, (E.2.get η).eqHead⟩ := by
  intro hE
  have ⟨η, hη, hden⟩ := hE.get hfe
  generalize hentry : E.2.get η = entry at hden
  have .quot hηeq := hden
  have hentry' : E.2.get (sig := .quot) η = .quot _ := hentry
  exact ⟨η, hη, by rw [hentry']; exact hηeq⟩

section

variable {E : Env ζ}

theorem FEntry.Denotes.inductive_inv {ι : IndSig} {I : FInductive}
    {entry : Entry ζ (.inductive ι)} :
    FEntry.Denotes L ⟨ζ, E⟩ (.inductive ι I) entry →
    ∃ I', FInductive.Denotes L ⟨ζ, E⟩ I I' ∧ entry = .inductive I'
  | .inductive hI => ⟨_, hI, rfl⟩

end

section

variable {E : Σ ζ, Env ζ} {ι : IndSig}

structure FRecField.NoProj (ffd : FRecField) : Prop where
  tele : ∀ t ∈ ffd.tele, t.NoProj
  indices : ∀ i ∈ ffd.indices, i.NoProj

structure FCtor.NoProj (fctor : FCtor) : Prop where
  ordinary : ∀ f ∈ fctor.ordinary, f.type.NoProj
  recursive : ∀ r ∈ fctor.recursive, r.NoProj
  targetIndices : ∀ i ∈ fctor.targetIndices, i.NoProj

structure FInductive.NoProj (fI : FInductive) : Prop where
  params : ∀ t ∈ fI.params, t.NoProj
  indices : ∀ ts ∈ fI.indices, ∀ t ∈ ts, t.NoProj
  ctors : ∀ cs ∈ fI.ctors, ∀ c ∈ cs, c.NoProj

theorem FField.Denotes.unique {nfields : Nat} {ffd : FField} {fd₁ fd₂ : Field E.1 ι nfields} :
    FField.Denotes L E ffd fd₁ →
    FField.Denotes L E ffd fd₂ →
    ffd.type.NoProj →
    fd₁ = fd₂ := by
  intro ⟨h₁, ⟨l₁, hl₁, he₁⟩⟩ ⟨h₂, ⟨l₂, hl₂, he₂⟩⟩ hnp
  have hlevel : fd₁.level = fd₂.level := by
    rw [← he₁, ← he₂, hl₁.unique hl₂]
  exact congr(Field.mk $(h₁.unique h₂ hnp) $hlevel)

theorem FRecField.Denotes.unique {nfields arity : Nat} {target : Fin ι.nsorts} {ffd : FRecField}
    {fd₁ fd₂ : RecField E.1 ι nfields arity target} :
    FRecField.Denotes L E ffd fd₁ →
    FRecField.Denotes L E ffd fd₂ →
    ffd.NoProj →
    fd₁ = fd₂ := fun h₁ h₂ hnp =>
  congr(RecField.mk $(h₁.tele.unique h₂.tele hnp.tele)
    $(funext fun i => (h₁.indices i).unique (h₂.indices i)
      (hnp.indices _ (Array.getElem_mem _))))

theorem FCtor.Denotes.unique {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {fctor : FCtor}
    {ctor₁ ctor₂ : Ctor E.1 ι s csig} :
    FCtor.Denotes L E fctor ctor₁ →
    FCtor.Denotes L E fctor ctor₂ →
    fctor.NoProj →
    ctor₁ = ctor₂ := fun h₁ h₂ hnp =>
  congr(Ctor.mk
    $(funext fun f => (h₁.ordinary f).unique (h₂.ordinary f)
      (hnp.ordinary _ (Array.getElem_mem _)))
    $(funext fun r => (h₁.recursive r).unique (h₂.recursive r)
      (hnp.recursive _ (Array.getElem_mem _)))
    $(funext fun i => (h₁.targetIndices i).unique (h₂.targetIndices i)
      (hnp.targetIndices _ (Array.getElem_mem _))))

theorem FInductive.Denotes.unique {fI : FInductive} {I₁ I₂ : Inductive E.1 ι} :
    FInductive.Denotes L E fI I₁ →
    FInductive.Denotes L E fI I₂ →
    fI.NoProj →
    I₁ = I₂ := by
  intro h₁ h₂ hnp
  have ⟨l₁, hl₁, he₁⟩ := h₁.level
  have ⟨l₂, hl₂, he₂⟩ := h₂.level
  have hlevel : I₁.level = I₂.level := by
    rw [← he₁, ← he₂, hl₁.unique hl₂]
  exact congr(Inductive.mk $(h₁.params.unique h₂.params hnp.params)
    $(funext fun s => (h₁.indices s).unique (h₂.indices s)
      (hnp.indices _ (Array.getElem_mem _)))
    $hlevel
    $(funext fun s => funext fun c => (h₁.ctors s c).unique (h₂.ctors s c)
      (hnp.ctors _ (Array.getElem_mem _) _ (Array.getElem_mem _))))

end

end Metalean.FastChecker
