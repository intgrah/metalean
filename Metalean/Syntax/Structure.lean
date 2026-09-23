/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Recursor
public import Metalean.Syntax.Inductive.LargeElimination
public import Metalean.Syntax.Env
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean.Inductive

open CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {ℓ ℓ' n m : Nat}
  {ι : IndSig} {η : Head ζ₁ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}

structure IsStructure (I : Inductive ζ₁ ι)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) : Prop where
  sort_unique : ∀ s', s' = s
  ctor_unique : ∀ c', c' = c
  no_indices : IsEmpty (Fin (ι.nindices s))
  no_recursive : IsEmpty (Fin (ι.ctors s c).nrecFields)
  sortLargeElim : I.SortLargeElim s

namespace IsStructure

variable {I : Inductive ζ₁ ι}

theorem map (h : I.IsStructure s c) (pre : ζ₁ ⟶ ζ₂) :
    (I.map pre).IsStructure s c where
  sort_unique := h.sort_unique
  ctor_unique := h.ctor_unique
  no_indices := h.no_indices
  no_recursive := h.no_recursive
  sortLargeElim := (I.sortLargeElim_map pre s).mpr h.sortLargeElim

theorem largeElim (h : I.IsStructure s c) : I.LargeElim :=
  fun other => h.sort_unique other ▸ h.sortLargeElim

theorem recAllowed (h : I.IsStructure s c) (l : Level ℓ) :
    I.RecAllowed l :=
  .inr h.largeElim

def indices (h : I.IsStructure s c) {α : Sort _} : Fin (ι.nindices s) → α :=
  h.no_indices.elim

def recursive (h : I.IsStructure s c) {α : Sort _} : Fin (ι.ctors s c).nrecFields → α :=
  h.no_recursive.elim

def projTypeWith (I : Inductive ζ₁ ι) {n : Nat}
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (previous : Fin f.val → Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  let C := I.ctors s c
  (C.ordinary f).type{ls}.subst (Fin.append ps previous)

@[simp] theorem projTypeWith_map
    (pre : ζ₁ ⟶ ζ₂)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (previous : Fin f.val → Expr ζ₁ ℓ n) :
    (projTypeWith I ls ps f previous).map pre =
      projTypeWith (I.map pre) ls
        (fun param => (ps param).map pre) f
        fun prior => (previous prior).map pre := by
  simp [projTypeWith, Inductive.map, Ctor.map, Field.map]

@[simp] theorem projTypeWith_instL
    (ls' : Param ℓ → Level ℓ')
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (previous : Fin f.val → Expr ζ₁ ℓ n) :
    (projTypeWith I ls ps f previous){ls'} =
      projTypeWith I ls{ls'} ps{ls'} f previous{ls'} := by
  simp [projTypeWith, InstLevel.inst_tuple, Fin.append_comp]

def projection {n : Nat} (h : I.IsStructure s c)
    (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (maj : Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n × Expr ζ₁ ℓ n :=
  let previous := fun previous : Fin f.val =>
    (projection h η ls ps
      (previous.castLT (previous.isLt.trans f.isLt)) maj).2
  let type := projTypeWith I ls ps f previous
  let u := ((I.ctors s c).ordinary f).level{ls}
  let ms : Fin ι.nsorts → Expr ζ₁ ℓ n := fun other => by
    have hs := h.sort_unique other
    subst other
    let previous : Fin f.val →
        Expr ζ₁ ℓ (n + ι.nindices s + 1) := fun previous =>
      (h.projection (n := n + ι.nindices s + 1) η ls
        (fun param => (ps param).wkN (ι.nindices s + 1))
        (previous.castLT (previous.isLt.trans f.isLt))
        (.var (Fin.last (n + ι.nindices s)))).2
    exact Ctx.lam
      (projTypeWith I ls
        (fun param => (ps param).wkN (ι.nindices s + 1)) f previous)
      (I.motiveTele η ls ps s)
  let mins : (other : Fin ι.nsorts) →
      Fin (ι.nctors other) → Expr ζ₁ ℓ n := fun other otherCtor => by
    have hs := h.sort_unique other
    subst other
    have hc := h.ctor_unique otherCtor
    subst otherCtor
    exact Ctx.lam
      ((ι.ctors s c).caseOrdinary (n := n) f)
      (I.caseTele η ls ps ms s c)
  (type, .recr η s ls u ps ms mins h.indices maj)

def projType (h : I.IsStructure s c)
    (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (maj : Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  (h.projection η ls ps f maj).1

def projTerm (h : I.IsStructure s c)
    (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (maj : Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  (h.projection η ls ps f maj).2

def rebuildTerm (h : I.IsStructure s c)
    (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (maj : Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  .ctor η s c ls ps (fun f => h.projTerm η ls ps f maj) h.recursive

variable (h : I.IsStructure s c)
  (pre : ζ₁ ⟶ ζ₂)
  (ls' : Param ℓ → Level ℓ')
  (η : Head ζ₁ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ)
  (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
  (f : Fin (ι.ctors s c).nfields)
  (maj : Expr ζ₁ ℓ n)

def projectionMotives : Fin ι.nsorts → Expr ζ₁ ℓ n := fun other => by
  obtain hs := h.sort_unique other
  subst other
  let previous : Fin f.val →
      Expr ζ₁ ℓ (n + ι.nindices s + 1) := fun previous =>
    h.projTerm (n := n + ι.nindices s + 1) η ls
      (fun param => (ps param).wkN (ι.nindices s + 1))
      (previous.castLT (previous.isLt.trans f.isLt))
      (.var (Fin.last (n + ι.nindices s)))
  exact Ctx.lam
    (projTypeWith I ls
      (fun param => (ps param).wkN (ι.nindices s + 1)) f previous)
    (I.motiveTele η ls ps s)

def projectionCases (ms : Fin ι.nsorts → Expr ζ₁ ℓ n) (other : Fin ι.nsorts)
    (otherCtor : Fin (ι.nctors other)) : Expr ζ₁ ℓ n := by
  have hs := h.sort_unique other
  subst other
  have hc := h.ctor_unique otherCtor
  subst otherCtor
  exact Ctx.lam ((ι.ctors s c).caseOrdinary f) (I.caseTele η ls ps ms s c)

theorem projTerm_eq_recr :
    h.projTerm η ls ps f maj =
      .recr η s ls ((I.ctors s c).ordinary f).level{ls} ps
        (h.projectionMotives η ls ps f)
        (h.projectionCases η ls ps f (h.projectionMotives η ls ps f)) h.indices maj := by
  rw [projTerm, projection]
  rfl

theorem projection_map :
    (h.projection η ls ps f maj).map (Expr.map pre) (Expr.map pre) =
      (h.map pre).projection (η.map pre) ls
        (fun param => (ps param).map pre) f
        (maj.map pre) := by
  fun_induction h.projection η ls ps f maj with
  | case1 n ps f maj previous type u ms cases ihMajor ihMotive =>
    have ihMajorTerm := fun previous => congrArg Prod.snd (ihMajor previous)
    have ihMotiveTerm := fun previous => congrArg Prod.snd (ihMotive previous)
    simp at ihMajorTerm ihMotiveTerm
    rw [projection, Prod.map]
    congr 1
    · rw [projTypeWith_map]
      congr 1
      funext previous
      exact ihMajorTerm previous
    · simp only [Expr.map]
      congr 1
      · funext other
        have hs := h.sort_unique other
        subst other
        simp [ms, ihMotiveTerm, Expr.map]
      · funext other otherCtor
        have hs := h.sort_unique other
        subst other
        have hc := h.ctor_unique otherCtor
        subst otherCtor
        simp only [cases]
        simp [ms, ihMotiveTerm, Expr.map]
      · exact funext h.no_indices.elim

@[simp] theorem projType_map :
    (h.projType η ls ps f maj).map pre =
      (h.map pre).projType (η.map pre) ls
        (fun param => (ps param).map pre) f
        (maj.map pre) :=
  congrArg Prod.fst (h.projection_map pre η ls ps f maj)

@[simp] theorem projTerm_map :
    (h.projTerm η ls ps f maj).map pre =
      (h.map pre).projTerm (η.map pre) ls
        (fun param => (ps param).map pre) f
        (maj.map pre) :=
  congrArg Prod.snd (h.projection_map pre η ls ps f maj)

@[simp] theorem rebuildTerm_map :
    (h.rebuildTerm η ls ps maj).map pre =
      (h.map pre).rebuildTerm (η.map pre) ls
        (fun param => (ps param).map pre)
        (maj.map pre) := by
  simp only [rebuildTerm, Expr.map]
  congr 1
  · funext f
    exact h.projTerm_map pre η ls ps f maj
  · exact funext h.no_recursive.elim

theorem projection_instL :
    (h.projection η ls ps f maj).map (·{ls'}) (·{ls'}) =
      h.projection η ls{ls'} ps{ls'} f maj{ls'} := by
  fun_induction h.projection η ls ps f maj with
  | case1 n ps₁ field maj previous type u ms cases ihMajor ihMotive =>
    have hwk : ((fun param => (ps₁ param).wkN (ι.nindices s + 1)) :
        Fin ι.nparams → Expr ζ₁ ℓ (n + (ι.nindices s + 1))){ls'} =
        (fun param => (ps₁ param){ls'}.wkN (ι.nindices s + 1)) := by
      funext param
      simp
    have ihMajorTerm := fun previous => congrArg Prod.snd (ihMajor previous)
    have ihMotiveTerm := fun previous => congrArg Prod.snd (ihMotive previous)
    simp at ihMajorTerm ihMotiveTerm
    rw [projection, Prod.map]
    congr 1
    · rw [projTypeWith_instL]
      congr 1
      funext previous
      exact ihMajorTerm previous
    · simp only [Expr.inst_recr]
      congr 1
      · simp [u, InstLevel.inst_tuple]
      · funext other
        have hs := h.sort_unique other
        subst other
        simp [ms, ← hwk]
        congr 2
        funext previous
        exact ihMotiveTerm previous
      · funext other otherCtor
        have hs := h.sort_unique other
        subst other
        have hc := h.ctor_unique otherCtor
        subst otherCtor
        simp [cases, ms, ← hwk]
        congr 2
        funext other
        have hs := h.sort_unique other
        subst other
        simp
        congr 2
        funext previous
        exact ihMotiveTerm previous
      · exact funext h.no_indices.elim

@[simp] theorem projType_instL :
    (h.projType η ls ps f maj){ls'} =
      h.projType η ls{ls'} ps{ls'} f maj{ls'} :=
  congrArg Prod.fst (h.projection_instL ls' η ls ps f maj)

@[simp] theorem projTerm_instL :
    (h.projTerm η ls ps f maj){ls'} =
      h.projTerm η ls{ls'} ps{ls'} f maj{ls'} :=
  congrArg Prod.snd (h.projection_instL ls' η ls ps f maj)

@[simp] theorem rebuildTerm_instL :
    (h.rebuildTerm η ls ps maj){ls'} =
      h.rebuildTerm η ls{ls'} ps{ls'} maj{ls'} := by
  simp only [rebuildTerm, Expr.inst_ctor]
  congr 1
  · funext f
    exact h.projTerm_instL ls' η ls ps f maj
  · exact funext h.no_recursive.elim

theorem ordinaryLevel_eq_zero_of_eval_zero
    {ν : Param ℓ → Nat} {c : Fin (ι.nctors s)} (h : I.IsStructure s c) (ls : Fin ι.nlevels → Level ℓ)
    (hzero : I.level{ls}.eval ν = 0) (f : Fin (ι.ctors s c).nfields) :
    ((I.ctors s c).ordinary f).level = .zero := by
  have hel := (h.sortLargeElim.singleton_of_eval_zero ls hzero c).2.ordinary f
  rcases hel with hu | ⟨i, _⟩
  · exact hu
  · exact h.no_indices.elim i

end IsStructure

end Metalean.Inductive

namespace Metalean.Env.IsStructure

open CategoryTheory

variable {ℓ n : Nat} {ι : IndSig} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}

@[transport] theorem map {E₁ E₂ : Σ ζ, Env ζ} (pre : E₁ ⟶ E₂) {η : Head E₁.1 (.inductive ι)} :
    (E₁.2.get η).block.IsStructure s c →
    (E₂.2.get (η.map pre.sigs)).block.IsStructure s c := by
  intro h
  rw [Env.get_map, Entry.block_map]
  exact h.map _

@[simp high] theorem projTerm_map {E₁ E₂ : Σ ζ, Env ζ} (pre : E₁ ⟶ E₂)
    {η : Head E₁.1 (.inductive ι)} (h : (E₁.2.get η).block.IsStructure s c)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr E₁.1 ℓ n)
    (f : Fin (ι.ctors s c).nfields) (maj : Expr E₁.1 ℓ n) :
    (h.projTerm η ls ps f maj).map pre.sigs =
      (map pre h).projTerm (η.map pre.sigs) ls
        (fun param => (ps param).map pre.sigs) f (maj.map pre.sigs) := by
  rw [Inductive.IsStructure.projTerm_map]
  generalize map pre h = h'
  revert h'
  rw [Env.get_map, Entry.block_map]
  intro h'
  rfl

end Metalean.Env.IsStructure
