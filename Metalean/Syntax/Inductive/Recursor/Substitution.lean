/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Recursor
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {ℓ n : Nat} {ι : IndSig} {s : Fin ι.nsorts}
  (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
  (ps : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
  (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n)
  (is : Fin (ι.nindices s) → Expr ζ ℓ n) (maj : Expr ζ ℓ n)

def Inductive.recrSubst :
    Subst ζ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) n :=
  Fin.snoc (Fin.append (Fin.append (Fin.append ps ms) fun tag =>
    let ⟨s₁, c⟩ := Fin.decodeSigma ι.nctors tag
    mins s₁ c) is) maj

@[simp] theorem Inductive.recrSubst_param (param : Fin ι.nparams) :
    Inductive.recrSubst ps ms mins is maj
      (((param.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)).castAdd
        (ι.nindices s)).castSucc = ps param := by
  simp [Inductive.recrSubst]

@[simp] theorem Inductive.recrSubst_motive (s₁ : Fin ι.nsorts) :
    Inductive.recrSubst ps ms mins is maj
      (((Fin.natAdd ι.nparams s₁).castAdd
        (Fin.sum ι.nctors)).castAdd
        (ι.nindices s)).castSucc = ms s₁ := by
  simp [Inductive.recrSubst]

@[simp] theorem Inductive.recrSubst_case (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    Inductive.recrSubst ps ms mins is maj
      ((Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)).castAdd
        (ι.nindices s)).castSucc = mins s₁ c := by
  rw [Inductive.recrSubst, Fin.snoc_castSucc, Fin.append_left, Fin.append_right,
    Fin.decodeSigma_encodeSigma]

@[simp] theorem Inductive.recrSubst_index (index : Fin (ι.nindices s)) :
    Inductive.recrSubst ps ms mins is maj
      (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
        index.castSucc) = is index := by
  rw [Fin.natAdd_castSucc, Inductive.recrSubst, Fin.snoc_castSucc, Fin.append_right]

@[simp] theorem Inductive.recrSubst_major :
    Inductive.recrSubst ps ms mins is maj
      (Fin.last (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
        ι.nindices s)) = maj := by
  simp [Inductive.recrSubst]

def Inductive.recrBinderType (b : IndSig.RecrBinder ι s) : Expr ζ ℓ n :=
  match b with
  | .param p => I.paramType ls ps p
  | .motive t => I.motiveType η ls ps l t
  | .case t c => I.caseFnType η ls ps ms t c
  | .index i => I.indexType ls s ps is i
  | .major => .ind η s ls ps is

theorem Inductive.recrTele_get_subst (b : IndSig.RecrBinder ι s) :
    (Ctx.get b.resolve (I.recrTele η s ls l)).subst (Inductive.recrSubst ps ms mins is maj) =
      I.recrBinderType η ls l ps ms is b := by
  cases b with
  | param param =>
    dsimp only [IndSig.RecrBinder.resolve, recrBinderType]
    simp! [recrTele, Expr.wk_subst, Expr.wkN_eq_subst, Ren.wkN]
  | motive s₁ =>
    dsimp only [IndSig.RecrBinder.resolve, recrBinderType]
    simp! [recrTele, motiveBinders, Expr.wk_subst, Expr.wkN_eq_subst, Ren.wkN]
  | case s₁ c =>
    dsimp only [IndSig.RecrBinder.resolve, recrBinderType]
    unfold recrTele
    rw [Ctx.get_snoc _ _ _ (Nat.ne_of_lt
      ((Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)).castAdd
        (ι.nindices s)).isLt),
      Fin.castLT_castSucc, Ctx.get_append, caseBinders, Ctx.get_append_ofTypes,
      Fin.decodeSigma_encodeSigma]
    simp! [Expr.wk_subst, Expr.wkN_eq_subst, Ren.wkN]
  | index index =>
    dsimp only [IndSig.RecrBinder.resolve, recrBinderType]
    unfold recrTele
    rw [
      Ctx.get_snoc _ _ _ (Nat.ne_of_lt (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index).isLt),
      Expr.wk_subst, Fin.castLT_castSucc, I.indexTele_get]
    simp only [Inductive.indexType_subst]
    congr 2
    · funext p
      simp only [Expr.wkN_eq_rename, Expr.rename, Expr.subst]
      exact recrSubst_param ps ms mins is maj p
    · exact funext (recrSubst_index ps ms mins is maj)
  | major =>
    dsimp only [IndSig.RecrBinder.resolve, recrBinderType]
    unfold recrTele
    rw [Ctx.get_last, Expr.wk_subst]
    simp only [Expr.subst, Expr.wkN_eq_rename]
    congr 2
    · exact funext (recrSubst_param ps ms mins is maj)
    · exact funext (recrSubst_index ps ms mins is maj)

@[simp] theorem IndSig.recrBody_subst :
    (ι.recrBody s).subst
        (Inductive.recrSubst ps ms mins is maj) =
      Inductive.motiveResult (ms s) is maj := by
  simp only [recrBody, Inductive.motiveResult_subst, Expr.subst]
  exact congr(Inductive.motiveResult $(Inductive.recrSubst_motive ps ms mins is maj s)
    $(funext (Inductive.recrSubst_index ps ms mins is maj)) $(Inductive.recrSubst_major ps ms mins is maj))

open IndSig

variable {I η ls l} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
  {mins₁ mins₂ : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n}
  {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} {maj₁ maj₂ : Expr ζ ℓ n}

@[elab_as_elim]
theorem Inductive.forall_recrSubst
    {motive : Fin (ι.recrEnd s) → Expr ζ ℓ n → Expr ζ ℓ n → Expr ζ ℓ n → Prop}
    (hps : ∀ p, motive (RecrBinder.param p).resolve (ps₁ p) (ps₂ p) (I.paramType ls ps₁ p))
    (hms : ∀ t, motive (RecrBinder.motive t).resolve (ms₁ t) (ms₂ t) (I.motiveType η ls ps₁ l t))
    (hmins : ∀ t c, motive (RecrBinder.case t c).resolve (mins₁ t c) (mins₂ t c)
      (I.caseFnType η ls ps₁ ms₁ t c))
    (his : ∀ i, motive (RecrBinder.index i).resolve (is₁ i) (is₂ i) (I.indexType ls s ps₁ is₁ i))
    (hmaj : motive RecrBinder.major.resolve maj₁ maj₂ (.ind η s ls ps₁ is₁))
    (v : Fin (ι.recrEnd s)) :
    motive v (recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v) (recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v)
      ((Ctx.get v (I.recrTele η s ls l)).subst (recrSubst ps₁ ms₁ mins₁ is₁ maj₁)) := by
  obtain ⟨b, rfl⟩ := RecrBinder.resolve_surjective v
  rw [recrTele_get_subst]
  cases b with
  | param p => simpa [recrBinderType] using hps p
  | motive t => simpa [recrBinderType] using hms t
  | case t c => simpa [recrBinderType] using hmins t c
  | index i => simpa [recrBinderType] using his i
  | major => simpa [recrBinderType] using hmaj

@[elab_as_elim]
theorem Inductive.forall_recrSubst_image {motive : Expr ζ ℓ n → Prop} (hps : ∀ p, motive (ps₁ p))
    (hms : ∀ t, motive (ms₁ t)) (hmins : ∀ t c, motive (mins₁ t c)) (his : ∀ i, motive (is₁ i))
    (hmaj : motive maj₁) (v : Fin (ι.recrEnd s)) :
    motive (recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v) := by
  obtain ⟨b, rfl⟩ := RecrBinder.resolve_surjective v
  cases b with
  | param p => simpa using hps p
  | motive t => simpa using hms t
  | case t c => simpa using hmins t c
  | index i => simpa using his i
  | major => simpa using hmaj

theorem Inductive.recrSubst_comp {m : Nat} (σ : Subst ζ ℓ n m) :
    Subst.comp (recrSubst ps₁ ms₁ mins₁ is₁ maj₁) σ =
      recrSubst (fun p => (ps₁ p).subst σ) (fun t => (ms₁ t).subst σ)
        (fun t c => (mins₁ t c).subst σ) (fun i => (is₁ i).subst σ) (maj₁.subst σ) := by
  unfold recrSubst
  refine (Fin.comp_snoc (Expr.subst σ) _ _).trans ?_
  simp [Function.comp_def, Fin.append_comp]

theorem Inductive.recrSubst_vars :
    recrSubst (fun p => .var (RecrBinder.param p).resolve) (fun t => .var (RecrBinder.motive t).resolve)
      (fun t c => .var (RecrBinder.case (s := s) t c).resolve)
      (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve) =
      (Subst.id : Subst ζ ℓ (ι.recrEnd s) (ι.recrEnd s)) := by
  funext v
  obtain ⟨b, rfl⟩ := RecrBinder.resolve_surjective v
  cases b <;> simp [Subst.id]

end Metalean
