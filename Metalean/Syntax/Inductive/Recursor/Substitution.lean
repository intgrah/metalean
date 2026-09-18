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
        index).castSucc = is index := by
  simp only [Inductive.recrSubst]
  rw [Fin.snoc_castSucc, Fin.append_right]

@[simp] theorem Inductive.recrSubst_major :
    Inductive.recrSubst ps ms mins is maj
      (Fin.last (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
        ι.nindices s)) = maj := by
  simp [Inductive.recrSubst]

@[simp] theorem Inductive.recrSubst_resolve_motive (t : Fin ι.nsorts) :
    Inductive.recrSubst ps ms mins is maj
      (IndSig.RecrBinder.motive (s := s) t).resolve = ms t := by
  rw [IndSig.RecrBinder.resolve_motive_eq, Inductive.recrSubst_motive]

@[simp] theorem Inductive.recrSubst_resolve_index (index : Fin (ι.nindices s)) :
    Inductive.recrSubst ps ms mins is maj
      (IndSig.RecrBinder.index index).resolve = is index := by
  rw [IndSig.RecrBinder.resolve_index_eq, Inductive.recrSubst_index]

@[simp] theorem Inductive.recrSubst_resolve_major :
    Inductive.recrSubst ps ms mins is maj
      (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve = maj :=
  Inductive.recrSubst_major ps ms mins is maj

@[simp] theorem Inductive.recrTele_get_param_subst (param : Fin ι.nparams) :
    (Ctx.get
      (((param.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)).castAdd
        (ι.nindices s)).castSucc
      (I.recrTele η s ls l)).subst
      (Inductive.recrSubst ps ms mins is maj) =
      I.paramType ls ps param := by
  unfold recrTele
  simp [Expr.wk_subst, Expr.wkN_eq_subst, Expr.subst, Ren.wkN]

@[simp] theorem Inductive.recrTele_get_motive_subst (s₁ : Fin ι.nsorts) :
    (Ctx.get
      (((Fin.natAdd ι.nparams s₁).castAdd
        (Fin.sum ι.nctors)).castAdd (ι.nindices s)).castSucc
      (I.recrTele η s ls l)).subst
        (Inductive.recrSubst ps ms mins is maj) =
      I.motiveType η ls ps l s₁ := by
  unfold recrTele
  simp [motiveBinders, Expr.wk_subst, Expr.wkN_eq_subst, Expr.subst, Ren.wkN]

@[simp] theorem Inductive.recrTele_get_case_subst (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    (Ctx.get
      ((Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)).castAdd
        (ι.nindices s)).castSucc
      (I.recrTele η s ls l)).subst
        (Inductive.recrSubst ps ms mins is maj) =
      I.caseFnType η ls ps ms s₁ c := by
  unfold recrTele
  rw [Ctx.get_snoc _ _ _ (Nat.ne_of_lt
    ((Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)).castAdd
      (ι.nindices s)).isLt),
    Fin.castLT_castSucc, Ctx.get_append, caseBinders, Ctx.get_append_ofTypes,
    Fin.decodeSigma_encodeSigma]
  simp [Expr.wk_subst, Expr.wkN_eq_subst, Expr.subst, Ren.wkN]

@[simp] theorem Inductive.recrTele_get_index_subst (index : Fin (ι.nindices s)) :
    (Ctx.get
      (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
        index).castSucc
      (I.recrTele η s ls l)).subst
        (Inductive.recrSubst ps ms mins is maj) =
      I.indexType ls s ps is index := by
  unfold recrTele
  rw [
    Ctx.get_snoc _ _ _ (Nat.ne_of_lt (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index).isLt),
    Expr.wk_subst, Fin.castLT_castSucc, Fin.natAdd_mk, I.indexTele_get]
  simp only [Inductive.indexType_subst]
  congr 2
  · funext param
    simp
    calc
      _ = Inductive.recrSubst ps ms mins is maj
          (((param.castAdd ι.nsorts).castAdd
            (Fin.sum ι.nctors)).castAdd
            (ι.nindices s)).castSucc := rfl
      _ = ps param := by simp
  · funext previous
    calc
      _ = Inductive.recrSubst ps ms mins is maj
          (Fin.natAdd
            (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
            previous).castSucc := rfl
      _ = is previous := by
        simp only [Inductive.recrSubst, Fin.snoc_castSucc,
          Fin.append_right]

@[simp] theorem Inductive.recrTele_get_index_succ_subst (index : Fin (ι.nindices s)) :
    (Ctx.get
      (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
        index.castSucc)
      (I.recrTele η s ls l)).subst
        (Inductive.recrSubst ps ms mins is maj) =
      I.indexType ls s ps is index := by
  have hposition : Fin.natAdd
      (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index.castSucc =
      (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
        index).castSucc := rfl
  rw [hposition, I.recrTele_get_index_subst]

@[simp] theorem Inductive.recrTele_get_major_subst :
    (Ctx.get
      (Fin.last (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
        ι.nindices s))
      (I.recrTele η s ls l)).subst
        (Inductive.recrSubst ps ms mins is maj) =
      .ind η s ls ps is := by
  unfold recrTele
  rw [Ctx.get_last, Expr.wk_subst]
  simp only [Expr.subst, Expr.wkN_eq_rename]
  congr 2
  · funext param
    calc
      _ = Inductive.recrSubst ps ms mins is maj
          (((param.castAdd ι.nsorts).castAdd
            (Fin.sum ι.nctors)).castAdd
            (ι.nindices s)).castSucc := rfl
      _ = ps param := by simp
  · funext index
    let expected := (Fin.natAdd
      (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index).castSucc
    have hexpected :
        Inductive.recrSubst ps ms mins is maj expected =
          is index := by
      simp only [expected, Inductive.recrSubst, Fin.snoc_castSucc,
        Fin.append_right]
    exact (congrArg
      (Inductive.recrSubst ps ms mins is maj)
      (show (⟨ι.nparams + ι.nsorts + Fin.sum ι.nctors + index.val,
          by omega⟩ : Fin
          (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
            ι.nindices s + 1)) = expected from rfl)).trans
      hexpected

@[simp] theorem IndSig.recrBody_subst :
    (ι.recrBody s).subst
        (Inductive.recrSubst ps ms mins is maj) =
      Inductive.motiveResult (ms s) is maj := by
  simp [recrBody, Expr.subst]

section

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
  cases v using Fin.lastCases with
  | last =>
    rw [recrSubst_major, recrSubst_major, recrTele_get_major_subst]
    exact hmaj
  | cast v =>
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases with
        | left p =>
          rw [recrSubst_param, recrSubst_param, recrTele_get_param_subst]
          exact hps p
        | right t =>
          rw [recrSubst_motive, recrSubst_motive, recrTele_get_motive_subst]
          exact hms t
      | right tag =>
        obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
          ⟨_, Fin.encodeSigma_decodeSigma ..⟩
        rw [recrSubst_case, recrSubst_case, recrTele_get_case_subst]
        exact hmins t c
    | right i =>
      rw [recrSubst_index, recrSubst_index, recrTele_get_index_subst]
      exact his i

@[elab_as_elim]
theorem Inductive.forall_recrSubst_image {motive : Expr ζ ℓ n → Prop} (hps : ∀ p, motive (ps₁ p))
    (hms : ∀ t, motive (ms₁ t)) (hmins : ∀ t c, motive (mins₁ t c)) (his : ∀ i, motive (is₁ i))
    (hmaj : motive maj₁) (v : Fin (ι.recrEnd s)) :
    motive (recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v) := by
  cases v using Fin.lastCases with
  | last =>
    rw [recrSubst_major]
    exact hmaj
  | cast v =>
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases with
        | left p =>
          rw [recrSubst_param]
          exact hps p
        | right t =>
          rw [recrSubst_motive]
          exact hms t
      | right tag =>
        obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
          ⟨_, Fin.encodeSigma_decodeSigma ..⟩
        rw [recrSubst_case]
        exact hmins t c
    | right i =>
      rw [recrSubst_index]
      exact his i

@[simp] theorem Inductive.recrSubst_resolve_param (p : Fin ι.nparams) :
    recrSubst ps₁ ms₁ mins₁ is₁ maj₁ (RecrBinder.param (s := s) p).resolve = ps₁ p :=
  recrSubst_param ..

@[simp] theorem Inductive.recrSubst_resolve_case (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) :
    recrSubst ps₁ ms₁ mins₁ is₁ maj₁ (RecrBinder.case (s := s) t c).resolve = mins₁ t c :=
  recrSubst_case ..

theorem Inductive.recrSubst_comp {m : Nat} (σ : Subst ζ ℓ n m) :
    Subst.comp (recrSubst ps₁ ms₁ mins₁ is₁ maj₁) σ =
      recrSubst (fun p => (ps₁ p).subst σ) (fun t => (ms₁ t).subst σ)
        (fun t c => (mins₁ t c).subst σ) (fun i => (is₁ i).subst σ) (maj₁.subst σ) := by
  funext v
  cases v using Fin.lastCases with
  | last => simp [Subst.comp]
  | cast v =>
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases with
        | left p => simp [Subst.comp]
        | right t => simp [Subst.comp]
      | right tag =>
        obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
          ⟨_, Fin.encodeSigma_decodeSigma ..⟩
        simp [Subst.comp]
    | right i => rw [Subst.comp, recrSubst_index, recrSubst_index]

theorem Inductive.recrSubst_vars :
    recrSubst (fun p => .var (RecrBinder.param p).resolve) (fun t => .var (RecrBinder.motive t).resolve)
      (fun t c => .var (RecrBinder.case (s := s) t c).resolve)
      (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve) =
      (Subst.id : Subst ζ ℓ (ι.recrEnd s) (ι.recrEnd s)) := by
  funext v
  cases v using Fin.lastCases with
  | last => exact recrSubst_major ..
  | cast v =>
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases with
        | left p => exact recrSubst_param ..
        | right t => exact recrSubst_motive ..
      | right tag =>
        obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
          ⟨_, Fin.encodeSigma_decodeSigma ..⟩
        exact recrSubst_case ..
    | right i => exact recrSubst_index ..

end

end Metalean
