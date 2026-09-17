/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Inductive
import Metalean.Strong.InstLevel
import Metalean.Strong.Substitution
import Metalean.Strong.Telescope
import Metalean.Syntax.Structure.Projection
import Metalean.Syntax.Substitution
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}
  {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}

namespace Inductive

variable {I : Inductive ζ ι}

theorem IsStructure.projTypeWith_hasTypeStrong
    (hctor : (I.ctors s c).WFStrong E I)
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    {f : Fin (ι.ctors s c).nfields}
    {previous : Fin f.val → Expr ζ ℓ n}
    (hps : ∀ param, E[Γ] ⊢ₛ ps param :
      I.paramType ls ps param)
    (hprevious : ∀ prior, E[Γ] ⊢ₛ previous prior :
      projTypeWith I ls ps
        (prior.castLE f.isLt.le)
        fun earlier => previous
          (earlier.castLE prior.isLt.le)) :
    E[Γ] ⊢ₛ projTypeWith I ls ps f previous :
      .sort (((I.ctors s c).ordinary f).level.inst ls) := by
  have hσ := Ctor.ordinarySubstWFStrong
    (ctor := I.ctors s c) f.isLt.le hps fun prior => by
      simpa [projTypeWith] using hprevious prior
  have htype := ((hctor.ordinary f).typeExact.instLevel ls).substitution hσ
  simpa [projTypeWith, Ctor.ordinaryType,
    Expr.instL, Expr.subst] using htype

theorem IsStructure.projTypeWith_congrStrong
    (hB : I.WFStrong E) (hctor : (I.ctors s c).WFStrong E I)
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    {f : Fin (ι.ctors s c).nfields}
    {previous previous' : Fin f.val → Expr ζ ℓ n}
    (hps : ∀ param, E[Γ] ⊢ₛ ps param :
      I.paramType ls ps param)
    (hprevious : ∀ prior, E[Γ] ⊢ₛ previous prior ≡ previous' prior :
      projTypeWith I ls ps
        (prior.castLE f.isLt.le)
        fun earlier => previous
          (earlier.castLE prior.isLt.le)) :
    E[Γ] ⊢ₛ projTypeWith I ls ps f previous ≡
      projTypeWith I ls ps f previous' :
        .sort (((I.ctors s c).ordinary f).level.inst ls) := by
  have hpsEq := paramSubstEqStrong hps
  have hfieldsTele := (hctor.ordinaryTeleAuxStrong f.val f.isLt.le).instLevel
    (Q := fun _ => True) ls fun _ => trivial
  have hfullEq := SubstEqStrong.extendFamily
      (xs₁ := previous) (xs₂ := previous') hfieldsTele hpsEq fun prior => by
    rw [← Ctx.entry_instL, Ctor.ordinaryTeleAux_entry]
    simpa [projTypeWith,
      Ctor.ordinaryType] using hprevious prior
  have hsource := hB.params.append
    (by simpa using hctor.ordinaryTeleAuxStrong f.val f.isLt.le)
  have hfield := (hctor.ordinary f).typeExact.instLevel ls
  rw [Ctx.instL_append] at hfield
  have hsourceInst := hsource.instLevel (Q := fun _ => True)
    ls fun _ => trivial
  rw [Ctx.instL_append] at hsourceInst
  have hfield := hsourceInst.substitution_congr hfullEq hfield
  simpa [projTypeWith, Ctor.ordinaryType,
    Fin.append, Expr.instL, Expr.subst] using hfield

structure IsStructure.ProjectionStrong
    (E : Env ζ) (Γ : Ctx ζ ℓ 0 n)
    (h : I.IsStructure s c)
    (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (maj : Expr ζ ℓ n) : Prop where
  type : E[Γ] ⊢ₛ h.projType η ls ps f maj :
    .sort (((I.ctors s c).ordinary f).level.inst ls)
  result : E[Γ] ⊢ₛ
    Inductive.motiveResult
        (h.projectionMotives η ls ps f s) h.indices maj ≡
      h.projType η ls ps f maj :
        .sort (((I.ctors s c).ordinary f).level.inst ls)
  term : E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
    h.projType η ls ps f maj
  case : E[Γ] ⊢ₛ
      h.projectionCases η ls ps f
        (h.projectionMotives η ls ps f) s c :
    I.caseFnType η ls ps
      (h.projectionMotives η ls ps f) s c
  motive (other : Fin ι.nsorts) : E[Γ] ⊢ₛ
    h.projectionMotives η ls ps f other :
      I.motiveType η ls ps (((I.ctors s c).ordinary f).level.inst ls) other
  iota (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
      (heq : maj = .ctor η s c ls ps fds h.recursive)
      (hfields : ∀ current, E[Γ] ⊢ₛ fds current :
      projTypeWith I ls ps current fun previous =>
        fds (previous.castLE current.isLt.le)) :
    E[Γ] ⊢ₛ h.projTerm η ls ps f
        (.ctor η s c ls ps fds h.recursive) ≡
      fds f :
        h.projType η ls ps f
          (.ctor η s c ls ps fds h.recursive)

theorem IsStructure.projectionStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} {maj : Expr ζ ℓ n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ param, E[Γ] ⊢ₛ ps param :
      (E.get η).block.paramType ls ps param)
    (hmaj : E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices)
    (f : Fin (ι.ctors s c).nfields) :
    ProjectionStrong E Γ h η ls ps f maj := by
  let previous := fun previous : Fin f.val =>
    (h.projection η ls ps
      (previous.castLT (previous.isLt.trans f.isLt)) maj).2
  let u := (((E.get η).block.ctors s c).ordinary f).level.inst ls
  let ms := h.projectionMotives η ls ps f
  let mins := h.projectionCases η ls ps f ms
  have hni : ι.nindices s = 0 := by
      by_contra hne
      exact h.no_indices.elim ⟨0, Nat.pos_of_ne_zero hne⟩
  have hnr : (ι.ctors s c).nrecFields = 0 := by
      by_contra hne
      exact h.no_recursive.elim ⟨0, Nat.pos_of_ne_zero hne⟩
  have htype : E[Γ] ⊢ₛ (h.projection η ls ps f maj).1 :
        .sort ((((E.get η).block.ctors s c).ordinary f).level.inst ls) := by
      rw [projection.eq_1]
      exact projTypeWith_hasTypeStrong (I := (E.get η).block) (hB.ctors s c) hps fun prior => by
        have hprior := (projectionStrong h hB hΓ hps hmaj
          (prior.castLT (prior.isLt.trans f.isLt))).term
        unfold projType at hprior
        rw [projection.eq_1] at hprior
        exact hprior
  have hresultTermCase :
      (E[Γ] ⊢ₛ Inductive.motiveResult (ms s) h.indices maj ≡
        h.projType η ls ps f maj : .sort u) ∧
      (E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
        h.projType η ls ps f maj) ∧
      (E[Γ] ⊢ₛ mins s c :
        (E.get η).block.caseFnType η ls ps ms s c) ∧
      ∀ target, E[Γ] ⊢ₛ ms target :
        (E.get η).block.motiveType η ls ps u target := by
    have hmotTele := hB.motiveTele (η := η) (s := s) hΓ
      (by simpa using hps)
    have hΓmot := hmotTele.appendCtxWFStrong hΓ
    have hpsMot : ∀ param,
        E[Γ ++ (E.get η).block.motiveTele η ls ps s] ⊢ₛ
          (ps param).wkN (ι.nindices s + 1) :
            (E.get η).block.paramType ls
              (fun param => (ps param).wkN (ι.nindices s + 1)) param :=
      fun param => by
        have hp := (hps param).wkN
          (Δ := (E.get η).block.indexTele ls s ps)
        rw [Inductive.paramType_wkN] at hp
        have hp := hp.wk (.ind η s ls
            (fun param => (ps param).wkN (ι.nindices s))
            (fun index => .var ⟨n + index.val, by omega⟩))
        simp only [Expr.wk, Inductive.paramType_wkFrom] at hp
        change E[Γ ++ (E.get η).block.motiveTele η ls ps s] ⊢ₛ
          ((ps param).wkN (ι.nindices s)).wk :
            (E.get η).block.paramType ls
              (fun param => ((ps param).wkN (ι.nindices s)).wk) param at hp
        simpa [Expr.wkN] using hp
    have hmajMot : E[Γ ++ (E.get η).block.motiveTele η ls ps s] ⊢ₛ
        .var (Fin.last (n + ι.nindices s)) :
          .ind η s ls
            (fun param => (ps param).wkN (ι.nindices s + 1)) h.indices := by
      have hvar := hΓmot.var (Fin.last (n + ι.nindices s))
      have hind := DefeqStrong.indDF (E := E)
        (η := η) (s := s) (ls := ls)
        (ps₁ := fun param => (ps param).wkN (ι.nindices s + 1))
        (ps₂ := fun param => (ps param).wkN (ι.nindices s + 1))
        (is₁ := fun index =>
          (.var ⟨n + index.val, by omega⟩ : Expr ζ ℓ
            (n + ι.nindices s)).wk)
        (is₂ := h.indices)
        (fun param => by simpa using
          (hpsMot param).left)
        h.no_indices.elim
      rw [Inductive.motiveTele, Tele.append_snoc,
        Ctx.get_last] at hvar
      exact .defeqDF hind hvar
    have hpreviousMot (prior : Fin f.val) :
        E[Γ ++ (E.get η).block.motiveTele η ls ps s] ⊢ₛ
          (h.projection η ls
            (fun param => (ps param).wkN (ι.nindices s + 1))
            (prior.castLT (prior.isLt.trans f.isLt))
            (.var (Fin.last (n + ι.nindices s)))).2 :
          projTypeWith ((E.get η).block) ls
            (fun param => (ps param).wkN (ι.nindices s + 1))
            (prior.castLE f.isLt.le)
            (fun earlier => (h.projection η ls
              (fun param => (ps param).wkN (ι.nindices s + 1))
              ⟨earlier.val, earlier.isLt.trans
                (prior.castLE f.isLt.le).isLt⟩
              (.var (Fin.last (n + ι.nindices s)))).2) := by
        have hprior := (projectionStrong h hB hΓmot hpsMot hmajMot
          (prior.castLT (prior.isLt.trans f.isLt))).term
        unfold projType at hprior
        rw [projection.eq_1] at hprior
        exact hprior
    have htypeMot := projTypeWith_hasTypeStrong (I := (E.get η).block)
      (hB.ctors s c) hpsMot hpreviousMot
    have hmotive : E[Γ] ⊢ₛ ms s :
        (E.get η).block.motiveType η ls ps u s :=
      Ctx.lam_congrStrong hΓmot htypeMot
    have hms : ∀ target, E[Γ] ⊢ₛ ms target :
        (E.get η).block.motiveType η ls ps u target := fun target => by
      have hs := h.sort_unique target
      subst target
      exact hmotive
    have hfieldsTele := (hB.ctors s c).ordinaryFieldTele
      (η := η) hps
    have hrecFieldsTeleAux (count : Nat)
        (hcount : count ≤ (ι.ctors s c).nrecFields) :
        WFTeleStrong E (fun _ => True)
          (Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
          (((E.get η).block.ctors s c).recursiveFieldTeleAux η ls
            (fun param => (ps param).wkN (ι.ctors s c).nfields)
            (Expr.boundVars n (ι.ctors s c).nfields 0)
            count hcount) := by
      induction count with
      | zero => exact .nil
      | succ count _ => exact h.no_recursive.elim ⟨count, by omega⟩
    have hrecFieldsTele := hrecFieldsTeleAux
      (ι.ctors s c).nrecFields le_rfl
    have hfieldTele : WFTeleStrong E (fun _ => True) Γ
        (((E.get η).block.ctors s c).fieldTele η ls ps) := by
      simpa [Ctor.fieldTele, Ctor.recursiveFieldTele] using
        hfieldsTele.append hrecFieldsTele
    have hihTeleAux (count : Nat)
        (hcount : count ≤ (ι.ctors s c).nrecFields) :
        WFTeleStrong E (fun _ => True)
          (Γ ++ ((E.get η).block.ctors s c).fieldTele η ls ps)
          (((E.get η).block.ctors s c).ihTeleAux ls ps ms count hcount) := by
      induction count with
      | zero => exact .nil
      | succ count _ => exact h.no_recursive.elim ⟨count, by omega⟩
    have hihTele := hihTeleAux
      (ι.ctors s c).nrecFields le_rfl
    have hcaseTele : WFTeleStrong E (fun _ => True) Γ
        ((E.get η).block.caseTele η ls ps ms s c) := by
      simpa [Inductive.caseTele, Ctor.ihTele] using
        hfieldTele.append hihTele
    have hΓcase := hcaseTele.appendCtxWFStrong hΓ
    have hcaseParams := (Inductive.caseParams_typed (E := E) (Γ := Γ) (ls := ls)
      (ps := ps) (η := η) (s := s) (c := c) (ms := ms) ·
      (fun param => by simpa using hps param))
    have hcaseMotives := (Inductive.caseMotives_typed (E := E) (Γ := Γ) (ls := ls)
      (ps := ps) (ms := ms) (l := u) (η := η) (s := s) (c := c) ·
      (fun target => by simpa using hms target))
    have hcaseOrdinary := (hB.caseOrdinary_typed (s := s) (c := c) (ms := ms) ·
      (fun param => by simpa using hps param))
    have hcaseType := hB.caseType_hasTypeStrong hΓcase
      (fun param => by simpa using hcaseParams param)
      (fun target => by simpa using hcaseMotives target)
      (fun current => by simpa using hcaseOrdinary current)
      h.no_recursive.elim
    have hcaseIndices := fun index =>
      (hB.ctors s c).targetIndex index (by
        exact Ctor.targetSubstWFStrong hcaseParams hcaseOrdinary)
    have hcaseTarget := DefeqStrong.indDF
      (fun param => by simpa using
        (hcaseParams param).left)
      (fun index => (hcaseIndices index).left)
    have hcaseMajor := DefeqStrong.ctorDF
      (recFds₁ := (ι.ctors s c).caseRecursive)
      (recFds₂ := (ι.ctors s c).caseRecursive)
      (recFieldLevels := fun _ => .zero)
      (fun param => by simpa using
        (hcaseParams param).left)
      (fun current => by simpa using
        (hcaseOrdinary current).left)
      h.no_recursive.elim
      (fun f => by simpa using
        (hB.ctors s c).ordinaryFieldExprStrong f hcaseParams hcaseOrdinary)
      h.no_recursive.elim
      hcaseTarget
    have hΓcaseMajor : E[(Γ ++
        (E.get η).block.caseTele η ls ps ms s c).snoc
          (.ind η s ls
            ((ι.ctors s c).caseParams ps)
            (fun index => ((E.get η).block.ctors s c).targetIndex ls
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary index))] ⊢ₛ ok :=
      hΓcase.snoc ⟨_, hcaseTarget.left⟩
    have hcaseParamsMajor : ∀ param, E[(Γ ++
        (E.get η).block.caseTele η ls ps ms s c).snoc
          (.ind η s ls
            ((ι.ctors s c).caseParams ps)
            (fun index => ((E.get η).block.ctors s c).targetIndex ls
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary index))] ⊢ₛ
        ((ι.ctors s c).caseParams ps param).wk :
          (E.get η).block.paramType ls
            (fun p => ((ι.ctors s c).caseParams ps p).wk)
            param := fun param => by
      simpa [Expr.wk] using (hcaseParams param).wk (.ind η s ls
          ((ι.ctors s c).caseParams ps)
          (fun index => ((E.get η).block.ctors s c).targetIndex ls
            ((ι.ctors s c).caseParams ps)
            (ι.ctors s c).caseOrdinary index))
    have hcaseMajorVar : E[(Γ ++
        (E.get η).block.caseTele η ls ps ms s c).snoc
          (.ind η s ls
            ((ι.ctors s c).caseParams ps)
            (fun index => ((E.get η).block.ctors s c).targetIndex ls
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary index))] ⊢ₛ
        .var (Fin.last (n + (ι.ctors s c).nfields +
          (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields)) :
          .ind η s ls
            (fun param => ((ι.ctors s c).caseParams ps param).wk)
            h.indices := by
      have hvar := hΓcaseMajor.var
        (Fin.last (n + (ι.ctors s c).nfields +
          (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields))
      rw [Ctx.get_last] at hvar
      have hind := DefeqStrong.indDF (E := E)
        (η := η) (s := s) (ls := ls)
        (is₁ := fun index => (((E.get η).block.ctors s c).targetIndex ls
          ((ι.ctors s c).caseParams ps)
          (ι.ctors s c).caseOrdinary index).wk)
        (is₂ := h.indices)
        (fun param => by simpa using
          (hcaseParamsMajor param).left)
        h.no_indices.elim
      exact .defeqDF hind hvar
    have hcasePreviousMotive (prior : Fin f.val) : E[(Γ ++
        (E.get η).block.caseTele η ls ps ms s c).snoc
          (.ind η s ls
            ((ι.ctors s c).caseParams ps)
            (fun index => ((E.get η).block.ctors s c).targetIndex ls
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary index))] ⊢ₛ
        h.projTerm η ls
          (fun param => ((ι.ctors s c).caseParams ps param).wk)
          (prior.castLT (prior.isLt.trans f.isLt))
          (.var (Fin.last (n + (ι.ctors s c).nfields +
            (ι.ctors s c).nrecFields +
            (ι.ctors s c).nrecFields))) :
          projTypeWith ((E.get η).block) ls
            (fun param => ((ι.ctors s c).caseParams ps param).wk)
            (prior.castLE f.isLt.le)
            (fun earlier => h.projTerm η ls
              (fun param =>
                ((ι.ctors s c).caseParams ps param).wk)
              ⟨earlier.val, earlier.isLt.trans
                (prior.castLE f.isLt.le).isLt⟩
              (.var (Fin.last (n + (ι.ctors s c).nfields +
                (ι.ctors s c).nrecFields +
                (ι.ctors s c).nrecFields)))) := by
      have hprior := (projectionStrong h hB hΓcaseMajor
        hcaseParamsMajor hcaseMajorVar
        (prior.castLT (prior.isLt.trans f.isLt))).term
      unfold projType at hprior
      rw [projection.eq_1] at hprior
      exact hprior
    have hcaseBody := projTypeWith_hasTypeStrong (I := (E.get η).block)
      (hB.ctors s c) hcaseParamsMajor hcasePreviousMotive
    have hmotiveWk (count : Nat) :
        (ms s).wkN count =
          .lam
            (.ind η s ls
              (fun param => (ps param).wkN count) h.indices)
            (projTypeWith ((E.get η).block) ls
              (fun param => (ps param).wkN (count + 1)) f
              fun prior => h.projTerm η ls
                (fun param => (ps param).wkN (count + 1))
                (prior.castLT (prior.isLt.trans f.isLt))
                (.var (Fin.last (n + count)))) := by
      induction count with
      | zero =>
        simpa [ms, projectionMotives, Expr.wkN] using
          h.projectionMotiveLam η ls ps f
      | succ count ih =>
        rw [Expr.wkN, ih]
        change (Expr.lam _ _).wkFrom (n + count) = _
        rw [Expr.wkFrom_lam le_rfl]
        congr 1
        · rw [Expr.wkFrom_ind]
          congr 1
          exact funext h.no_indices.elim
        · rw [projTypeWith_wkFrom]
          congr 1
          · funext param
            simp [Expr.wkN, Expr.wk, Nat.add_assoc]
          · funext prior
            rw [projTerm_wkFrom]
            congr 1
            · funext param
              simp [Expr.wkN, Expr.wk, Nat.add_assoc]
            · rw [Expr.last_wkFrom
                (show n + count ≤ n + count from Nat.le_refl _)]
              congr 1
    let caseMajor : Expr ζ ℓ
        (n + (ι.ctors s c).nfields +
          (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields) := .ctor η s c ls
      ((ι.ctors s c).caseParams ps)
      (ι.ctors s c).caseOrdinary h.recursive
    have hcaseRecursive :
        ((ι.ctors s c).caseRecursive :
          Fin (ι.ctors s c).nrecFields →
            Expr ζ ℓ
              (n + (ι.ctors s c).nfields +
                (ι.ctors s c).nrecFields +
                (ι.ctors s c).nrecFields)) = h.recursive :=
      funext h.no_recursive.elim
    rw [hcaseRecursive] at hcaseMajor
    have hcaseIndices :
        ((E.get η).block.ctors s c).targetIndex ls
          ((ι.ctors s c).caseParams ps)
          (ι.ctors s c).caseOrdinary = h.indices :=
      funext h.no_indices.elim
    have hcaseMajorStruct := hcaseMajor
    rw [hcaseIndices] at hcaseMajorStruct
    let casePrevious : Fin f.val →
        Expr ζ ℓ (n + (ι.ctors s c).nfields +
          (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields) := fun prior =>
      h.projTerm η ls ((ι.ctors s c).caseParams ps)
        (prior.castLT (prior.isLt.trans f.isLt)) caseMajor
    let casePrevious' : Fin f.val →
        Expr ζ ℓ (n + (ι.ctors s c).nfields +
          (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields) := fun prior =>
      (ι.ctors s c).caseOrdinary
        (prior.castLT (prior.isLt.trans f.isLt))
    have hpreviousIota (prior : Fin f.val) : E[Γ ++
        (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
        casePrevious prior ≡ casePrevious' prior :
          projTypeWith ((E.get η).block) ls
            ((ι.ctors s c).caseParams ps)
            (prior.castLE f.isLt.le)
            (fun earlier => casePrevious
              (earlier.castLE prior.isLt.le)) := by
      have hi := (projectionStrong h hB hΓcase hcaseParams hcaseMajorStruct
        (prior.castLT (prior.isLt.trans f.isLt))).iota
        (ι.ctors s c).caseOrdinary rfl hcaseOrdinary
      unfold projType at hi
      rw [projection.eq_1] at hi
      exact hi
    have hfieldTypeEq := projTypeWith_congrStrong
      (I := (E.get η).block) (f := f) (previous := casePrevious)
      (previous' := casePrevious') hB (hB.ctors s c)
      hcaseParams hpreviousIota
    have hcaseBeta : E[Γ ++
        (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
        (E.get η).block.caseType η ls ps ms s c ≡
          projTypeWith ((E.get η).block) ls
            ((ι.ctors s c).caseParams ps) f casePrevious :
          .sort ((((E.get η).block.ctors s c).ordinary f).level.inst ls) := by
      have hresult := hcaseBody.substitution
        (SubstWFStrong.inst hΓcase
          (hcaseMajor.left))
      have hbeta := DefeqStrong.beta hcaseTarget .sortDF
        hcaseBody hcaseMajor (by simpa [Expr.inst] using
          (DefeqStrong.sortDF (E := E) (l := u)))
        hresult
      simp only [Inductive.caseType, Inductive.motiveResult]
      have hmotiveCase := congrArg
        (fun motive => (motive.wkN
          (ι.ctors s c).nrecFields).wkN
            (ι.ctors s c).nrecFields)
        (hmotiveWk (ι.ctors s c).nfields)
      let baseMotive :=
        (Expr.lam
          (.ind η s ls
            (fun param => (ps param).wkN
              (ι.ctors s c).nfields) h.indices)
          (projTypeWith ((E.get η).block) ls
            (fun param => (ps param).wkN
              ((ι.ctors s c).nfields + 1)) f
            fun prior => h.projTerm η ls
              (fun param => (ps param).wkN
                ((ι.ctors s c).nfields + 1))
              (prior.castLT (prior.isLt.trans f.isLt))
              (.var (Fin.last
                (n + (ι.ctors s c).nfields)))))
      have wkEmpty {scope : Nat} (e : Expr ζ ℓ scope) :
          (e.wkN (ι.ctors s c).nrecFields).wkN
              (ι.ctors s c).nrecFields ≍ e := by
        have hinner : e.wkN (ι.ctors s c).nrecFields ≍
            e.wkN 0 :=
          congr(@Expr.wkN $(rfl) $(rfl) $(rfl) $(rfl)
            $(heq_of_eq hnr))
        have hinner : e.wkN (ι.ctors s c).nrecFields ≍ e :=
          hinner.trans (heq_of_eq rfl)
        have houter : (e.wkN
              (ι.ctors s c).nrecFields).wkN
              (ι.ctors s c).nrecFields ≍
            (e.wkN
              (ι.ctors s c).nrecFields).wkN 0 :=
          congr(@Expr.wkN $(rfl) $(rfl) $(rfl) $(rfl)
            $(heq_of_eq hnr))
        exact houter.trans hinner
      let actualMotive :=
        Expr.lam
          (.ind η s ls
            ((ι.ctors s c).caseParams ps)
            (fun index => ((E.get η).block.ctors s c).targetIndex ls
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary index))
          (projTypeWith ((E.get η).block) ls
            (fun param => ((ι.ctors s c).caseParams ps param).wk)
            f fun prior => h.projTerm η ls
              (fun param => ((ι.ctors s c).caseParams ps param).wk)
              (prior.castLT (prior.isLt.trans f.isLt))
              (.var (Fin.last
                (n + (ι.ctors s c).nfields +
                  (ι.ctors s c).nrecFields +
                  (ι.ctors s c).nrecFields))))
      have hbaseActual : baseMotive ≍ actualMotive := by
        have hpsBase :
            (fun param => (ps param).wkN
              (ι.ctors s c).nfields) ≍
              (ι.ctors s c).caseParams ps := by
          refine Function.hfunext rfl ?_
          intro param param' hparam
          cases eq_of_heq hparam
          exact (wkEmpty ((ps param).wkN
            (ι.ctors s c).nfields)).symm
        have hisBase :
            (h.indices : Fin (ι.nindices s) →
              Expr ζ ℓ (n + (ι.ctors s c).nfields)) ≍
              (fun index => ((E.get η).block.ctors s c).targetIndex ls
                ((ι.ctors s c).caseParams ps)
                (ι.ctors s c).caseOrdinary index) := by
          refine Function.hfunext rfl ?_
          intro index
          exact h.no_indices.elim index
        have hheadBase :
            Expr.ind η s ls
                (fun param => (ps param).wkN
                  (ι.ctors s c).nfields) h.indices ≍
              Expr.ind η s ls
                ((ι.ctors s c).caseParams ps)
                (fun index => ((E.get η).block.ctors s c).targetIndex ls
                  ((ι.ctors s c).caseParams ps)
                  (ι.ctors s c).caseOrdinary index) :=
          congr(@Expr.ind $(rfl) $(rfl) $(by omega) $(rfl) $(rfl)
            $(rfl) $(rfl) $hpsBase $hisBase)
        have hbodyParams :
            (fun param => (ps param).wkN
              ((ι.ctors s c).nfields + 1)) ≍
              (fun param =>
                ((ι.ctors s c).caseParams ps param).wk) := by
          refine Function.hfunext rfl ?_
          intro param param' hparam
          cases eq_of_heq hparam
          have hp := wkEmpty ((ps param).wkN
            (ι.ctors s c).nfields)
          simpa [CtorSig.caseParams, CtorSig.fieldParams, Expr.wkN] using
            Expr.wkN_congr (by omega) hp.symm 1
        have hmajBase :
            (Expr.var (Fin.last
                (n + (ι.ctors s c).nfields)) :
              Expr ζ ℓ (n + (ι.ctors s c).nfields + 1)) ≍
              (Expr.var (Fin.last
                (n + (ι.ctors s c).nfields +
                  (ι.ctors s c).nrecFields +
                  (ι.ctors s c).nrecFields)) :
                Expr ζ ℓ
                  (n + (ι.ctors s c).nfields +
                    (ι.ctors s c).nrecFields +
                    (ι.ctors s c).nrecFields + 1)) := by
          have hv : Fin.last (n + (ι.ctors s c).nfields) ≍
              Fin.last (n + (ι.ctors s c).nfields +
                (ι.ctors s c).nrecFields +
                (ι.ctors s c).nrecFields) :=
            (Fin.heq_ext_iff (by omega)).2 (by simp [Fin.last]; omega)
          exact congr(@Expr.var $(rfl) $(rfl) $(by omega) $hv)
        have hbodyBase :
            projTypeWith ((E.get η).block) ls
                (fun param => (ps param).wkN
                  ((ι.ctors s c).nfields + 1)) f
                (fun prior => h.projTerm η ls
                  (fun param => (ps param).wkN
                    ((ι.ctors s c).nfields + 1))
                  (prior.castLT (prior.isLt.trans f.isLt))
                  (.var (Fin.last
                    (n + (ι.ctors s c).nfields)))) ≍
              projTypeWith ((E.get η).block) ls
                (fun param =>
                  ((ι.ctors s c).caseParams ps param).wk)
                f fun prior => h.projTerm η ls
                  (fun param =>
                    ((ι.ctors s c).caseParams ps param).wk)
                  (prior.castLT (prior.isLt.trans f.isLt))
                  (.var (Fin.last
                    (n + (ι.ctors s c).nfields +
                      (ι.ctors s c).nrecFields +
                      (ι.ctors s c).nrecFields))) := by
          congr 1
          · omega
          · refine Function.hfunext rfl ?_
            intro prior prior' hprior
            cases eq_of_heq hprior
            congr 1
            · omega
        exact congr(@Expr.lam $(rfl) $(rfl) $(by omega)
          $hheadBase $hbodyBase)
      have houter := wkEmpty baseMotive
      rw [hmotiveCase]
      convert hbeta using 1
      · have hmotiveExact :
            (baseMotive.wkN
                (ι.ctors s c).nrecFields).wkN
                (ι.ctors s c).nrecFields = actualMotive :=
            eq_of_heq (houter.trans hbaseActual)
        rw [hmotiveExact]
        rw [Expr.apps_eq_self_of_zero hni]
        rw [hcaseRecursive]
      · simp [casePrevious, caseMajor, Expr.inst,
          Expr.wk_subst_extend]
        congr 1
        funext prior
        rw [Expr.subst, Subst.extend_last]
      · simp [Expr.inst]
    have hcase : E[Γ] ⊢ₛ mins s c :
        (E.get η).block.caseFnType η ls ps ms s c :=
      Ctx.lam_congrStrong hΓcase
        (.defeqDF (hcaseBeta.trans hfieldTypeEq).symm
          (hcaseOrdinary f))
    have hmins : ∀ target targetCtor, E[Γ] ⊢ₛ
        mins target targetCtor :
          (E.get η).block.caseFnType η ls ps ms target targetCtor :=
      fun target targetCtor => by
        have hs := h.sort_unique target
        subst target
        have hc := h.ctor_unique targetCtor
        subst targetCtor
        exact hcase
    have hallowed : (E.get η).block.RecAllowed u := by
      simpa using h.recAllowed u
    have hresultTy := hB.motiveResult_congr
      (s := s) (ls := ls) (l := u)
      (ps₁ := ps) (ps₂ := ps)
      (ms₁ := ms) (ms₂ := ms)
      (is₁ := h.indices) (is₂ := h.indices)
      (maj₁ := maj) (maj₂ := maj) hΓ
      (fun param => by simpa using
        (hps param).left)
      (fun target => by simpa using
        (hms target).left)
      h.no_indices.elim
      (hmaj.left)
    have hrecr := DefeqStrong.recrDF
      (η := η) (s := s) (ls := ls)
      (l := u) (ps₁ := ps) (ps₂ := ps)
      (ms₁ := ms) (ms₂ := ms)
      (mins₁ := mins) (mins₂ := mins)
      (is₁ := h.indices) (is₂ := h.indices)
      (maj₁ := maj) (maj₂ := maj)
      hallowed
      (fun param => by simpa using
        (hps param).left)
      (fun target => by simpa using
        (hms target).left)
      (fun target targetCtor => by simpa using
        (hmins target targetCtor).left)
      h.no_indices.elim
      (hmaj.left) (hresultTy.left)
    have htarget := DefeqStrong.indDF (E := E)
      (η := η) (s := s) (ls := ls)
      (ps₁ := ps) (ps₂ := ps)
      (is₁ := h.indices) (is₂ := h.indices)
      (fun param => by simpa using
        (hps param).left)
      h.no_indices.elim
    have hΓmajor : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ ok :=
      hΓ.snoc ⟨_, htarget⟩
    have hpsMajor : ∀ param,
        E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ
          (ps param).wk :
            (E.get η).block.paramType ls (fun p => (ps p).wk) param :=
      fun param => by
        simpa [Expr.wk] using (hps param).wk (.ind η s ls ps h.indices)
    have hmajVar : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ
        .var (Fin.last n) :
          .ind η s ls (fun param => (ps param).wk) h.indices := by
      convert hΓmajor.var (Fin.last n) using 1
      simp only [Ctx.get_last, Expr.wk, Expr.wkFrom_ind]
      congr 1
      exact funext h.no_indices.elim
    have hpreviousMajor (prior : Fin f.val) :
        E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ
          h.projTerm η ls (fun param => (ps param).wk)
            (prior.castLT (prior.isLt.trans f.isLt))
            (.var (Fin.last n)) :
          projTypeWith ((E.get η).block) ls (fun param => (ps param).wk)
            (prior.castLE f.isLt.le) fun earlier =>
              h.projTerm η ls (fun param => (ps param).wk)
                ⟨earlier.val, earlier.isLt.trans
                  (prior.castLE f.isLt.le).isLt⟩
                (.var (Fin.last n)) := by
      have hp := (projectionStrong h hB hΓmajor hpsMajor hmajVar
        (prior.castLT (prior.isLt.trans f.isLt))).term
      unfold projType at hp
      rw [projection.eq_1] at hp
      exact hp
    have hbodyMajor := projTypeWith_hasTypeStrong (I := (E.get η).block)
      (hB.ctors s c) hpsMajor hpreviousMajor
    have hresultBeta : E[Γ] ⊢ₛ
        Inductive.motiveResult (ms s) h.indices maj ≡
          projTypeWith ((E.get η).block) ls ps f previous : .sort u := by
      have hresult := hbodyMajor.substitution
        (SubstWFStrong.inst hΓ
          (hmaj.left))
      have hbeta := DefeqStrong.beta htarget .sortDF
        hbodyMajor hmaj (by simpa [Expr.inst] using
          (DefeqStrong.sortDF (E := E) (l := u)))
        hresult
      have hmotiveZero := hmotiveWk 0
      simp [Expr.wkN] at hmotiveZero
      simp only [Inductive.motiveResult]
      rw [hmotiveZero]
      convert hbeta using 1
      · rw [Expr.apps_eq_self_of_zero hni]
      · simp [previous, IsStructure.projTerm, Expr.inst,
          Expr.wk_subst_extend]
        congr 1
        funext prior
        have hs := congrArg Prod.snd
          (h.projection_subst η ls
            (fun param => (ps param).wk)
            (prior.castLT (prior.isLt.trans f.isLt))
            (.var (Fin.last n))
            ((Subst.id : Subst ζ ℓ n n).extend maj))
        simpa! [Expr.wk_subst_extend] using hs.symm
      · simp [u, Expr.inst]
    have hterm : E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
        h.projType η ls ps f maj := by
      unfold IsStructure.projTerm IsStructure.projType
      rw [projection.eq_1]
      exact .defeqDF hresultBeta hrecr
    have hresult : E[Γ] ⊢ₛ
        Inductive.motiveResult (ms s) h.indices maj ≡
          h.projType η ls ps f maj : .sort u := by
      unfold IsStructure.projType
      rw [projection]
      exact hresultBeta
    exact ⟨hresult, hterm, hcase, hms⟩
  have ⟨hresult, hterm, hcase, hms⟩ := hresultTermCase
  refine ProjectionStrong.mk htype hresult hterm hcase hms ?_
  · intro fds heq hfields
    subst maj
    have htargetIndices :
        (fun index => ((E.get η).block.ctors s c).targetIndex ls ps fds index) =
          h.indices :=
      funext h.no_indices.elim
    have htypeIota : E[Γ] ⊢ₛ
        (E.get η).block.iotaType η ls ps ms s c fds h.recursive ≡
          h.projType η ls ps f
            (.ctor η s c ls ps fds h.recursive) :
          .sort u := by
      simpa [Inductive.iotaType, htargetIndices] using
        hresultTermCase.1
    have hlhs : E[Γ] ⊢ₛ
        (E.get η).block.iotaLhs η ls u ps ms mins s c
            fds h.recursive ≡
          (E.get η).block.iotaLhs η ls u ps ms mins s c
            fds h.recursive :
          (E.get η).block.iotaType η ls ps ms s c fds h.recursive := by
      have ht := DefeqStrong.defeqDF htypeIota.symm
        (hresultTermCase.2.1.left)
      unfold IsStructure.projTerm at ht
      rw [projection.eq_1] at ht
      rw [← htargetIndices] at ht
      change E[Γ] ⊢ₛ
        (E.get η).block.iotaLhs η ls u ps ms mins s c
            fds h.recursive ≡
          (E.get η).block.iotaLhs η ls u ps ms mins s c
            fds h.recursive :
          (E.get η).block.iotaType η ls ps ms s c fds h.recursive at ht
      exact ht
    have hfieldsTele' := (hB.ctors s c).ordinaryFieldTele
      (η := η) hps
    have hbody : E[Γ ++
        ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps] ⊢ₛ
        Expr.boundVars n (ι.ctors s c).nfields 0 f :
          projTypeWith ((E.get η).block) ls
            (fun param => (ps param).wkN
              (ι.ctors s c).nfields) f
            (fun previous => Expr.boundVars n
              (ι.ctors s c).nfields 0
              (previous.castLE f.isLt.le)) := by
      have hv := (hB.ctors s c).boundOrdinarySubstWFStrong
        (η := η) hps
          (Fin.natAdd ι.nparams f)
      rw [Ctx.get_subst _ _ _ _ (by omega) rfl] at hv
      rw [← Ctx.entry_instL] at hv
      have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
        simp
      rw [Ctx.entry_append_right (E.get η).block.params _ (by omega) hb (by omega)] at hv
      simpa [Ctor.ordinaryTele,
        CtorSig.fieldOrdinary, Expr.boundVars, projTypeWith,
        Ctor.ordinaryType] using hv
    have hcaseBeta := Ctx.lam_applyFamilyStrong (xs := fds)
      hΓ hfieldsTele' (fun current => by
        unfold Ctor.ordinaryFieldTele Ctor.ordinaryFieldTeleAux
        rw [Ctx.entry_substN ps _ _ current.val
          (by omega) (by omega) (by omega) (by omega), ← Ctx.entry_instL,
          Ctor.ordinaryTeleAux_entry]
        rw [Expr.subst_subst, Subst.liftN_comp_append]
        simpa [projTypeWith,
          Ctor.ordinaryType] using
            hfields current) hbody
    have hcaseBeta' : E[Γ] ⊢ₛ
        (E.get η).block.iotaRhs η ls u ps ms mins s c
            fds h.recursive ≡ fds f :
          projTypeWith ((E.get η).block) ls ps f fun previous =>
            fds (previous.castLE f.isLt.le) := by
      have hcaseTerm : mins s c =
          Ctx.lam (Expr.boundVars n (ι.ctors s c).nfields 0 f)
            (((E.get η).block.ctors s c).ordinaryFieldTele η ls ps) := by
        change Ctx.lam ((ι.ctors s c).caseOrdinary f)
            ((E.get η).block.caseTele η ls ps ms s c) = _
        exact eq_of_heq (congr(@Ctx.lam $(rfl) $(rfl) $(by omega) $(rfl)
          $(h.caseOrdinaryField f)
          $(h.caseTeleOrdinary η ls ps ms)))
      unfold Inductive.iotaRhs
      rw [hcaseTerm]
      rw [Expr.apps_eq_self_of_zero hnr,
        Expr.apps_eq_self_of_zero hnr]
      simpa [Inductive.iotaIHs,
        mins, projectionCases, Inductive.caseTele,
        Ctor.fieldTele, Ctor.recursiveFieldTele,
        Ctor.recursiveFieldTeleAux, Ctor.ihTele,
        Ctor.ihTeleAux, CtorSig.caseOrdinary,
        CtorSig.fieldOrdinary, Expr.boundVars, Expr.subst] using hcaseBeta
    have hpreviousIota (prior : Fin f.val) : E[Γ] ⊢ₛ
        h.projTerm η ls ps (prior.castLE f.isLt.le)
            (.ctor η s c ls ps fds h.recursive) ≡
          fds (prior.castLE f.isLt.le) :
        projTypeWith ((E.get η).block) ls ps
          (prior.castLE f.isLt.le) fun earlier =>
            h.projTerm η ls ps
              (earlier.castLT (earlier.isLt.trans
                (prior.isLt.trans f.isLt)))
              (.ctor η s c ls ps fds h.recursive) := by
      have hp := (projectionStrong h hB hΓ hps hmaj
        (prior.castLE f.isLt.le)).iota fds rfl hfields
      unfold IsStructure.projType at hp
      rw [projection.eq_1] at hp
      exact hp
    have hfieldTypeEq := IsStructure.projTypeWith_congrStrong
      (I := (E.get η).block) hB (hB.ctors s c) hps hpreviousIota
    have htypeIota' := htypeIota
    unfold IsStructure.projType at htypeIota'
    rw [projection.eq_1] at htypeIota'
    have htypeToOrd := htypeIota'.trans hfieldTypeEq
    have hrhs := DefeqStrong.defeqDF htypeToOrd.symm
      (hcaseBeta'.left)
    have hiota : E[Γ] ⊢ₛ
        (E.get η).block.iotaLhs η ls u ps ms mins s c
            fds h.recursive ≡
          (E.get η).block.iotaRhs η ls u ps ms mins s c
            fds h.recursive :
          (E.get η).block.iotaType η ls ps ms s c
            fds h.recursive := by
      exact
        DefeqStrong.iota (E := E) (η := η) (by simpa using h.recAllowed u)
          (fun p => by simpa using hps p)
          (fun target => by simpa using hms target)
          (fun target targetCtor => by
            have hs := h.sort_unique target
            subst target
            have hc := h.ctor_unique targetCtor
            subst targetCtor
            simpa using hcase)
          (fun current => by
            simpa [projTypeWith, Ctor.ordinaryType] using
              hfields current)
          h.no_recursive.elim
          htypeToOrd.left
          hlhs hrhs
    unfold IsStructure.projTerm
    rw [projection.eq_1]
    rw [← htargetIndices]
    change E[Γ] ⊢ₛ
      (E.get η).block.iotaLhs η ls u ps ms mins s c
          fds h.recursive ≡ fds f :
        h.projType η ls ps f
          (.ctor η s c ls ps fds h.recursive)
    exact DefeqStrong.defeqDF htypeIota
      (hiota.trans (.defeqDF htypeToOrd.symm hcaseBeta'))
termination_by f.val

theorem IsStructure.projTerm_hasTypeStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} {maj : Expr ζ ℓ n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
      h.projType η ls ps f maj :=
  fun hΓ hps hmaj => (h.projectionStrong hB hΓ hps hmaj f).term

theorem IsStructure.projType_hasTypeStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} {maj : Expr ζ ℓ n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.projType η ls ps f maj :
      .sort ((((E.get η).block.ctors s c).ordinary f).level.inst ls) :=
  fun hΓ hps hmaj => (h.projectionStrong hB hΓ hps hmaj f).type

theorem IsStructure.indTypeStrong
    (h : (E.get η).block.IsStructure s c)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n} :
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ] ⊢ₛ (.ind η s ls ps h.indices : Expr ζ ℓ n) :
      .sort ((E.get η).block.level.inst ls) :=
  fun hps =>
    .indDF hps
      h.no_indices.elim

theorem IsStructure.projTerm_genericStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ
      h.projTerm η ls (fun param => (ps param).wk) f (.var (Fin.last n)) :
      h.projType η ls (fun param => (ps param).wk) f (.var (Fin.last n)) :=
  fun hΓ hps =>
    have hΓ' : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ ok :=
      hΓ.snoc ⟨_, h.indTypeStrong hps⟩
    have hpswk (param : Fin ι.nparams) :
        E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ (ps param).wk :
          (E.get η).block.paramType ls (fun p => (ps p).wk) param := by
      simpa [Expr.wk] using (hps param).wk (.ind η s ls ps h.indices)
    have hvar : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ .var (Fin.last n) :
        .ind η s ls (fun p => (ps p).wk) h.indices := by
      have hwkidx : (fun index => Expr.wkFrom n (h.indices (α := Expr ζ ℓ n) index)) =
          h.indices := funext h.no_indices.elim
      have hv := hΓ'.var (Fin.last n)
      rw [Ctx.get_last, Expr.wk, Expr.wkFrom_ind, hwkidx] at hv
      exact hv
    h.projTerm_hasTypeStrong hB f hΓ' hpswk hvar

theorem IsStructure.projTerm_substCongrStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n m : Nat} {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ 0 m}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    {β₁ β₂ : Subst ζ ℓ n m} {maj₁ maj₂ : Expr ζ ℓ m}
    (f : Fin (ι.ctors s c).nfields) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Δ] ⊢ₛ β₁ ≡ β₂ ⊣ Γ →
    E[Δ] ⊢ₛ maj₁ ≡ maj₂ :
      .ind η s ls (fun param => (ps param).subst β₁) h.indices →
    E[Δ] ⊢ₛ h.projTerm η ls (fun param => (ps param).subst β₁) f maj₁ ≡
      h.projTerm η ls (fun param => (ps param).subst β₂) f maj₂ :
      h.projType η ls (fun param => (ps param).subst β₁) f maj₁ := by
  intro hΓ hps hβ hmaj
  have hidx {α : Sort _} (g : Fin (ι.nindices s) → α) : g = h.indices :=
    funext h.no_indices.elim
  have hΓ' : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ ok :=
    hΓ.snoc ⟨_, h.indTypeStrong hps⟩
  have hterm := h.projTerm_genericStrong hB f hΓ hps
  have hξ : E[Δ] ⊢ₛ β₁.extend maj₁ ≡ β₂.extend maj₂ ⊣ Γ.snoc (.ind η s ls ps h.indices) := by
    have hsubidx : (fun index => Expr.subst β₁ (h.indices (α := Expr ζ ℓ n) index)) =
        h.indices := hidx _
    refine hβ.extend ?_
    rw [Expr.subst, hsubidx]
    exact hmaj
  have hcongr := DefeqStrong.substitution_congr hΓ' hξ hterm
  simpa [Expr.wk_subst_extend,
    show Expr.subst (β₁.extend maj₁) (Expr.var (Fin.last n)) = maj₁ from Subst.extend_last _ _,
    show Expr.subst (β₂.extend maj₂) (Expr.var (Fin.last n)) = maj₂ from
      Subst.extend_last _ _] using hcongr

theorem IsStructure.projTerm_congrStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {maj₁ maj₂ : Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields) :
    (∀ param, E[Γ] ⊢ₛ ps₁ param ≡ ps₂ param : (E.get η).block.paramType ls ps₁ param) →
    E[Γ] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ h.indices →
    E[Γ] ⊢ₛ h.projTerm η ls ps₁ f maj₁ ≡ h.projTerm η ls ps₂ f maj₂ :
      h.projType η ls ps₁ f maj₁ := by
  intro hps hmaj
  have hparams := hB.params.instLevel (Q := fun _ : Level ℓ => True) ls fun _ => trivial
  have hΓ₀ : E[Ctx.instL ls (E.get η).block.params] ⊢ₛ ok := by
    simpa [Ctx.instL] using hparams.appendCtxWFStrong (Γ := .nil) .nil
  have hgeneric : ∀ param : Fin ι.nparams,
      E[Ctx.instL ls (E.get η).block.params] ⊢ₛ Expr.var param :
        (E.get η).block.paramType ls (Subst.id : Subst ζ ℓ ι.nparams ι.nparams) param := by
    intro param
    have hvar := hΓ₀.var param
    rw [← Ctx.get_instL] at hvar
    rw [← Inductive.paramType_eq_get_subst, Expr.subst_id]
    exact hvar
  exact h.projTerm_substCongrStrong hB
    (ls := ls) (ps := (Subst.id : Subst ζ ℓ ι.nparams ι.nparams))
    (β₁ := ps₁) (β₂ := ps₂) f hΓ₀ hgeneric (Inductive.paramSubstEqStrong hps) hmaj

theorem IsStructure.projType_congrStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {maj₁ maj₂ : Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields) :
    (∀ param, E[Γ] ⊢ₛ ps₁ param ≡ ps₂ param : (E.get η).block.paramType ls ps₁ param) →
    E[Γ] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ h.indices →
    E[Γ] ⊢ₛ h.projType η ls ps₁ f maj₁ ≡ h.projType η ls ps₂ f maj₂ typ := by
  intro hps hmaj
  have hfields : ∀ current : Fin (ι.ctors s c).nfields,
      E[Γ] ⊢ₛ h.projTerm η ls ps₁ current maj₁ ≡ h.projTerm η ls ps₂ current maj₂ :
        ((((E.get η).block.ctors s c).ordinaryType current).instL ls).subst
          (Fin.append ps₁ fun prior : Fin current.val =>
            h.projTerm η ls ps₁ (prior.castLE current.isLt.le) maj₁) := by
    intro current
    have hcongr := h.projTerm_congrStrong hB current hps hmaj
    rwa [IsStructure.projType_eq, Ctor.ordinaryFieldExpr] at hcongr
  have ⟨_, heq⟩ := (hB.ctors s c).ordinaryFieldExpr_congr hB.params f
    hps hfields
  rw [IsStructure.projType_eq, IsStructure.projType_eq]
  exact .ofDefEq heq

theorem IsStructure.rebuildTerm_hasTypeStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} {maj : Expr ζ ℓ n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.rebuildTerm η ls ps maj : .ind η s ls ps is := by
  intro hΓ hps hmaj
  have hfields : ∀ f, E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
      ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          h.projTerm η ls ps
            (previous.castLE f.isLt.le) maj) := by
    intro f
    have hf := h.projTerm_hasTypeStrong hB f hΓ hps hmaj
    unfold IsStructure.projType at hf
    rw [projection.eq_1] at hf
    exact hf
  have hrebuild := DefeqStrong.ctorDF
    (ps₂ := ps)
    (fds₂ := fun f => h.projTerm η ls ps f maj)
    (recFds₁ := h.recursive) (recFds₂ := h.recursive)
    (recFieldLevels := h.no_recursive.elim)
    hps hfields
    h.no_recursive.elim
    (fun f => (hB.ctors s c).ordinaryFieldExprStrong f hps hfields)
    h.no_recursive.elim
    (DefeqStrong.indDF hps
      h.no_indices.elim)
  have hindices : ((E.get η).block.ctors s c).targetIndex ls ps
      (fun f => h.projTerm η ls ps f maj) = is :=
    funext h.no_indices.elim
  rw [hindices] at hrebuild
  exact hrebuild

theorem IsStructure.projTerm_ctorStrong
    (h : (E.get η).block.IsStructure s c)
    (hB : (E.get η).block.WFStrong E)
    {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    (f : Fin (ι.ctors s c).nfields)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ ps param : (E.get η).block.paramType ls ps param) →
    E[Γ] ⊢ₛ .ctor η s c ls ps fds h.recursive :
      .ind η s ls ps h.indices →
    (∀ current, E[Γ] ⊢ₛ fds current :
      projTypeWith ((E.get η).block) ls ps current fun previous =>
        fds (previous.castLE current.isLt.le)) →
    E[Γ] ⊢ₛ h.projTerm η ls ps f
        (.ctor η s c ls ps fds h.recursive) ≡
      fds f :
        h.projType η ls ps f
          (.ctor η s c ls ps fds h.recursive) :=
  fun hΓ hps hmaj hfields => (h.projectionStrong hB hΓ hps hmaj f).iota
    fds rfl hfields

end Inductive

end Metalean
