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

namespace Metalean.Inductive.IsStructure

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}
  {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {I : Inductive ζ ι} {ls : Fin ι.nlevels → Level ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {maj maj₁ maj₂ : Expr ζ ℓ n}

theorem projTypeWith_hasTypeStrong
    (hctor : (I.ctors s c).WFStrong E I)
    {f : Fin (ι.ctors s c).nfields}
    {previous : Fin f.val → Expr ζ ℓ n}
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p)
    (hprevious : ∀ prior, E[Γ] ⊢ₛ previous prior :
      projTypeWith I ls ps
        (prior.castLE f.isLt.le)
        fun earlier => previous
          (earlier.castLE prior.isLt.le)) :
    E[Γ] ⊢ₛ projTypeWith I ls ps f previous :
      .sort (((I.ctors s c).ordinary f).level.inst ls) := by
  have hσ := Ctor.forall_ordinarySubst
    f.isLt.le hps fun prior => by
      simpa [projTypeWith] using hprevious prior
  have htype := ((hctor.ordinary f).typeExact.instLevel ls).substitution hσ
  simpa [projTypeWith, Expr.instL] using htype

theorem projTypeWith_congrStrong
    (hB : I.WFStrong E) (hctor : (I.ctors s c).WFStrong E I)
    {f : Fin (ι.ctors s c).nfields}
    {previous previous' : Fin f.val → Expr ζ ℓ n}
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p)
    (hprevious : ∀ prior, E[Γ] ⊢ₛ previous prior ≡ previous' prior :
      projTypeWith I ls ps
        (prior.castLE f.isLt.le)
        fun earlier => previous
          (earlier.castLE prior.isLt.le)) :
    E[Γ] ⊢ₛ projTypeWith I ls ps f previous ≡
      projTypeWith I ls ps f previous' :
        .sort (((I.ctors s c).ordinary f).level.inst ls) := by
  have hpsEq := paramSubstEqStrong hps
  have hfieldsTele := (hctor.ordinaryTeleAux f.val f.isLt.le).instLevel
    (Q := fun _ => True) ls fun _ => trivial
  have hfullEq := SubstEqStrong.extendFamily
      hfieldsTele hpsEq fun prior => by
    rw [← Ctx.entry_instL]
    simpa [projTypeWith] using hprevious prior
  have hsource := hB.params.append
    (by simpa using (hctor.ordinaryTeleAux f.val f.isLt.le).mono fun _ => trivial)
  have hfield := (hctor.ordinary f).typeExact.instLevel ls
  rw [Ctx.instL_append] at hfield
  have hsourceInst := hsource.instLevel (Q := fun _ => True)
    ls fun _ => trivial
  rw [Ctx.instL_append] at hsourceInst
  have hfield := hsourceInst.substitution_congr hfullEq hfield
  simpa [projTypeWith, Expr.instL] using hfield

structure ProjectionStrong
    (E : Env ζ) (Γ : Ctx ζ ℓ 0 n)
    (h : I.IsStructure s c)
    (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (f : Fin (ι.ctors s c).nfields)
    (maj : Expr ζ ℓ n) : Prop where
  type : E[Γ] ⊢ₛ h.projType η ls ps f maj :
    .sort (((I.ctors s c).ordinary f).level.inst ls)
  result : E[Γ] ⊢ₛ Inductive.motiveResult
        (h.projectionMotives η ls ps f s) h.indices maj ≡
      h.projType η ls ps f maj :
        .sort (((I.ctors s c).ordinary f).level.inst ls)
  term : E[Γ] ⊢ₛ h.projTerm η ls ps f maj : h.projType η ls ps f maj
  case : E[Γ] ⊢ₛ h.projectionCases η ls ps f
        (h.projectionMotives η ls ps f) s c :
    I.caseFnType η ls ps
      (h.projectionMotives η ls ps f) s c
  motive (other : Fin ι.nsorts) : E[Γ] ⊢ₛ h.projectionMotives η ls ps f other :
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

variable (h : (E.get η).block.IsStructure s c)
  (hB : (E.get η).block.WFStrong E)
  (f : Fin (ι.ctors s c).nfields)

include h

theorem indices_eq {α : Sort _} (g : Fin (ι.nindices s) → α) : g = h.indices :=
  funext h.no_indices.elim

theorem recursive_eq {α : Sort _} (g : Fin (ι.ctors s c).nrecFields → α) :
    g = h.recursive :=
  funext h.no_recursive.elim

theorem indTypeStrong :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ (.ind η s ls ps h.indices : Expr ζ ℓ n) :
      .sort ((E.get η).block.level.inst ls) :=
  fun hps => .indDF hps h.no_indices.elim

theorem wkParams
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (p : Fin ι.nparams) :
    E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ (ps p).wk :
      (E.get η).block.paramType ls (fun p => (ps p).wk) p := by
  simpa [Expr.wk] using (hps p).wk (.ind η s ls ps h.indices)

theorem varMajor (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) :
    E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ .var (Fin.last n) :
      .ind η s ls (fun p => (ps p).wk) h.indices := by
  have hΓ' : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ ok :=
    hΓ.snoc ⟨_, h.indTypeStrong hps⟩
  have hv := hΓ'.var (Fin.last n)
  rw [Ctx.get_last, Expr.wk, Expr.wkFrom_ind,
    h.indices_eq fun i => Expr.wkFrom n (h.indices i)] at hv
  exact hv

include hB

theorem projectionStrong
    {n : Nat} {Γ : Ctx ζ ℓ 0 n} {ps : Fin ι.nparams → Expr ζ ℓ n}
    {maj : Expr ζ ℓ n}
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (hmaj : E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices)
    (f : Fin (ι.ctors s c).nfields) :
    ProjectionStrong E Γ h η ls ps f maj := by
  have hni := Fin.eq_zero_of_isEmpty h.no_indices
  have hnr := Fin.eq_zero_of_isEmpty h.no_recursive
  let u := (((E.get η).block.ctors s c).ordinary f).level.inst ls
  let ms := h.projectionMotives η ls ps f
  let mins := h.projectionCases η ls ps f ms
  have hmsDef : ms = h.projectionMotives η ls ps f := rfl
  have hminsDef : mins = h.projectionCases η ls ps f ms := rfl
  have hbody {m : Nat} {Δ : Ctx ζ ℓ 0 m} {qs : Fin ι.nparams → Expr ζ ℓ m}
      {t : Expr ζ ℓ m} (hΔ : E[Δ] ⊢ₛ ok)
      (hqs : ∀ p, E[Δ] ⊢ₛ qs p : (E.get η).block.paramType ls qs p)
      (ht : E[Δ] ⊢ₛ t : .ind η s ls qs h.indices) :
      E[Δ] ⊢ₛ h.projType η ls qs f t : .sort u := by
    rw [projType_eq_projTypeWith]
    refine projTypeWith_hasTypeStrong (hB.ctors s c) hqs fun prior => ?_
    have hp := (projectionStrong hΔ hqs ht
      (prior.castLT (prior.isLt.trans f.isLt))).term
    rw [projType_eq_projTypeWith] at hp
    exact hp
  have hsnoc {m : Nat} {Δ : Ctx ζ ℓ 0 m} {qs : Fin ι.nparams → Expr ζ ℓ m}
      (hΔ : E[Δ] ⊢ₛ ok)
      (hqs : ∀ p, E[Δ] ⊢ₛ qs p : (E.get η).block.paramType ls qs p) :
      E[Δ.snoc (.ind η s ls qs h.indices)] ⊢ₛ
        h.projType η ls (fun p => (qs p).wk) f (.var (Fin.last m)) : .sort u :=
    hbody (hΔ.snoc ⟨_, h.indTypeStrong hqs⟩) (h.wkParams hqs) (h.varMajor hΔ hqs)
  have hbeta {m : Nat} {Δ : Ctx ζ ℓ 0 m} {qs : Fin ι.nparams → Expr ζ ℓ m}
      {t : Expr ζ ℓ m} (hΔ : E[Δ] ⊢ₛ ok)
      (hqs : ∀ p, E[Δ] ⊢ₛ qs p : (E.get η).block.paramType ls qs p)
      (ht : E[Δ] ⊢ₛ t : .ind η s ls qs h.indices) :
      E[Δ] ⊢ₛ .app (h.projectionMotives η ls qs f s) t ≡
        h.projType η ls qs f t : .sort u := by
    rw [h.projectionMotives_self]
    have hb := DefeqStrong.beta (h.indTypeStrong hqs) .sortDF (hsnoc hΔ hqs) ht
      (by simpa [Expr.inst] using DefeqStrong.sortDF)
      ((hsnoc hΔ hqs).substitution (SubstWFStrong.inst hΔ ht.left))
    convert hb using 1
    · simp only [Expr.inst, Expr.wk_subst_extend, projType_subst,
        Expr.subst, Subst.extend_last, Expr.subst_id]
    · simp [Expr.inst]
  have hiotaType {m : Nat} {Δ : Ctx ζ ℓ 0 m} {qs : Fin ι.nparams → Expr ζ ℓ m}
      {gds : Fin (ι.ctors s c).nfields → Expr ζ ℓ m} (hΔ : E[Δ] ⊢ₛ ok)
      (hqs : ∀ p, E[Δ] ⊢ₛ qs p : (E.get η).block.paramType ls qs p)
      (ht : E[Δ] ⊢ₛ .ctor η s c ls qs gds h.recursive :
        .ind η s ls qs h.indices)
      (hgds : ∀ current, E[Δ] ⊢ₛ gds current :
        projTypeWith ((E.get η).block) ls qs current fun previous =>
          gds (previous.castLE current.isLt.le)) :
      E[Δ] ⊢ₛ h.projType η ls qs f (.ctor η s c ls qs gds h.recursive) ≡
        projTypeWith ((E.get η).block) ls qs f
          (fun prior => gds (prior.castLE f.isLt.le)) : .sort u := by
    rw [projType_eq_projTypeWith]
    refine projTypeWith_congrStrong hB (hB.ctors s c) hqs fun prior => ?_
    have hp := (projectionStrong hΔ hqs ht
      (prior.castLT (prior.isLt.trans f.isLt))).iota gds rfl hgds
    rw [projType_eq_projTypeWith] at hp
    exact hp
  have hmotive : E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps u s := by
    rw [hmsDef, h.projectionMotives_self, h.motiveType_self]
    exact .lamDF (h.indTypeStrong hps) .sortDF .sortDF (hsnoc hΓ hps) (hsnoc hΓ hps)
  have hms : ∀ target, E[Γ] ⊢ₛ ms target :
      (E.get η).block.motiveType η ls ps u target := fun target => by
    obtain rfl := h.sort_unique target
    exact hmotive
  have hfieldsTele := (hB.ctors s c).ordinaryFieldTele (η := η) hps
  have hΓcase := (hB.caseTele (c := c) hΓ hps hms).appendCtxWFStrong hΓ
  have hcaseParams := (Inductive.caseParams_congr (c := c) (ms := ms) · hps)
  have hcaseOrdinary := (hB.caseOrdinary_typed (c := c) (ms := ms) · hps)
  have hcaseIdx : ((E.get η).block.ctors s c).targetIndex ls
      ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary = h.indices :=
    h.indices_eq _
  have hcaseRec : ((ι.ctors s c).caseRecursive :
      Fin (ι.ctors s c).nrecFields → Expr ζ ℓ
        (n + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
          (ι.ctors s c).nrecFields)) = h.recursive :=
    h.recursive_eq _
  have hcaseMajor : E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      .ctor η s c ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary h.recursive :
      .ind η s ls ((ι.ctors s c).caseParams ps) h.indices := by
    rw [← hcaseRec, ← hcaseIdx]
    exact .ctorDF (recFieldLevels := fun _ => .zero)
      (fun p => (hcaseParams p).left)
      (fun current => (hcaseOrdinary current).left)
      h.no_recursive.elim
      (fun current => (hB.ctors s c).ordinaryFieldExprStrong current
        hcaseParams hcaseOrdinary)
      h.no_recursive.elim
      (.indDF (fun p => (hcaseParams p).left) h.no_indices.elim)
  have hcaseMotive : (((ms s).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields =
      h.projectionMotives η ls ((ι.ctors s c).caseParams ps) f s := by
    simp only [hmsDef, h.projectionMotives_wkN]
    rfl
  have hcaseBeta : E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      (E.get η).block.caseType η ls ps ms s c ≡
        projTypeWith ((E.get η).block) ls ((ι.ctors s c).caseParams ps) f
          (fun prior => (ι.ctors s c).caseOrdinary (prior.castLE f.isLt.le)) :
        .sort u := by
    rw [Inductive.caseType, Inductive.motiveResult, hcaseMotive,
      Expr.apps_eq_self_of_zero hni, hcaseRec]
    exact (hbeta hΓcase hcaseParams hcaseMajor).trans
      (hiotaType hΓcase hcaseParams hcaseMajor hcaseOrdinary)
  have hcase : E[Γ] ⊢ₛ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c :=
    Ctx.lam_congrStrong hΓcase (.defeqDF hcaseBeta.symm (hcaseOrdinary f))
  have hmins : ∀ target targetCtor, E[Γ] ⊢ₛ mins target targetCtor :
      (E.get η).block.caseFnType η ls ps ms target targetCtor :=
    fun target targetCtor => by
      obtain rfl := h.sort_unique target
      obtain rfl := h.ctor_unique targetCtor
      exact hcase
  have hresult : E[Γ] ⊢ₛ Inductive.motiveResult (ms s) h.indices maj ≡
        h.projType η ls ps f maj : .sort u := by
    rw [Inductive.motiveResult, hmsDef, Expr.apps_eq_self_of_zero hni]
    exact hbeta hΓ hps hmaj
  have hresultTy : E[Γ] ⊢ₛ Inductive.motiveResult (ms s) h.indices maj : .sort u :=
    hB.motiveResult_congr hΓ (fun p => (hps p).left)
      (fun target => (hms target).left) h.no_indices.elim hmaj.left
  have hterm : E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
      h.projType η ls ps f maj := by
    rw [h.projTerm_eq_recr]
    exact .defeqDF hresult (.recrDF (by simpa using h.recAllowed u)
      (fun p => (hps p).left) (fun target => (hms target).left)
      (fun target targetCtor => (hmins target targetCtor).left)
      h.no_indices.elim hmaj.left hresultTy)
  refine ⟨hresult.right, hresult, hterm, hcase, hms, ?_⟩
  intro fds rfl hfields
  have htargetIdx : (fun i =>
      ((E.get η).block.ctors s c).targetIndex ls ps fds i) = h.indices :=
    h.indices_eq _
  have htypeIota : E[Γ] ⊢ₛ (E.get η).block.iotaType η ls ps ms s c fds h.recursive ≡
        h.projType η ls ps f (.ctor η s c ls ps fds h.recursive) : .sort u := by
    simpa [Inductive.iotaType, htargetIdx] using hresult
  have hlhs : E[Γ] ⊢ₛ (E.get η).block.iotaLhs η ls u ps ms mins s c fds h.recursive :
      (E.get η).block.iotaType η ls ps ms s c fds h.recursive := by
    have ht := DefeqStrong.defeqDF htypeIota.symm hterm
    rw [h.projTerm_eq_recr, ← htargetIdx] at ht
    exact ht
  have hbodyOrd : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps] ⊢ₛ
      Expr.boundVars n (ι.ctors s c).nfields 0 f :
        projTypeWith ((E.get η).block) ls
          (fun p => (ps p).wkN (ι.ctors s c).nfields) f
          (fun previous => Expr.boundVars n (ι.ctors s c).nfields 0
            (previous.castLE f.isLt.le)) := by
    have hv := (hB.ctors s c).boundOrdinarySubstWFStrong (η := η) hps
      (Fin.natAdd ι.nparams f)
    rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL,
      Ctx.entry_append_right (E.get η).block.params _ (by omega) (by simp)
        (by omega)] at hv
    simpa [projTypeWith] using hv
  have hrhsEq : E[Γ] ⊢ₛ (E.get η).block.iotaRhs η ls u ps ms mins s c fds h.recursive ≡ fds f :
      projTypeWith ((E.get η).block) ls ps f fun previous =>
        fds (previous.castLE f.isLt.le) := by
    have happly := Ctx.lam_applyFamilyStrong hΓ hfieldsTele
      (fun current => by
        unfold Ctor.ordinaryFieldTele Ctor.ordinaryFieldTeleAux
        rw [Ctx.entry_substN ps _ _ current.val (by omega) (by omega) (by omega)
            (by omega), ← Ctx.entry_instL]
        simpa [projTypeWith] using hfields current) hbodyOrd
    rw [Inductive.iotaRhs, hminsDef, h.projectionCases_self,
      Expr.apps_eq_self_of_zero hnr, Expr.apps_eq_self_of_zero hnr]
    simpa [Expr.boundVars, Expr.subst] using happly
  have htypeToOrd := htypeIota.trans (hiotaType hΓ hps hmaj hfields)
  have hiota := DefeqStrong.iota (by simpa using h.recAllowed u)
    hps hms hmins
    (fun current => by simpa [projTypeWith] using hfields current)
    h.no_recursive.elim htypeToOrd.left hlhs
    (.defeqDF htypeToOrd.symm hrhsEq.left)
  rw [h.projTerm_eq_recr, ← htargetIdx]
  exact .defeqDF htypeIota (hiota.trans (.defeqDF htypeToOrd.symm hrhsEq))
termination_by f.val

theorem projTerm_hasTypeStrong :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
      h.projType η ls ps f maj :=
  fun hΓ hps hmaj => (h.projectionStrong hB hΓ hps hmaj f).term

theorem projType_hasTypeStrong :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.projType η ls ps f maj :
      .sort ((((E.get η).block.ctors s c).ordinary f).level.inst ls) :=
  fun hΓ hps hmaj => (h.projectionStrong hB hΓ hps hmaj f).type

theorem projTerm_genericStrong :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ
      h.projTerm η ls (fun p => (ps p).wk) f (.var (Fin.last n)) :
      h.projType η ls (fun p => (ps p).wk) f (.var (Fin.last n)) :=
  fun hΓ hps =>
    h.projTerm_hasTypeStrong hB f (hΓ.snoc ⟨_, h.indTypeStrong hps⟩)
      (h.wkParams hps) (h.varMajor hΓ hps)

theorem projTerm_substCongrStrong
    {m : Nat} {Δ : Ctx ζ ℓ 0 m}
    {β₁ β₂ : Subst ζ ℓ n m} {maj₁ maj₂ : Expr ζ ℓ m} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Δ] ⊢ₛ β₁ ≡ β₂ ⊣ Γ →
    E[Δ] ⊢ₛ maj₁ ≡ maj₂ :
      .ind η s ls (fun p => (ps p).subst β₁) h.indices →
    E[Δ] ⊢ₛ h.projTerm η ls (fun p => (ps p).subst β₁) f maj₁ ≡
      h.projTerm η ls (fun p => (ps p).subst β₂) f maj₂ :
      h.projType η ls (fun p => (ps p).subst β₁) f maj₁ := by
  intro hΓ hps hβ hmaj
  have hΓ' : E[Γ.snoc (.ind η s ls ps h.indices)] ⊢ₛ ok :=
    hΓ.snoc ⟨_, h.indTypeStrong hps⟩
  have hξ : E[Δ] ⊢ₛ β₁.extend maj₁ ≡ β₂.extend maj₂ ⊣
      Γ.snoc (.ind η s ls ps h.indices) := by
    refine hβ.extend ?_
    rw [Expr.subst, h.indices_eq fun i => Expr.subst β₁ (h.indices i)]
    exact hmaj
  simpa [Expr.wk_subst_extend, Expr.subst, Subst.extend_last] using
    DefeqStrong.substitution_congr hΓ' hξ (h.projTerm_genericStrong hB f hΓ hps)

theorem projTerm_congrStrong :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ h.indices →
    E[Γ] ⊢ₛ h.projTerm η ls ps₁ f maj₁ ≡ h.projTerm η ls ps₂ f maj₂ :
      h.projType η ls ps₁ f maj₁ := by
  intro hps hmaj
  have hparams := hB.params.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hΓ₀ : E[Ctx.instL ls (E.get η).block.params] ⊢ₛ ok := by
    simpa using hparams.appendCtxWFStrong (Γ := .nil) .nil
  have hgeneric : ∀ p : Fin ι.nparams,
      E[Ctx.instL ls (E.get η).block.params] ⊢ₛ Expr.var p :
        (E.get η).block.paramType ls (Subst.id : Subst ζ ℓ ι.nparams ι.nparams) p := by
    intro p
    have hvar := hΓ₀.var p
    rw [← Ctx.get_instL] at hvar
    rw [← Inductive.paramType_eq_get_subst, Expr.subst_id]
    exact hvar
  exact h.projTerm_substCongrStrong hB
    f hΓ₀ hgeneric (Inductive.paramSubstEqStrong hps) hmaj

theorem projType_congrStrong :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ h.indices →
    E[Γ] ⊢ₛ h.projType η ls ps₁ f maj₁ ≡ h.projType η ls ps₂ f maj₂ typ := by
  intro hps hmaj
  have hfields : ∀ current : Fin (ι.ctors s c).nfields,
      E[Γ] ⊢ₛ h.projTerm η ls ps₁ current maj₁ ≡ h.projTerm η ls ps₂ current maj₂ :
        (((((E.get η).block.ctors s c).ordinary current).type).instL ls).subst
          (Fin.append ps₁ fun prior : Fin current.val =>
            h.projTerm η ls ps₁ (prior.castLE current.isLt.le) maj₁) := by
    intro current
    have hcongr := h.projTerm_congrStrong hB current hps hmaj
    rwa [projType_eq] at hcongr
  have heq := (hB.ctors s c).ordinaryFieldExpr_congr hB.params f
    hps (fun g _ => hfields g)
  rw [projType_eq, projType_eq]
  exact .ofDefEq heq

theorem rebuildTerm_hasTypeStrong
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ maj : .ind η s ls ps h.indices →
    E[Γ] ⊢ₛ h.rebuildTerm η ls ps maj : .ind η s ls ps is := by
  intro hΓ hps hmaj
  have hfields : ∀ f, E[Γ] ⊢ₛ h.projTerm η ls ps f maj :
      (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          h.projTerm η ls ps
            (previous.castLE f.isLt.le) maj) := by
    intro f
    have hf := h.projTerm_hasTypeStrong hB f hΓ hps hmaj
    rw [projType_eq_projTypeWith] at hf
    exact hf
  have hrebuild := DefeqStrong.ctorDF
    (recFds₁ := h.recursive) (recFds₂ := h.recursive)
    (recFieldLevels := h.no_recursive.elim)
    hps hfields
    h.no_recursive.elim
    (fun f => (hB.ctors s c).ordinaryFieldExprStrong f hps hfields)
    h.no_recursive.elim
    (DefeqStrong.indDF hps h.no_indices.elim)
  have hindices : ((E.get η).block.ctors s c).targetIndex ls ps
      (h.projTerm η ls ps · maj) = is :=
    funext h.no_indices.elim
  rw [hindices] at hrebuild
  exact hrebuild

theorem projTerm_ctorStrong
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ .ctor η s c ls ps fds h.recursive :
      .ind η s ls ps h.indices →
    (∀ current, E[Γ] ⊢ₛ fds current :
      projTypeWith ((E.get η).block) ls ps current fun previous =>
        fds (previous.castLE current.isLt.le)) →
    E[Γ] ⊢ₛ h.projTerm η ls ps f (.ctor η s c ls ps fds h.recursive) ≡ fds f :
      h.projType η ls ps f (.ctor η s c ls ps fds h.recursive) :=
  fun hΓ hps hmaj => (h.projectionStrong hB hΓ hps hmaj f).iota fds rfl

end Metalean.Inductive.IsStructure
