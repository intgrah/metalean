/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Rules.Core
public import Metalean.Semantics.Soundness.Telescope.Beta
public import Metalean.Semantics.Soundness.Recursor.Case
public import Metalean.Semantics.Soundness.Structure.Fields
public import Metalean.Semantics.Soundness.Structure.Generic
import Metalean.Strong.Structure
import Metalean.Typing.Weakening
import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Soundness.Rules.Function
import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ₁.as.len} {maj : Expr ζ₂ ℓ Γ₁.as.len}

theorem HasEquality.structure_projection_motive_beta
    (hs : (E₂.get η).block.IsStructure s c)
    (pps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields)
    (pbodyI : HasIdeality (CtxCat.extension Γ₁ (hs.indTypeStrong pps))
      (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len))))
    (pbodyS : HasSubstitution (CtxCat.extension Γ₁ (hs.indTypeStrong pps))
      (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len)))) :
    HasEquality Γ₁
      (Inductive.motiveResult (hs.projectionMotives η ls ps f s) hs.indices maj)
      (hs.projType η ls ps f maj) := by
  rw [hs.projectionMotives_self, Inductive.motiveResult,
    Expr.apps_eq_self_of_zero (Fin.eq_zero_of_isEmpty hs.no_indices),
    show hs.projType η ls ps f maj = (hs.projType η ls (fun p => (ps p).wk) f
      (.var (Fin.last Γ₁.as.len))).inst maj by
      simp [Expr.inst, Expr.wk_subst_extend, Expr.subst]]
  exact @HasEquality.beta _ _ _ _ _ _ _ _ (hs.indTypeStrong pps) pmaj.syntactic.left
    pmaj.type.ideal pbodyI pmaj.left.ideal pmaj.fixed pmaj.left.subst pbodyS

theorem RawInterpretationProperties.structure_projection_case
    (hs : (E₂.get η).block.IsStructure s c)
    (hΔ : WFTeleStrong E₂ (fun _ => True) Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (pfields : RawTeleProperties E₂ Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (f : Fin (ι.ctors s c).nfields) :
    RawInterpretationProperties Γ₁ (hs.projectionCases η ls ps f ms s c) := by
  let Δ := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps
  let Full := CtxCat.extendTele Γ₁ Δ hΔ
  rw [hs.projectionCases_self]
  exact RawInterpretationProperties.ctxLam Δ rfl hΔ pfields _ (.var Full _)

theorem rawInterpret_structure_case_beta (hs : (E₂.get η).block.IsStructure s c)
    (hΔ : WFTeleStrong E₂ (fun _ => True) Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (pfields : RawTeleProperties E₂ Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ)
    (ρ : RawValuation Γ₂) (args : Fin (ι.ctors s c).nfields → Domain Γ₂)
    (hρ : SourceAdmissible σ (ρ.pushFin fun i => (args i).val))
    (f : Fin (ι.ctors s c).nfields) :
    rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁
      (hs.projectionCases η ls ps f ms s c)).app _
      (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ)
      (fun i => (Tm E₂ ℓ).map σ.op
        (Tm.varLabel (CtxCat.extendTele Γ₁
          (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ) (Fin.natAdd Γ₁.as.len i)))
      (fun i => (args i).val) = (args f).val := by
  let Δ := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps
  let Full := CtxCat.extendTele Γ₁ Δ hΔ
  have pvar : RawInterpretationProperties Full (.var (Fin.natAdd Γ₁.as.len f)) :=
    RawInterpretationProperties.var Full _
  rw [hs.projectionCases_self]
  have hb := rawInterpret_openCtxLam_beta Δ hΔ pfields
    (.var (Fin.natAdd Γ₁.as.len f)) pvar σ ρ args hρ
  refine hb.trans ?_
  erw [rawInterpret_var]
  change (ρ.pushFin fun i => (args i).val) (Var.db (Fin.natAdd Γ₁.as.len f)) = _
  simp

structure StructureProjection (hs : (E₂.get η).block.IsStructure s c)
    (ls : Fin ι.nlevels → Level ℓ) (f : Fin (ι.ctors s c).nfields) (Γ₁ : CtxCat E₂ ℓ)
    (ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len) (maj : Expr ζ₂ ℓ Γ₁.as.len) : Prop where
  term : RawInterpretationProperties Γ₁ (hs.projTerm η ls ps f maj)
  fixed : HasFixedness Γ₁ (hs.projTerm η ls ps f maj) (hs.projType η ls ps f maj)
  value {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ₁) (ρ : RawValuation Ξ) :
    SourceAdmissible σ ρ →
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ.op ρ =
        RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
          ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ.op ρ)

def StructureProjection.Prev (hs : (E₂.get η).block.IsStructure s c)
    (ls : Fin ι.nlevels → Level ℓ) (f : Fin (ι.ctors s c).nfields) : Prop :=
  ∀ g : Fin f.val,
  ∀ ⦃Γ₁ : CtxCat E₂ ℓ⦄ {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len} {maj : Expr ζ₂ ℓ Γ₁.as.len},
  RawTeleProperties E₂ .nil Γ₁.as.ctx →
  (∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p)) →
  RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices) →
  StructureProjection hs ls (g.castLE f.isLt.le) Γ₁ ps maj

theorem structure_carrier_relevant (hs : (E₂.get η).block.IsStructure s c)
    (f : Fin (ι.ctors s c).nfields)
    (hf : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = true) :
    Level.rel ((E₂.get η).block.level.inst ls) = true := by
  by_contra hn
  have hz : (E₂.get η).block.level.inst ls = .zero := by simpa using hn
  have hzero : ((E₂.get η).block.level.inst ls).eval (fun _ => 0) = 0 := by rw [hz]; rfl
  have hfield := hs.ordinaryLevel_eq_zero_of_eval_zero ls hzero f
  simp only [hfield, Level.rel, decide_eq_true_eq] at hf
  exact hf rfl

theorem HasFixedness.structure_projection_case (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (f : Fin (ι.ctors s c).nfields)
    (hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = true)
    (pms : ∀ t, RawTyped Γ₁ (hs.projectionMotives η ls ps f t)
      ((E₂.get η).block.motiveType η ls ps ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) t))
    (hprev : StructureProjection.Prev hs ls f) :
    HasFixedness Γ₁ (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f) s c)
      ((E₂.get η).block.caseFnType η ls ps (hs.projectionMotives η ls ps f) s c) := by
  let ms := hs.projectionMotives η ls ps f
  have hps (p : Fin ι.nparams) := (pps p).syntactic.left
  have hms (t : Fin ι.nsorts) := (pms t).typed
  have hcarrier := structure_carrier_relevant hs f hrel
  have hdata : IndData Γ₁ η ls ps := ⟨hB, hps⟩
  have hΔ := hB.caseTele (s := s) (c := c) Γ₁.as.wf hps hms
  have pΔ := hsound.caseTeleProperties hI hblock s c hdata hR (fun p => (pps p).toRawTyped) pms
  let Γ₁' := CtxCat.extendTele Γ₁ ((E₂.get η).block.caseTele η ls ps ms s c) hΔ
  have hR' : RawTeleProperties E₂ .nil Γ₁'.as.ctx := hR.append (by simpa using pΔ)
  have hparams (p : Fin ι.nparams) : E₂[Γ₁'.as.ctx] ⊢ₛ (ι.ctors s c).caseParams ps p :
      (E₂.get η).block.paramType ls ((ι.ctors s c).caseParams ps) p :=
    Inductive.caseParams_typed (ms := ms) (c := c) p hps
  have hord (g : Fin (ι.ctors s c).nfields) := hB.caseOrdinary_typed (ms := ms) g hps
  let O := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps
  let R := ((E₂.get η).block.ctors s c).recursiveFieldTele η ls
    (fun p => (ps p).wkN (ι.ctors s c).nfields) (Expr.boundVars Γ₁.as.len (ι.ctors s c).nfields 0)
  let H := ((E₂.get η).block.ctors s c).ihTele ls ps ms
  have ⟨hO, hRt⟩ := ((hB.ctors s c).fieldTele rfl Γ₁.as.wf hps).of_append
  have hH : WFTeleStrong E₂ (fun _ => True) ((Γ₁.as.ctx ++ O) ++ R) H := by
    rw [Tele.append_assoc]
    exact (hB.ctors s c).ihTele hB Γ₁.as.wf hps hms
  have pps' (p : Fin ι.nparams) : RawJudgment Γ₁' ((ι.ctors s c).caseParams ps p)
      ((ι.ctors s c).caseParams ps p) ((E₂.get η).block.paramType ls ((ι.ctors s c).caseParams ps) p) := by
    have q (wf : E₂[((Γ₁.as.ctx ++ O) ++ R) ++ H] ⊢ₛ ok) :
        RawJudgment (⟨((Γ₁.as.ctx ++ O) ++ R) ++ H, wf⟩ : CtxCat E₂ ℓ)
          ((((ps p).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields)
          ((((ps p).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields)
          (((((E₂.get η).block.paramType ls ps p).wkN (ι.ctors s c).nfields).wkN
            (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) :=
      (((pps p).wkN O hO).wkN (Γ := CtxCat.extendTele Γ₁ O hO) R hRt).wkN
        (Γ := CtxCat.extendTele (CtxCat.extendTele Γ₁ O hO) R hRt) H hH
    rw [Tele.append_assoc (Γ₁.as.ctx ++ O) R H, Tele.append_assoc Γ₁.as.ctx O (R ++ H),
      ← Tele.append_assoc O R H, Inductive.paramType_wkN, Inductive.paramType_wkN,
      Inductive.paramType_wkN] at q
    exact q Γ₁'.as.wf
  have hvar (g : Fin (ι.ctors s c).nfields) : (ι.ctors s c).caseOrdinary g =
      (Expr.var (((Fin.natAdd Γ₁.as.len g).castAdd (ι.ctors s c).nrecFields).castAdd
        (ι.ctors s c).nrecFields) : Expr ζ₂ ℓ Γ₁'.as.len) := by
    simp [CtorSig.caseOrdinary, CtorSig.fieldOrdinary]
  have hentry (g : Fin (ι.ctors s c).nfields) :
      Γ₁'.as.ctx.get (((Fin.natAdd Γ₁.as.len g).castAdd (ι.ctors s c).nrecFields).castAdd
        (ι.ctors s c).nrecFields) =
      ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary g := by
    change Ctx.get _ (Γ₁.as.ctx ++ (((E₂.get η).block.ctors s c).fieldTele η ls ps ++ H)) = _
    rw [← Tele.append_assoc, Ctx.get_append]
    change (Ctx.get (fieldVar hdata s c (Fin.castAdd (ι.ctors s c).nrecFields g))
      (CtxCat.ctorFields hdata s c).as.ctx).wkN (ι.ctors s c).nrecFields = _
    rw [CtxCat.ctorFields_get_ordinary, Expr.wkN_eq_subst, Ctor.ordinaryFieldExpr_subst]
    congr 1
    · funext p
      simp [CtorSig.caseParams, Expr.wkN_eq_subst]
    · funext g'
      simp [CtorSig.caseOrdinary, Expr.wkN_eq_subst]
  have hctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) := hB.ordinaryClosedWF s c ls k hk
  have pctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) :=
      hsound.blockOrdinaryPrefixProperties η hI hblock s c ls k hk
  have pfield (g : Fin (ι.ctors s c).nfields) :=
      hsound.blockOrdinaryTypeJudgment η hI hblock s c ls g
  have pvarProps (g : Fin (ι.ctors s c).nfields) :
      RawInterpretationProperties Γ₁' ((ι.ctors s c).caseOrdinary g) := by
    rw [hvar g]
    exact RawInterpretationProperties.var Γ₁' _
  have fvar (g : Fin (ι.ctors s c).nfields) : HasFixedness Γ₁' ((ι.ctors s c).caseOrdinary g)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary g) := by
    rw [hvar g, ← hentry g]
    exact HasFixedness.var Γ₁'.as.wf hR' _
  have pfvar (g : Fin (ι.ctors s c).nfields) : RawJudgment Γ₁' ((ι.ctors s c).caseOrdinary g)
      ((ι.ctors s c).caseOrdinary g)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary g) := by
    have hp := ordinaryField_properties g (hctx g.val g.isLt.le) (pctx g.val g.isLt.le)
      (pfield g (hctx g.val g.isLt.le)) hparams
      (fun p => (pps' p).left) (fun p => (pps' p).fixed) (fun _ => hord _) (fun _ => pvarProps _)
      (fun _ => fvar _)
    exact { syntactic := hord g
            type := hp.1
            left := pvarProps g
            right := pvarProps g
            equal := HasEquality.refl _ _
            fixed := fvar g }
  have hidx : ((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).caseParams ps)
      (ι.ctors s c).caseOrdinary = hs.indices := funext hs.no_indices.elim
  have pfn (d : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hI hblock s d ls
  have pmaj' : RawJudgment Γ₁' (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary
      hs.recursive) (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive)
      (.ind η s ls ((ι.ctors s c).caseParams ps) hs.indices) := by
    have hm := RawJudgment.ctorDF (recFds₁ := hs.recursive) (recFds₂ := hs.recursive)
      (recFieldLevels := hs.no_recursive.elim) hsound hI hblock hB pps' pfvar
      hs.no_recursive.elim
      (fun g => (hB.ctors s c).ordinaryFieldExprStrong g hparams hord) hs.no_recursive.elim
      (RawJudgment.indDF hB pfn pps' hs.no_indices.elim)
    rwa [hidx] at hm
  have hmaj' := pmaj'.syntactic.left
  have hA' := hs.indTypeStrong (η := η) hparams
  have pgen := RawJudgment.structure_generic hs hparams pmaj'.type
  have hRG' : RawTeleProperties E₂ .nil (Γ₁'.extension hA').as.ctx := hR'.extension Γ₁'.as.wf pmaj'.type
  have ppsG' := RawJudgment.paramType_wk pps' hA'
  have hprevG' (g : Fin f.val) := hprev g hRG' ppsG' pgen
  have ⟨pbody', _⟩ := structure_projection_type_properties hsound hI hblock hs hB
    (fun p => (ppsG' p).syntactic.left) (fun p => (ppsG' p).left) (fun p => (ppsG' p).fixed) pgen.syntactic.left f
    (fun g => (hprevG' g).term) fun g => (hprevG' g).fixed
  have hprev' (g : Fin f.val) := hprev g hR' pps' pmaj'
  have hmsw : (E₂.get η).block.caseType η ls ps ms s c =
      Inductive.motiveResult (hs.projectionMotives η ls ((ι.ctors s c).caseParams ps) f s) hs.indices
        (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive) := by
    unfold Inductive.caseType
    rw [hs.projectionMotives_wkN, hs.projectionMotives_wkN, hs.projectionMotives_wkN]
    congr 2
    exact funext hs.no_recursive.elim
  have hiota (g : Fin f.val) := by
    have hi := (hs.projectionStrong hB Γ₁'.as.wf hparams hmaj' (g.castLE f.isLt.le)).iota
      (ι.ctors s c).caseOrdinary rfl hord
    rwa [hs.projType_eq] at hi
  have hresult : E₂[Γ₁'.as.ctx] ⊢ₛ (E₂.get η).block.caseType η ls ps ms s c ≡
      ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary f : .sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) := by
    have hres := (hs.projectionStrong hB Γ₁'.as.wf hparams hmaj' f).result
    rw [hs.projType_eq] at hres
    rw [hmsw]
    exact hres.trans (Inductive.IsStructure.projTypeWith_congrStrong (I := (E₂.get η).block) hB
      (hB.ctors s c) hparams hiota)
  have hteq : HasEquality Γ₁' ((E₂.get η).block.caseType η ls ps ms s c)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary f) := by
    intro Ξ σ ρ hρ
    rw [hmsw, HasEquality.structure_projection_motive_beta hs hparams pmaj' f pbody'.ideal pbody'.subst σ ρ hρ,
      hs.projType_eq]
    let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls ((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩
    have hprojTyped (g : Fin f.val) : E₂[Γ₁'.as.ctx] ⊢ₛ
        hs.projTerm η ls ((ι.ctors s c).caseParams ps) (g.castLE f.isLt.le)
          (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive) :
        ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
          (fun h => hs.projTerm η ls ((ι.ctors s c).caseParams ps) h
            (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive))
          (g.castLE f.isLt.le) := by
      have ht := hs.projTerm_hasTypeStrong hB (g.castLE f.isLt.le) Γ₁'.as.wf hparams hmaj'
      rwa [hs.projType_eq] at ht
    let σ₁ : Γ₁'.as ⟶ Src.as := ⟨Fin.append ((ι.ctors s c).caseParams ps) fun g : Fin f.val =>
        hs.projTerm η ls ((ι.ctors s c).caseParams ps) (g.castLE f.isLt.le)
          (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive),
      Ctor.ordinarySubstWFStrong f.isLt.le hparams hprojTyped⟩
    let σ₂ : Γ₁'.as ⟶ Src.as := ⟨Fin.append ((ι.ctors s c).caseParams ps) fun g : Fin f.val =>
        (ι.ctors s c).caseOrdinary (g.castLE f.isLt.le),
      Ctor.ordinarySubstWFStrong f.isLt.le hparams fun _ => hord _⟩
    have hσ : RawCtx.toCtx.map σ₁ = RawCtx.toCtx.map σ₂ := by
      refine (RawCtx.toCtx_map_eq_iff σ₁ σ₂).mpr ?_
      have hfieldsTele := ((hB.ctors s c).ordinaryTeleAuxStrong f.val f.isLt.le).instLevel
        (Q := fun _ => True) ls fun _ => trivial
      have hfull := SubstEqStrong.extendFamily hfieldsTele (Inductive.paramSubstEqStrong hparams)
        (xs₁ := fun g : Fin f.val => hs.projTerm η ls ((ι.ctors s c).caseParams ps) (g.castLE f.isLt.le)
          (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive))
        (xs₂ := fun g : Fin f.val => (ι.ctors s c).caseOrdinary (g.castLE f.isLt.le)) fun prior => by
          rw [← Ctx.entry_instL, Ctor.ordinaryTeleAux_entry]
          exact hiota prior
      change E₂[Γ₁'.as.ctx] ⊢ₛ _ ≡ _ ⊣ Ctx.instL ls ((E₂.get η).block.params ++
        ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le)
      rwa [Ctx.instL_append]
    have hpf (g : Fin f.val) : HasFixedness Γ₁'
        (hs.projTerm η ls ((ι.ctors s c).caseParams ps) (g.castLE f.isLt.le)
          (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive))
        (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
          (fun h => hs.projTerm η ls ((ι.ctors s c).caseParams ps) h
            (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive))
          (g.castLE f.isLt.le)) := by
      have hf := @StructureProjection.fixed _ _ _ _ _ _ _ hs _ _ _ _ _ (hprev' g)
      rwa [hs.projType_eq] at hf
    have hctor : CtorTyping Γ₁' η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary
        hs.recursive := ⟨hord, hs.no_recursive.elim⟩
    have hv (v : Var Src.as.len) : RawInterpretationProperties Γ₁' (σ₁.subst v) ∧
        RawInterpretationProperties Γ₁' (σ₂.subst v) ∧ HasEquality Γ₁' (σ₁.subst v) (σ₂.subst v) ∧
        HasFixedness Γ₁' (σ₁.subst v) ((Src.as.ctx.get v).subst σ₁.subst) := by
      change RawInterpretationProperties Γ₁' (σ₁.subst v) ∧
        RawInterpretationProperties Γ₁' (σ₂.subst v) ∧ HasEquality Γ₁' (σ₁.subst v) (σ₂.subst v) ∧
        HasFixedness Γ₁' (σ₁.subst v)
          ((Ctx.get v (Ctx.instL ls ((E₂.get η).block.params ++
            ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le))).subst σ₁.subst)
      rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
      cases v using Fin.addCases with
      | left p =>
        rw [Ctx.entry_append_left (E₂.get η).block.params _ (by omega) p.isLt
          (show p.val < ι.nparams + f.val by omega)]
        simpa only [σ₁, σ₂, Fin.append_left, Fin.append_castLE_left _ _ p.isLt.le] using
          ⟨(pps' p).left, (pps' p).left, HasEquality.refl _ _, (pps' p).fixed⟩
      | right g =>
        rw [Ctx.entry_append_right (E₂.get η).block.params _ (by omega) (by simp) (by omega)]
        refine ⟨by simpa only [σ₁, Fin.append_right] using (hprev' g).term,
          by simpa only [σ₂, Fin.append_right] using pvarProps _, ?_, ?_⟩
        · simp only [σ₁, σ₂, Fin.append_right]
          intro Ξ' σ' ρ' hρ'
          rw [(hprev' g).value σ' ρ' hρ', rawInterpret_ctor_typed _ hctor hcarrier,
            RawFamily.ctor_value, RawValue.proj_ctor, Fin.append_left]
        · simp [σ₁]
          exact hpf g
    exact HasSubstitution.congrImages (pfield f (hctx _ _)).left.subst (pctx _ _) σ₁ σ₂ hσ
      (fun v => (hv v).1.ideal) (fun v => (hv v).1.subst) (fun v => (hv v).2.1.subst)
      (fun v => (hv v).2.2.2) (fun v => (hv v).2.2.1) σ ρ hρ
  have htype := hB.caseType_hasTypeStrong Γ₁'.as.wf hparams
    (fun t => Inductive.caseMotives_typed t hms) hord (fun g => hB.caseRecursive_typed g Γ₁.as.wf hps)
  have fb : HasFixedness Γ₁' ((ι.ctors s c).caseOrdinary f) ((E₂.get η).block.caseType η ls ps ms s c) := by
    intro Ξ he σ ρ hρ
    rw [hteq σ ρ hρ, Tm.label_eq (he₁ := he) (he₂ := hord f) (.ofDefEq hresult) he]
    exact (pfvar f).fixed (hord f) σ ρ hρ
  change HasFixedness Γ₁ (Ctx.lam ((ι.ctors s c).caseOrdinary f) ((E₂.get η).block.caseTele η ls ps ms s c))
    (Ctx.pi ((E₂.get η).block.caseType η ls ps ms s c) ((E₂.get η).block.caseTele η ls ps ms s c))
  exact HasFixedness.ctxLam (k := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields + (ι.ctors s c).nrecFields)
    _ (by omega) hΔ pΔ _ _ htype (.defeqDF hresult.symm (hord f))
    (hsound.caseTypeProperties hI hblock hdata (fun p => (pps p).toRawTyped) pms s c Γ₁'.as.wf).ideal
    (pvarProps f).ideal fb

theorem structure_projection_body_properties (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields) (hprev : StructureProjection.Prev hs ls f) :
    RawInterpretationProperties (Γ₁.extension (hs.indTypeStrong fun p => (pps p).syntactic.left))
        (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len))) ∧
      HasFixedness (Γ₁.extension (hs.indTypeStrong fun p => (pps p).syntactic.left))
        (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len)))
        (.sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)) := by
  have hps (p : Fin ι.nparams) := (pps p).syntactic.left
  have hA := hs.indTypeStrong hps
  have ppsw := RawJudgment.paramType_wk pps hA
  have pvar := RawJudgment.structure_generic hs hps pmaj.type
  have hprevw (g : Fin f.val) :=
    hprev g (hR.extension Γ₁.as.wf pmaj.type) ppsw pvar
  exact structure_projection_type_properties hsound hI hblock hs hB
    (fun p => (ppsw p).syntactic.left) (fun p => (ppsw p).left) (fun p => (ppsw p).fixed)
    pvar.syntactic.left f (fun g => (hprevw g).term) fun g => (hprevw g).fixed

theorem structure_projection_recrArgs (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields)
    (hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = true)
    (hprev : StructureProjection.Prev hs ls f) (v : Fin (ι.recrEnd s)) :
    RawInterpretationProperties Γ₁ (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
        (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj v) ∧
      HasFixedness Γ₁ (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
          (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj v)
        ((Ctx.get v ((E₂.get η).block.recrTele η s ls
            ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls))).subst
          (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
            (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj)) := by
  have hps (p : Fin ι.nparams) := (pps p).syntactic.left
  have hA := hs.indTypeStrong (η := η) hps
  have ⟨pbody, fbody⟩ :=
    structure_projection_body_properties hsound hI hblock hs hB hR pps pmaj f hprev
  have ppsw := RawJudgment.paramType_wk pps hA
  have pvar := RawJudgment.structure_generic hs hps pmaj.type
  have hbody := hs.projType_hasTypeStrong hB f (Γ₁.extension hA).as.wf
    (fun p => (ppsw p).syntactic.left) pvar.syntactic.left
  have pms (t : Fin ι.nsorts) : RawTyped Γ₁ (hs.projectionMotives η ls ps f t)
      ((E₂.get η).block.motiveType η ls ps
        ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) t) := by
    have hm := (hs.projectionStrong hB Γ₁.as.wf hps pmaj.syntactic.left f).motive t
    obtain rfl := hs.sort_unique t
    refine ⟨hm, ?_, ?_, ?_⟩
    · rw [hs.motiveType_self]
      exact RawInterpretationProperties.forallE hA .sortDF pmaj.type
        (RawInterpretationProperties.sort _ _)
    · rw [hs.projectionMotives_self]
      exact RawInterpretationProperties.lam hA pmaj.type pbody
    · rw [hs.projectionMotives_self, hs.motiveType_self]
      exact HasFixedness.lam hA .sortDF hbody pmaj.type.ideal
        (HasIdeality.sort _ _) pbody.ideal fbody
  have hΔ := (hB.ctors s c).ordinaryFieldTele (η := η) hps
  have pfields := structure_field_telescope_properties hsound hI hblock hB hps
    (fun p => (pps p).left) (fun p => (pps p).fixed) (s := s) (c := c)
  refine Inductive.forall_recrSubst
    (motive := fun _ e₁ _ t => RawInterpretationProperties Γ₁ e₁ ∧ HasFixedness Γ₁ e₁ t)
    (ps₂ := ps) (ms₂ := hs.projectionMotives η ls ps f)
    (mins₂ := hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f))
    (is₂ := hs.indices) (maj₂ := maj)
    (fun p => ⟨(pps p).left, (pps p).fixed⟩) (fun t => ⟨(pms t).term, (pms t).fixed⟩)
    (fun t d => ?_) hs.no_indices.elim ⟨pmaj.left, pmaj.fixed⟩ v
  obtain rfl := hs.sort_unique t
  obtain rfl := hs.ctor_unique d
  exact ⟨RawInterpretationProperties.structure_projection_case hs hΔ pfields f,
    HasFixedness.structure_projection_case hsound hI hblock hs hB hR pps f hrel pms hprev⟩

end Metalean.CoherentShape
