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
import Metalean.Strong.Structure
import Metalean.Typing.Weakening
import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Soundness.Rules.Function
import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ₁.as.len} {maj : Expr ζ₂ ℓ Γ₁.as.len}

theorem HasEquality.structure_projection_motive_beta
    (hs : (E₂.get η).block.IsStructure s c)
    (pps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
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
  exact @HasEquality.beta _ _ _ _ _ _ _ _ (hs.indTypeStrong pps) pmaj.typed
    pmaj.type.ideal pbodyI pmaj.term.ideal pmaj.fixed pmaj.term.subst pbodyS

structure StructureProjection (hs : (E₂.get η).block.IsStructure s c)
    (ls : Fin ι.nlevels → Level ℓ) (f : Fin (ι.ctors s c).nfields) (Γ₁ : CtxCat E₂ ℓ)
    (ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len) (maj : Expr ζ₂ ℓ Γ₁.as.len) : Prop
    extends RawTyped Γ₁ (hs.projTerm η ls ps f maj) (hs.projType η ls ps f maj) where
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
  (∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p)) →
  RawTyped Γ₁ maj (.ind η s ls ps hs.indices) →
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

theorem structure_projection_body_properties (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields) (hprev : StructureProjection.Prev hs ls f) :
    RawTyped (Γ₁.extension (hs.indTypeStrong fun p => (pps p).typed))
      (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len)))
      (.sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)) := by
  have hps (p : Fin ι.nparams) := (pps p).typed
  have hA := hs.indTypeStrong hps
  have ppsw (p) := (SemanticHom.projection hA).typed (pps p)
  simp only [Inductive.paramType_subst, CtxCat.projectionRaw, Expr.subst_wk] at ppsw
  have pvar := (RawJudgment.var (Γ₁ := Γ₁.extension hA)
    (hR.extension Γ₁.as.wf pmaj.type) (Fin.last Γ₁.as.len)).toRawTyped
  simp only [Ctx.get_last, Expr.wk, Expr.wkFrom_ind,
    hs.indices_eq (fun i => Expr.wkFrom Γ₁.as.len (hs.indices i))] at pvar
  have hprevw (g : Fin f.val) :=
    hprev g (hR.extension Γ₁.as.wf pmaj.type) ppsw pvar
  exact structure_projection_type_properties hsound hI hblock hs hB ppsw f
    fun g => (hprevw g).toRawTyped

theorem RawTyped.structure_projection_case (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (f : Fin (ι.ctors s c).nfields)
    (hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = true)
    (pms : ∀ t, RawTyped Γ₁ (hs.projectionMotives η ls ps f t)
      ((E₂.get η).block.motiveType η ls ps ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) t))
    (hprev : StructureProjection.Prev hs ls f) :
    RawTyped Γ₁ (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f) s c)
      ((E₂.get η).block.caseFnType η ls ps (hs.projectionMotives η ls ps f) s c) := by
  let ms := hs.projectionMotives η ls ps f
  have hps (p : Fin ι.nparams) := (pps p).typed
  have hms (t : Fin ι.nsorts) := (pms t).typed
  have hcarrier := structure_carrier_relevant hs f hrel
  have hdata : IndData Γ₁ η ls ps := ⟨hB, hps⟩
  have hΔ := hB.caseTele (s := s) (c := c) Γ₁.as.wf hps hms
  have pΔ := hsound.caseTeleProperties hI hblock s c hdata hR (fun p => (pps p)) pms
  let Γ₁' := CtxCat.extendTele Γ₁ ((E₂.get η).block.caseTele η ls ps ms s c) hΔ
  have hR' : RawTeleProperties E₂ .nil Γ₁'.as.ctx := hR.append (by simpa using pΔ)
  have pps' (p : Fin ι.nparams) : RawTyped Γ₁' ((ι.ctors s c).caseParams ps p) ((E₂.get η).block.paramType ls ((ι.ctors s c).caseParams ps) p) := by
    convert (SemanticHom.teleProjection hΔ).typed (pps p) using 1 <;>
      simp [RawCtx.Hom.teleProjection, CtorSig.caseParams,
        CtorSig.fieldParams, Expr.wkN_eq_rename, Expr.rename_rename, Expr.subst_vars]
    · rfl
    · congr
      funext v
      simp [CtorSig.caseParams, CtorSig.fieldParams, Expr.wkN_eq_rename, Expr.rename_rename, Ren.wkN]
      rfl
  have hctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) := hB.ordinaryClosedWF s c ls k hk
  have pctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) :=
      hsound.ordinaryPrefixProperties η hI hblock s c ls k hk
  have pfield (g : Fin (ι.ctors s c).nfields) :=
      hsound.ordinaryTypeJudgment η hI hblock s c ls g
  have pfvar (g : Fin (ι.ctors s c).nfields) : RawTyped Γ₁' ((ι.ctors s c).caseOrdinary g)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).caseParams ps)
        (ι.ctors s c).caseOrdinary g) := by
    have pv := (RawJudgment.var (Γ₁ := CtxCat.ctorFields hdata s c)
      (hR.append (by simpa using pΔ.of_append.1))
      (fieldVar hdata s c (Fin.castAdd (ι.ctors s c).nrecFields g))).toRawTyped
    rw [CtxCat.ctorFields_get_ordinary] at pv
    have q := (SemanticHom.teleProjection
      ((hB.ctors s c).ihTele hB Γ₁.as.wf hps hms)).typed pv
    simp only [Ctor.ordinaryFieldExpr_subst, RawCtx.Hom.teleProjection, Expr.subst_vars] at q
    convert q using 1 <;>
      simp [Γ₁', Inductive.caseTele, ms,
        Tele.append_assoc, CtorSig.caseOrdinary, CtorSig.fieldOrdinary]
    · rfl
    congr 2 <;> funext v <;>
    · simp [CtorSig.caseParams, CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.wkN_eq_rename]
      rfl
  have hparams (p) := (pps' p).typed
  have hord (g) := (pfvar g).typed
  have hidx : ((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).caseParams ps)
      (ι.ctors s c).caseOrdinary = hs.indices := funext hs.no_indices.elim
  have pmaj' := RawTyped.ctor (recFds₁ := hs.recursive) hsound hI hblock hB pps' pfvar hs.no_recursive.elim
  rw [hidx] at pmaj'
  have hmaj' := pmaj'.typed
  have pbody' := structure_projection_body_properties hsound hI hblock hs hB hR' pps' pmaj' f hprev
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
    rw [hmsw, HasEquality.structure_projection_motive_beta hs hparams pmaj' f pbody'.term.ideal pbody'.term.subst σ ρ hρ,
      hs.projType_eq]
    let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls ((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩
    have hprojTyped (g : Fin f.val) :=
      hs.projTerm_hasTypeStrong hB (g.castLE f.isLt.le) Γ₁'.as.wf hparams hmaj'
    simp only [hs.projType_eq] at hprojTyped
    let σ₁ : Γ₁'.as ⟶ Src.as := ⟨Fin.append ((ι.ctors s c).caseParams ps) fun g : Fin f.val =>
        hs.projTerm η ls ((ι.ctors s c).caseParams ps) (g.castLE f.isLt.le)
          (.ctor η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary hs.recursive),
      Ctor.forall_ordinarySubst f.isLt.le hparams hprojTyped⟩
    let σ₂ : Γ₁'.as ⟶ Src.as := ⟨Fin.append ((ι.ctors s c).caseParams ps) fun g : Fin f.val =>
        (ι.ctors s c).caseOrdinary (g.castLE f.isLt.le),
      Ctor.forall_ordinarySubst f.isLt.le hparams fun _ => hord _⟩
    have hσ : RawCtx.toCtx.map σ₁ = RawCtx.toCtx.map σ₂ :=
      (RawCtx.toCtx_map_eq_iff σ₁ σ₂).mpr
        (Ctor.forall_ordinarySubst f.isLt.le hparams hiota)
    have hpf (g : Fin f.val) := (hprev' g).fixed
    simp only [hs.projType_eq] at hpf
    have hctor : CtorTyping Γ₁' η s c ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary
        hs.recursive := ⟨hord, hs.no_recursive.elim⟩
    have hv := Ctor.forall_ordinarySubst
        (motive := fun e₁ e₂ t => RawInterpretationProperties Γ₁' e₁ ∧
          RawInterpretationProperties Γ₁' e₂ ∧ HasEquality Γ₁' e₁ e₂ ∧ HasFixedness Γ₁' e₁ t)
        f.isLt.le
        (fun p => ⟨(pps' p).term, (pps' p).term, HasEquality.refl _ _, (pps' p).fixed⟩)
        (fun g => ⟨(hprev' g).term, (pfvar _).term, fun _ σ' ρ' hρ' => by
          rw [(hprev' g).value σ' ρ' hρ', rawInterpret_ctor_typed _ hctor hcarrier,
            RawFamily.ctor_value, RawValue.proj_ctor, Fin.append_left], hpf g⟩)
    exact HasSubstitution.congrImages (pfield f (hctx _ _)).left.subst (pctx _ _) σ₁ σ₂ hσ
      (fun v => (hv v).1.ideal) (fun v => (hv v).1.subst) (fun v => (hv v).2.1.subst)
      (fun v => (hv v).2.2.2) (fun v => (hv v).2.2.1) σ ρ hρ
  change RawTyped Γ₁ (Ctx.lam ((ι.ctors s c).caseOrdinary f) ((E₂.get η).block.caseTele η ls ps ms s c))
    (Ctx.pi ((E₂.get η).block.caseType η ls ps ms s c) ((E₂.get η).block.caseTele η ls ps ms s c))
  exact RawTyped.ctxLam _ hΔ pΔ ⟨.defeqDF hresult.symm (hord f),
    hsound.caseTypeProperties hI hblock hdata pps pms s c Γ₁'.as.wf,
    (pfvar f).term, (pfvar f).fixed.convert (.ofDefEq hresult.symm) hteq.symm⟩

theorem structure_projection_recrArgs (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
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
  have hps (p : Fin ι.nparams) := (pps p).typed
  have hA := hs.indTypeStrong (η := η) hps
  have pbody := structure_projection_body_properties hsound hI hblock hs hB hR pps pmaj f hprev
  have pms (t : Fin ι.nsorts) : RawTyped Γ₁ (hs.projectionMotives η ls ps f t)
      ((E₂.get η).block.motiveType η ls ps
        ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) t) := by
    obtain rfl := hs.sort_unique t
    rw [hs.projectionMotives_self, hs.motiveType_self]
    exact pbody.lam hA pmaj.type
  refine Inductive.forall_recrSubst
    (motive := fun _ e₁ _ t => RawInterpretationProperties Γ₁ e₁ ∧ HasFixedness Γ₁ e₁ t)
    (ps₂ := ps) (ms₂ := hs.projectionMotives η ls ps f)
    (mins₂ := hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f))
    (is₂ := hs.indices) (maj₂ := maj)
    (fun p => ⟨(pps p).term, (pps p).fixed⟩) (fun t => ⟨(pms t).term, (pms t).fixed⟩)
    (fun t d => ?_) hs.no_indices.elim ⟨pmaj.term, pmaj.fixed⟩ v
  obtain rfl := hs.sort_unique t
  obtain rfl := hs.ctor_unique d
  have pc := RawTyped.structure_projection_case hsound hI hblock hs hB hR pps f hrel pms hprev
  exact ⟨pc.term, pc.fixed⟩

end Metalean.CoherentShape
