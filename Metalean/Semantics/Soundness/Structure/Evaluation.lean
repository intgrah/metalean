/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Decoder
public import Metalean.Semantics.Soundness.Telescope.Substitution
public import Metalean.Semantics.Soundness.Structure.Projection
public import Metalean.Semantics.Soundness.Structure.Reconstruction
import Metalean.Typing.InstLevel
import Metalean.Semantics.Interpretation.Computation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len} {maj : Expr ζ₂ ℓ Γ₁.as.len}

theorem rawInterpret_structure_projection_of_previous
    (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : InductiveWF E₂ (E₂.get η).block)
    (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields) (hprev : StructureProjection.Prev hs ls f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ₁.op ρ =
      RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ) := by
  have hps (p : Fin ι.nparams) := (pps p).typed
  have pparams (p : Fin ι.nparams) := (pps p).term
  have fparams (p : Fin ι.nparams) :
      HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p) := (pps p).fixed
  have pfields := structure_field_telescope_properties hsound hI hblock hB hps pparams fparams
    (s := s) (c := c)
  have hcurrent (g : Fin f.val) := hprev g hR pps pmaj
  cases hcarrier : Level.rel ((E₂.get η).block.level.inst ls) with
  | false =>
    have hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = false := by
      cases hfrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) with
      | false => rfl
      | true => exact Bool.noConfusion (hcarrier.symm.trans (structure_carrier_relevant hs f hfrel))
    rw [hs.projTerm_eq_recr, rawInterpret_recr_prop _ hrel,
      pmaj.structural_value_bot hs hB hps hcarrier σ₁ ρ hρ]
    simp
    rfl
  | true =>
    have hΔ := (hB.ctors s c).ordinaryFieldTele (η := η) hps
    have hpctx := hB.paramClosedWF ls
    have hd := ((hB.ctors s c).ordinaryTeleAux _ le_rfl).instLevel (Q := fun _ => True) ls fun _ => trivial
    have ppctx := hsound.paramTeleProperties hI hblock ls
    have ppfields := hsound.ordinaryTeleProperties η hI hblock s c ls
    have ppbody := hsound.ctorFieldProperties η hI hblock s c ls
    have pfn (d : Fin (ι.nctors s)) : HasIdeality (CtxCat.nil E₂ ℓ)
        (((E₂.get η).block.ctorTypeFn s d).instL fun p => ls p) :=
      (hsound.ctorTypeFnProperties η hI hblock s d ls).ideal
    have hf (g : Fin (ι.ctors s c).nfields) : E₂[Γ₁.as.ctx] ⊢ hs.projTerm η ls ps g maj :
        ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps (fun g => hs.projTerm η ls ps g maj) g := by
      rw [← hs.projType_eq]
      exact hs.projTerm_hasType hB g Γ₁.as.wf hps pmaj.typed
    let T : Domain Γ₂ := ctorFieldTypes pfn (fun p => Tm.label Γ₁.as (hps p)) σ₁ ρ
      (fun p => (pparams p).ideal σ₁ ρ hρ) c
    have hfixed := pmaj.structural_field_telescope hs hB hcarrier pfn hps (fun p => (pparams p).ideal)
      σ₁ ρ hρ
    simp only [hs.projType_eq] at hfixed
    let args : Fin (ι.ctors s c).nfields → Domain Γ₂ :=
      fun g => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ g) (hρ.eval pmaj.term.ideal)
    have ⟨hproj, hT', hbase, hnames⟩ := ctorFieldTypes_eq_pi hpctx hd ppctx (ppbody hpctx)
      hps pparams fparams hf σ₁ ρ hρ
    rw [← hproj] at hT' hbase
    have hsource := (rawInterpret_ctxPi_decode _ hd ppfields
      (.sort ((E₂.get η).block.level.inst ls)) .sortDF (HasIdeality.sort _ _)
      (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hpctx hd hps hf)) _ args
      (by rw [← hT']; exact T.property)).2 hbase
      (congr(((piLimit E₂ ℓ).telescope $(Subtype.val_injective hT'.symm) $hnames args).1).trans hfixed)
    let square := (ctorParamHom hpctx hps).liftTele_isPullback hd
    let σ₂ : Γ₂ ⟶ CtxCat.extendTele Γ₁
        (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ :=
      square.lift (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hpctx hd hps hf)) σ₁ hproj
    have hlift := square.lift_fst (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hpctx hd hps hf)) σ₁ hproj
    have hover := square.lift_snd (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hpctx hd hps hf)) σ₁ hproj
    have ⟨_, hadm⟩ := SemanticSubstitution.liftTele _ hd ppfields (ctorParamHom hpctx hps)
      σ₂ (RawValuation.pushFin (fun _ => ⊥) fun p =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ) ρ (fun g => (args g).val)
      (by
        rw [hover]
        exact SemanticSubstitution.ofHom hpctx (ctorParamHom hpctx hps)
          σ₁ ρ (fun p => (pparams p).subst) hρ)
      (by rw [hover]; exact hρ) (by rw [hlift]; exact hsource)
    have hnames' g := congrArg ((Tm E₂ ℓ).map σ₂.op)
      (Tm.map_liftTele_varLabel (ctorParamHom hpctx hps) hd g)
    have hnames' g := ((Tm E₂ ℓ).map_comp_apply
      (RawCtx.toCtx.map ((ctorParamHom hpctx hps).liftTele hd)).op σ₂.op _).trans (hnames' g)
    have hnames' g := (congrArg (fun σ => (Tm E₂ ℓ).map σ.op
      (Tm.varLabel (CtxCat.extendTele ⟨_, hpctx⟩ _ hd) (Fin.natAdd ι.nparams g))) hlift.symm).trans (hnames' g)
    have hfixed := (ppctx.append (by simpa using ppfields)).fixed_image
      (CtxCat.extendTele ⟨_, hpctx⟩ _ hd).as.wf (ctorTargetHom hpctx hd hps hf)
      (f.natAdd ι.nparams)
      (fun v hv => by
        cases v using Fin.addCases with
        | left p => simpa [ctorTargetHom] using (pparams p).subst
        | right g =>
          simp only [ctorTargetHom, Fin.append_right]
          exact (hcurrent ⟨g.val, by exact Nat.lt_of_add_lt_add_left hv⟩).term.subst)
      σ₁ _ ρ hsource hρ (fun v hv => by
        rw [← RawValuation.pushFin_append, RawValuation.pushFin_variable]
        cases v using Fin.addCases with
        | left p => simp [ctorTargetHom]
        | right g =>
          simp only [ctorTargetHom, Fin.append_right]
          exact (hcurrent ⟨g.val, by exact Nat.lt_of_add_lt_add_left hv⟩).value σ₁ ρ hρ)
    simp only [← RawValuation.pushFin_append, RawValuation.pushFin_variable, Fin.append_right] at hfixed
    rw [← Tm.map_varLabel (ctorTargetHom hpctx hd hps hf), ← Functor.map_comp_apply,
      ← op_comp, congrFun hnames f] at hfixed
    dsimp only [ctorTargetHom, CtxCat.extendTele] at hfixed
    conv_lhs at hfixed =>
      arg 2
      rw [← Ctx.instL_append, Ctx.get_subst _ _ _ (ι.nparams + f.val) (by omega) rfl,
        ← Ctx.entry_instL, Ctx.entry_append_right _ _ (by omega) (by simp) (by omega)]
      simp
      rfl
    rw [← Ctor.ordinaryFieldExpr.eq_def ((E₂.get η).block.ctors s c) ls ps
      (fun g => hs.projTerm η ls ps g maj) f] at hfixed
    simp only [← hs.projType_eq] at hfixed
    cases hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) with
    | false =>
      have pt := structure_projection_type_properties hsound hI hblock hs hB pps f
        fun g => (hcurrent g).toRawTyped
      have hp := pt.fixed
      have ht := pt.typed
      have hz : (((E₂.get η).block.ctors s c).ordinary f).level.inst ls = .zero := by simpa using hrel
      rw [hz] at hp ht
      have hsrt := hp ht σ₁ ρ hρ
      rw [rawInterpret_sort] at hsrt
      rw [hs.projTerm_eq_recr, rawInterpret_recr_prop _ hrel]
      exact (piLimit_rawExtend_prop _ hsrt _ _).symm.trans hfixed
    | true =>
      have hn g := (hnames' g).symm.trans (congrFun hnames g)
      simp only [← hs.projType_eq] at hn
      have hargs := structure_projection_recrArgs hsound hI hblock hs hB hR pps pmaj f hrel hprev
      have pbody :=
        (structure_projection_body_properties hsound hI hblock hs hB hR pps pmaj f hprev).term
      let h := RecTyping.structure_projection hs hB hps pmaj.typed f
      have hpr := hs.projection_spec hB Γ₁.as.wf hps pmaj.typed f
      have hlabel : Tm.label Γ₁.as h.typed = Tm.label Γ₁.as hpr.term := by
        refine Quotient.sound ⟨.ofDefEq hpr.result, ?_⟩
        dsimp only [Tm.Repr.ty, Tm.Repr.val]
        simpa [hs.projTerm_eq_recr] using h.typed
      let ns : Fin (ι.ctors s c).nfields → Tm_ Γ₂ := fun i => (Tm E₂ ℓ).map σ₂.op
        (Tm.varLabel (CtxCat.extendTele Γ₁
          (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ) (Fin.natAdd Γ₁.as.len i))
      have hns : (fun i => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
          (hs.projTerm_hasType h.block i Γ₁.as.wf h.param h.major))) = ns :=
        funext fun i => (hn i).symm
      have hvals : (fun i => RawValue.proj (CtorHead.mk η s c) i
          ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ)) =
          Fin.append (fun i => (args i).val) hs.no_recursive.elim := by
        funext i
        cases i using Fin.addCases with
        | left i =>
          rw [Fin.append_left]
          rfl
        | right i => exact hs.no_recursive.elim i
      have hb := RawFamily.ctxLam_openBeta _ rfl hΔ pfields (Nat.lt_succ_self _)
        (rawInterpret (piLimit E₂ ℓ) (CtxCat.extendTele Γ₁ _ hΔ) (Expr.boundVars Γ₁.as.len (ι.ctors s c).nfields 0 f))
        (rawInterpret_isFinitary _ _ _) (RawInterpretationProperties.var _ _).ideal
        σ₂ ρ (fun i => (args i).val) hadm
      rw [← rawInterpret_ctxLam, ← hs.projectionCases_self (η := η) (ls := ls) (ps := ps) (f := f) (ms := hs.projectionMotives η ls ps f)] at hb
      rw [show σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) = σ₁ from hover] at hb
      simp [Expr.boundVars, RawFamily.lookup] at hb
      have he := RawSound.recr_structural hsound hI hblock hs h hrel (structure_carrier_relevant hs f hrel) (fun v => (hargs v).1) (fun v => (hargs v).2)
        σ₁ ρ hρ
      rw [HasEquality.structure_projection_motive_beta hs hps pmaj f pbody.ideal pbody.subst σ₁ ρ hρ, hlabel, hns,
        hvals, rawApps_append_no_recursive hs] at he
      dsimp only [ns] at he
      rw [hb] at he
      simp only [← hs.projTerm_eq_recr] at he
      exact he.trans hfixed

end Metalean.CoherentShape
