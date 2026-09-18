/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Beta
import Metalean.Strong.InstLevel

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf CoherentShape CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {Γ₁ Γ₂ : CtxCat E₂ ℓ}

namespace CoherentShape

theorem ctorFieldTypes_value_isDirected (c : Fin (ι.nctors s))
    (hfn : HasIdeality (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s c).instL ls))
    (names : Fin ι.nparams → Tm_ Γ₁) (args : Fin ι.nparams → RawFamily Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (ha : ∀ p, ((args p).app _ σ.op ρ).IsDirected) :
    ((RawFamily.closedApps
      (rawInterpret (piLimit E₂ ℓ) (CtxCat.nil E₂ ℓ) (((E₂.get η).block.ctorTypeFn s c).instL ls))
      names args).app _ σ.op ρ).IsDirected := by
  rw [RawFamily.closedApps_value]
  exact rawApps_isDirected ⟨_, hfn _ _ (.nil _ _)⟩ _ fun p => ⟨_, ha p⟩

def ctorTargetHom {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[Ctx.instL ls (E₂.get η).block.params] ⊢ₛ ok)
    (hΔ : WFTeleStrong E₂ (fun _ => True) (Ctx.instL ls (E₂.get η).block.params)
      (Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele))
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (hf : ∀ f, E₂[Γ₁.as.ctx] ⊢ₛ fds f : ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f) :
    Γ₁.as ⟶ (CtxCat.extendTele ⟨Ctx.instL ls (E₂.get η).block.params, hctx⟩ _ hΔ).as :=
  ⟨Fin.append ps fds, by simpa [CtxCat.extendTele] using Ctor.targetSubstWFStrong hps hf⟩

def ctorParamHom {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[Ctx.instL ls (E₂.get η).block.params] ⊢ₛ ok)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p) :
    Γ₁.as ⟶ (⟨Ctx.instL ls (E₂.get η).block.params, hctx⟩ : CtxCat E₂ ℓ).as :=
  ⟨ps, (Inductive.paramSubstEqStrong hps).left⟩

theorem ctorFieldTypes_eq_pi {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[Ctx.instL ls (E₂.get η).block.params] ⊢ₛ ok)
    (hΔ : WFTeleStrong E₂ (fun _ => True) (Ctx.instL ls (E₂.get η).block.params)
      (Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele))
    (pctx : RawTeleProperties E₂ .nil (Ctx.instL ls (E₂.get η).block.params))
    (pbody : RawInterpretationProperties (⟨Ctx.instL ls (E₂.get η).block.params, hctx⟩ : CtxCat E₂ ℓ)
      (Expr.instL ls (((E₂.get η).block.ctors s c).ordinaryTele.pi (.sort (E₂.get η).block.level))))
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (fps : ∀ p, HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (hf : ∀ f, E₂[Γ₁.as.ctx] ⊢ₛ fds f : ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)) ≫
        RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
      σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps) ∧
    (RawFamily.closedApps
      (rawInterpret (piLimit E₂ ℓ) (CtxCat.nil E₂ ℓ) (((E₂.get η).block.ctorTypeFn s c).instL ls))
      (fun p => Tm.label Γ₁.as (hps p)) fun p => rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ =
      (rawInterpret (piLimit E₂ ℓ) ⟨_, hctx⟩ (Ctx.pi (.sort ((E₂.get η).block.level.inst ls))
        (Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele))).app _
        (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps)).op
        (RawValuation.pushFin (fun _ => ⊥) fun p =>
          (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ) ∧
    SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps))
      (RawValuation.pushFin (fun _ => ⊥) fun p =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ) ∧
    (fun f => (Tm E₂ ℓ).map (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)).op
        (Tm.varLabel (CtxCat.extendTele ⟨_, hctx⟩ _ hΔ) (Fin.natAdd ι.nparams f))) =
      fun f => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hf f)) := by
  have hadm := pctx.admissible_of_images hctx (ctorParamHom hctx hps) σ₁ ρ hρ (fun v => (pps v).ideal)
    (fun v => (pps v).subst) fun v => by
      change HasFixedness Γ₁ (ps v) _
      rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
      exact fps v
  have hproj : RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf) ≫
      RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) = RawCtx.toCtx.map (ctorParamHom hctx hps) :=
    (RawCtx.toCtx.map_comp _ _).symm.trans
      (congrArg RawCtx.toCtx.map (RawCtx.Hom.ext (funext fun v => Fin.append_left ps fds v)))
  refine ⟨(Category.assoc _ _ _).trans (congrArg (σ₁ ≫ ·) hproj), ?_, hadm, funext fun f => ?_⟩
  · have hb := rawInterpret_ctxLam_beta hctx pctx _ pbody (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps)) (fun _ => ⊥) _
      hadm
    have hn : (fun p => (Tm E₂ ℓ).map (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps)).op
        (Tm.varLabel (⟨_, hctx⟩ : CtxCat E₂ ℓ) p)) =
        fun p => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hps p)) := by
      funext p
      rw [op_comp, Functor.map_comp_apply, Tm.map_varLabel]
      refine congrArg _ (Tm.label_congr ?_)
      change ((Ctx.instL ls (E₂.get η).block.params).get p).subst ps = _
      rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    rw [hn] at hb
    rw [RawFamily.closedApps_value]
    simpa [ctorParamHom, Inductive.ctorTypeFn, CtxCat.hom_nil_eq (σ₁ ≫ CtxCat.toNil Γ₁) (CtxCat.toNil Γ₂),
      Expr.instL] using hb
  · rw [op_comp, Functor.map_comp_apply, Tm.map_varLabel]
    simp only [ctorTargetHom, Fin.append_right]
    apply congrArg ((Tm E₂ ℓ).map σ₁.op)
    apply Tm.label_congr
    change (Ctx.get (Fin.natAdd ι.nparams f) (Ctx.instL ls (E₂.get η).block.params ++
      Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele)).subst (Fin.append ps fds) = _
    rw [← Ctx.instL_append, Ctx.get_subst _ _ _ (ι.nparams + f.val) (by omega) rfl,
      ← Ctx.entry_instL, Ctx.entry_append_right (E₂.get η).block.params _ (by omega) (by simp)
        (by omega)]
    simp [Ctor.ordinaryTele, Ctor.ordinaryFieldExpr]

theorem ctorSourceJudgment
    {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawJudgment Γ₁ (fds f) (fds f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f))
    (v : Var (ι.nparams + (ι.ctors s c).nfields)) :
    RawJudgment Γ₁ ((Fin.append ps fds) v) ((Fin.append ps fds) v)
      (((Ctx.instL ls ((E₂.get η).block.params ++
        ((E₂.get η).block.ctors s c).ordinaryTele)).get v).subst (Fin.append ps fds)) := by
  rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
  cases v using Fin.addCases with
  | left p => simpa [Inductive.paramType, Ctx.entry, Tele.append] using pps p
  | right f =>
    rw [Ctx.entry_append_right (E₂.get η).block.params _ (by omega) (by simp) (by omega)]
    simpa [Ctor.ordinaryTele, Ctor.ordinaryFieldExpr] using pf f

end CoherentShape

theorem RawSound.ctorTypeFnProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (d : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) :
    RawInterpretationProperties (CtxCat.nil E₂ ℓ)
      (((I.map pre.sigs).ctorTypeFn s d).instL ls) := by
  have ⟨_, hf⟩ := hB.ctorTypeFn s d
  have p := (hsound.properties .nil rfl .nil (hf.instLevel ls)).left
  simpa [← Inductive.ctorTypeFn_map, ← Expr.map_instL, Ctx.map, CtxCat.nil] using p

theorem RawSound.ctorFieldProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (hctx : E₂[Ctx.instL ls (I.map pre.sigs).params] ⊢ₛ ok) :
    RawInterpretationProperties (⟨Ctx.instL ls (I.map pre.sigs).params, hctx⟩ : CtxCat E₂ ℓ)
      ((((I.map pre.sigs).ctors s c).ordinaryTele.pi (.sort I.level)).instL ls) :=
  have hp : E₁[I.params] ⊢ₛ ok := by
    simpa using WFTeleStrong.appendCtxWFStrong hB.params .nil
  have hfields := WFTeleStrong.appendCtxWFStrong
    ((hB.ctors s c).ordinaryTeleAuxStrong _ le_rfl) hp
  have ⟨u, ht⟩ := Ctx.pi_isTypeStrong hfields (.sortDF)
  have p := (hsound.properties (hp.instLevel ls)
    (Ctx.map_instL pre.sigs ls I.params) hctx (ht.instLevel ls)).left
  have he :=
    (Expr.map_instL pre.sigs ls ((I.ctors s c).ordinaryTele.pi (.sort I.level))).trans
      (congrArg (Expr.instL ls) ((Ctx.map_pi pre.sigs _ _).trans
        (congrArg (Ctx.pi (.sort I.level))
          (Ctor.ordinaryTele_map pre.sigs (I.ctors s c)))))
  (congrArg (RawInterpretationProperties (⟨_, hctx⟩ : CtxCat E₂ ℓ)) he).mp p

theorem RawSound.ordinaryPrefixProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (count : Nat) (hcount : count ≤ (ι.ctors s c).nfields) :
    RawTeleProperties E₂ .nil (Ctx.instL ls ((I.map pre.sigs).params ++
      ((I.map pre.sigs).ctors s c).ordinaryTeleAux count hcount)) :=
  have hfields := (hB.ctors s c).ordinaryTeleAuxStrong count hcount
  (congrArg (RawTeleProperties E₂ .nil)
    ((Ctx.map_instL pre.sigs ls _).trans (congrArg (Ctx.instL ls)
      ((Ctx.map_append pre.sigs _ _).trans
        (congrArg (Tele.append (I.params.map pre.sigs))
          (Ctor.ordinaryTeleAux_map pre.sigs (I.ctors s c) count hcount)))))).mp <|
    hsound.teleProperties .nil
      ((hB.params.append (by simpa using hfields)).instLevel (Q := fun _ => True) ls fun _ => trivial)

theorem RawSound.ordinaryTypeJudgment (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (f : Fin (ι.ctors s c).nfields)
    (hctx : E₂[Ctx.instL ls ((I.map pre.sigs).params ++
      ((I.map pre.sigs).ctors s c).ordinaryTeleAux f.val f.isLt.le)] ⊢ₛ ok) :
    RawJudgment
      (⟨Ctx.instL ls ((I.map pre.sigs).params ++
        ((I.map pre.sigs).ctors s c).ordinaryTeleAux f.val f.isLt.le), hctx⟩ : CtxCat E₂ ℓ)
      ((((I.map pre.sigs).ctors s c).ordinaryType f).instL ls)
      ((((I.map pre.sigs).ctors s c).ordinaryType f).instL ls)
      (.sort ((((I.map pre.sigs).ctors s c).ordinary f).level.inst ls)) := by
  have hsrc := hB.ordinaryClosedWF s c ls f.val f.isLt.le
  have hmap : (Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTeleAux f.val f.isLt.le)).map pre.sigs = Ctx.instL ls ((I.map pre.sigs).params ++
        ((I.map pre.sigs).ctors s c).ordinaryTeleAux f.val f.isLt.le) :=
    (Ctx.map_instL pre.sigs ls _).trans (congrArg (Ctx.instL ls)
      ((Ctx.map_append pre.sigs _ _).trans
        (congrArg (Tele.append (I.params.map pre.sigs))
          (Ctor.ordinaryTeleAux_map pre.sigs (I.ctors s c) f.val f.isLt.le))))
  simpa [Inductive.map, Ctor.ordinaryType, Ctor.map, Field.map,
    Expr.map, Expr.instL] using
    hsound.properties hsrc hmap hctx (((hB.ctors s c).ordinary f).typeExact.instLevel ls)

theorem Inductive.WFStrong.ordinaryTeleInstL {J : Inductive ζ₂ ι} (hJ : J.WFStrong E₂)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) :
    WFTeleStrong E₂ (fun _ => True) (Ctx.instL ls J.params)
      (Ctx.instL ls ((J.ctors s c).ordinaryTele)) := by
  simpa [Ctor.ordinaryTele] using
    ((hJ.ctors s c).ordinaryTeleAuxStrong _ le_rfl).instLevel
      ls fun _ => trivial

section Block

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
  (hblock : (E₂.get η).block = I.map pre.sigs) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (ls : Fin ι.nlevels → Level ℓ)

include hsound hB hblock

variable (η)

theorem RawSound.blockCtorTypeFnProperties :
    RawInterpretationProperties (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s c).instL ls) := by
  rw [hblock]
  exact hsound.ctorTypeFnProperties hB s c ls

theorem RawSound.blockCtorFieldProperties
    (hctx : E₂[Ctx.instL ls (E₂.get η).block.params] ⊢ₛ ok) :
    RawInterpretationProperties (⟨Ctx.instL ls (E₂.get η).block.params, hctx⟩ : CtxCat E₂ ℓ)
      ((((E₂.get η).block.ctors s c).ordinaryTele.pi (.sort (E₂.get η).block.level)).instL ls) := by
  revert hctx
  rw [hblock]
  exact hsound.ctorFieldProperties hB s c ls

theorem RawSound.blockOrdinaryTeleProperties :
    RawTeleProperties E₂ (Ctx.instL ls (E₂.get η).block.params)
      (Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele) := by
  rw [hblock]
  exact hsound.ordinaryTeleProperties hB s c ls

theorem RawSound.blockOrdinaryPrefixProperties (count : Nat)
    (hcount : count ≤ (ι.ctors s c).nfields) :
    RawTeleProperties E₂ .nil (Ctx.instL ls ((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux count hcount)) := by
  rw [hblock]
  exact hsound.ordinaryPrefixProperties hB s c ls count hcount

theorem RawSound.blockOrdinaryTypeJudgment (f : Fin (ι.ctors s c).nfields)
    (hctx : E₂[Ctx.instL ls ((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le)] ⊢ₛ ok) :
    RawJudgment
      (⟨Ctx.instL ls ((E₂.get η).block.params ++
        ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le), hctx⟩ : CtxCat E₂ ℓ)
      ((((E₂.get η).block.ctors s c).ordinaryType f).instL ls)
      ((((E₂.get η).block.ctors s c).ordinaryType f).instL ls)
      (.sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)) := by
  revert hctx
  rw [hblock]
  exact hsound.ordinaryTypeJudgment hB s c ls f

end Block

end Metalean
