module

public import Metalean.Strong.Inductive
public import Metalean.Semantics.Soundness.Context.Ordinary
public import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Interpretation.Computation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ ι} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
  {ctor : Ctor ζ ι s csig} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {fds : Fin csig.nfields → Expr ζ ℓ Γ₁.as.len}

theorem ordinaryField_properties (f : Fin csig.nfields)
    (hctx : E[Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le)] ⊢ₛ ok)
    (pctx : RawTeleProperties E .nil
      (Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le)))
    (pfield : RawJudgment
      (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx⟩ : CtxCat E ℓ)
      ((ctor.ordinaryType f).instL ls) ((ctor.ordinaryType f).instL ls)
      (.sort ((ctor.ordinary f).level.inst ls)))
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : I.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (hpsfixed : ∀ p, HasFixedness Γ₁ (ps p) (I.paramType ls ps p))
    (hprevious : ∀ g : Fin f.val, E[Γ₁.as.ctx] ⊢ₛ fds (g.castLE f.isLt.le) :
      ctor.ordinaryFieldExpr ls ps fds (g.castLE f.isLt.le))
    (pprevious : ∀ g : Fin f.val, RawInterpretationProperties Γ₁ (fds (g.castLE f.isLt.le)))
    (hpreviousFixed : ∀ g : Fin f.val, HasFixedness Γ₁ (fds (g.castLE f.isLt.le))
      (ctor.ordinaryFieldExpr ls ps fds (g.castLE f.isLt.le))) :
    RawInterpretationProperties Γ₁ (ctor.ordinaryFieldExpr ls ps fds f) ∧
      HasFixedness Γ₁ (ctor.ordinaryFieldExpr ls ps fds f) (.sort ((ctor.ordinary f).level.inst ls)) :=
  let Src : CtxCat E ℓ := ⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx⟩
  let σ : Γ₁.as ⟶ Src.as := ⟨Fin.append ps fun g : Fin f.val => fds (g.castLE f.isLt.le),
    Ctor.ordinarySubstWFStrong f.isLt.le hps hprevious⟩
  have pσ (v : Var Src.as.len) : RawInterpretationProperties Γ₁ (σ.subst v) := by
    cases v using Fin.addCases with
    | left p => simpa only [σ, Fin.append_left] using pps p
    | right g => simpa only [σ, Fin.append_right] using pprevious g
  have hf (v : Var Src.as.len) : HasFixedness Γ₁ (σ.subst v) ((Src.as.ctx.get v).subst σ.subst) := by
    change HasFixedness Γ₁ (σ.subst v)
      ((Ctx.get v (Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le))).subst σ.subst)
    rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
    cases v using Fin.addCases with
    | left p =>
      rw [Ctx.entry_append_left I.params _ (by omega) p.isLt
        (show p.val < ι.nparams + f.val by omega)]
      simp only [σ, Fin.append_left, Fin.append_castLE_left ps _ p.isLt.le]
      exact hpsfixed p
    | right g =>
      rw [Ctx.entry_append_right I.params _ (by omega) (by simp) (by omega)]
      simp [σ]
      exact hpreviousFixed g
  have hσ := SemanticHom.ofImages hctx pctx σ pσ hf
  ⟨hσ.props pfield.left, hσ.fixed pfield.syntactic.left (HasSubstitution.sort Src _)
    pfield.left.subst pfield.fixed⟩

theorem rawExtend_ordinaryFieldExpr_of_admissible
    (hctx : ∀ k (hk : k ≤ csig.nfields),
      E[Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux k hk)] ⊢ₛ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : I.paramType ls ps p)
    (hf : ∀ f, E[Γ₁.as.ctx] ⊢ₛ fds f : ctor.ordinaryFieldExpr ls ps fds f)
    (f : Fin csig.nfields)
    (pfield : HasSubstitution
      (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩ : CtxCat E ℓ)
      ((ctor.ordinaryType f).instL ls))
    (rps : ∀ p, HasSubstitution Γ₁ (ps p))
    (rprevious : ∀ g : Fin f.val, HasSubstitution Γ₁ (fds (g.castLE f.isLt.le)))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (args : Fin csig.nfields → RawValue Γ₂)
    (hargs : ∀ g : Fin f.val,
      (rawInterpret (piLimit E ℓ) Γ₁ (fds (g.castLE f.isLt.le))).app _ σ₁.op ρ = args (g.castLE f.isLt.le))
    (hadm : SourceAdmissible
      (σ₁ ≫ RawCtx.toCtx.map
        (⟨Fin.append ps fds, Ctor.targetSubstWFStrong hps hf⟩ : Γ₁.as ⟶
          (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTele), hctx _ le_rfl⟩ : CtxCat E ℓ).as))
      ((RawValuation.pushFin (fun _ => ⊥) fun p =>
        (rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ).pushFin args)) :
    (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Γ₁ (ctor.ordinaryFieldExpr ls ps fds f)).app _ σ₁.op ρ)
      ((Tm E ℓ).map σ₁.op (Tm.label Γ₁.as (hf f))) (args f) = args f := by
  let Src : CtxCat E ℓ := ⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩
  let vals : RawValuation Γ₂ := RawValuation.pushFin (fun _ => ⊥) fun p =>
    (rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ
  let σ₂ : Γ₁.as ⟶ Src.as := ⟨Fin.append ps fun g : Fin f.val => fds (g.castLE f.isLt.le),
    Ctor.ordinarySubstWFStrong f.isLt.le hps fun g => hf (g.castLE f.isLt.le)⟩
  have hfull := hctx (f.val + 1) f.isLt
  change E[Src.as.ctx.snoc ((ctor.ordinaryType f).instL ls)] ⊢ₛ ok at hfull
  have .snoc _ ⟨u, ht⟩ := hfull
  let σ₂' : Γ₁.as ⟶ (Src.extension ht).as :=
    ⟨Fin.append (m := ι.nparams) (n := f.val + 1) ps fun g : Fin (f.val + 1) => fds (g.castLE f.isLt),
      Ctor.ordinarySubstWFStrong f.isLt hps fun g => hf (g.castLE f.isLt)⟩
  have hprefix := SourceAdmissible.ordinaryPrefix (ctor := ctor) le_rfl
    (hctx _ le_rfl) hps hf σ₁ vals args hadm (f.val + 1) f.isLt hfull
  have hover : RawCtx.toCtx.map σ₂' ≫ Src.rawProjection ht = RawCtx.toCtx.map σ₂ := by
    change RawCtx.toCtx.map σ₂' ≫ RawCtx.toCtx.map (Src.projectionRaw ht) = _
    rw [← RawCtx.toCtx.map_comp]
    exact congrArg RawCtx.toCtx.map (RawCtx.Hom.ext (funext fun v =>
      Fin.append_castLE_right ps (fun g => fds (g.castLE f.isLt)) (Nat.le_succ f.val) v))
  have ⟨htail, _, _, hfixed⟩ := (SourceAdmissible.cons_iff ht (σ₁ ≫ RawCtx.toCtx.map σ₂')
    ((vals.pushFin fun g : Fin f.val => args (g.castLE f.isLt.le)).push (args f))).mp hprefix
  rw [Category.assoc, hover] at htail hfixed
  have hr (v : Var Src.as.len) : HasSubstitution Γ₁ (σ₂.subst v) := by
    cases v using Fin.addCases with
    | left p => simp [σ₂]; exact rps p
    | right g => simp [σ₂]; exact rprevious g
  have hs := SemanticSubstitution.ofHom (hctx _ _) σ₂ σ₁ ρ hr hρ
  have hv : (fun v => (rawInterpret (piLimit E ℓ) Γ₁ (σ₂.subst v)).app _ σ₁.op ρ) =
      Fin.append (fun p => (rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ)
        fun g => args (g.castLE f.isLt.le) := by
    funext v
    cases v using Fin.addCases with
    | left p => simp [σ₂]
    | right g => simpa [σ₂] using hargs g
  rw [hv, RawValuation.pushFin_append] at hs
  have htype : (rawInterpret (piLimit E ℓ) Γ₁ (ctor.ordinaryFieldExpr ls ps fds f)).app _ σ₁.op ρ =
      _ := pfield σ₂ σ₁ _ ρ hs htail
  rw [htype]
  have hname : (Tm E ℓ).map (σ₁ ≫ RawCtx.toCtx.map σ₂').op
      (CtxCat.rawComprehension ht).generic = (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as (hf f)) := by
    rw [CtxCat.rawComprehension_generic, op_comp, Functor.map_comp_apply, Tm.map_varLabel]
    apply congrArg ((Tm E ℓ).map σ₁.op)
    change Tm.label Γ₁.as (σ₂'.typed (Fin.last Src.as.len)) = _
    have he : σ₂'.subst (Fin.last Src.as.len) = fds f := by
      change Fin.append ps (fun g : Fin (f.val + 1) => fds (g.castLE f.isLt))
        (Fin.natAdd ι.nparams (Fin.last f.val)) = _
      rw [Fin.append_right]
      rfl
    have hget : ((Src.extension ht).as.ctx.get (Fin.last Src.as.len)).subst σ₂'.subst =
        ctor.ordinaryFieldExpr ls ps fds f := by
      change ((Src.as.ctx.snoc ((ctor.ordinaryType f).instL ls)).get
        (Fin.last Src.as.len)).subst σ₂'.subst = _
      rw [Ctx.get_last, Expr.wk_subst]
      apply congrArg fun σ₃ => ((ctor.ordinaryType f).instL ls).subst σ₃
      funext v
      change σ₂'.subst v.castSucc = σ₂.subst v
      exact Fin.append_castLE_right ps (fun g => fds (g.castLE f.isLt)) (Nat.le_succ f.val) v
    apply Tm.label_eq
    · rw [hget]
      exact IsTypeStrong.isTypeEq ⟨_, (hf f).regular.choose_spec⟩
    · rw [he, hget]
      exact hf f
  rwa [hname] at hfixed

theorem ordinaryField_eq_bot_of_admissible
    (hctx : ∀ k (hk : k ≤ csig.nfields),
      E[Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux k hk)] ⊢ₛ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : I.paramType ls ps p)
    (hf : ∀ f, E[Γ₁.as.ctx] ⊢ₛ fds f : ctor.ordinaryFieldExpr ls ps fds f)
    (f : Fin csig.nfields)
    (pfield : RawJudgment
      (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩ : CtxCat E ℓ)
      ((ctor.ordinaryType f).instL ls) ((ctor.ordinaryType f).instL ls)
      (.sort ((ctor.ordinary f).level.inst ls)))
    (hrel : Level.rel ((ctor.ordinary f).level.inst ls) = false)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (args : Fin csig.nfields → RawValue Γ₂)
    (hadm : SourceAdmissible
      (σ₁ ≫ RawCtx.toCtx.map
        (⟨Fin.append ps fds, Ctor.targetSubstWFStrong hps hf⟩ : Γ₁.as ⟶
          (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTele), hctx _ le_rfl⟩ : CtxCat E ℓ).as))
      (ρ.pushFin args)) : args f = ⊥ := by
  let Src : CtxCat E ℓ := ⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le), hctx _ _⟩
  have ht : E[Src.as.ctx] ⊢ₛ (ctor.ordinaryType f).instL ls :
      .sort ((ctor.ordinary f).level.inst ls) := pfield.syntactic.left
  let σ₂ : Γ₁.as ⟶ (Src.extension ht).as :=
    ⟨Fin.append (m := ι.nparams) (n := f.val + 1) ps
      fun g : Fin (f.val + 1) => fds (g.castLE f.isLt),
      Ctor.ordinarySubstWFStrong f.isLt hps fun g => hf (g.castLE f.isLt)⟩
  have hprefix := SourceAdmissible.ordinaryPrefix (ctor := ctor) le_rfl
    (hctx _ le_rfl) hps hf σ₁ ρ args hadm (f.val + 1) f.isLt (hctx _ _)
  have hsource := (SourceAdmissible.cons_iff ht (σ₁ ≫ RawCtx.toCtx.map σ₂)
    ((ρ.pushFin fun g : Fin f.val => args (g.castLE f.isLt.le)).push (args f))).mp hprefix
  have hsort := pfield.fixed ht _ _ hsource.1
  have hz : (ctor.ordinary f).level.inst ls = .zero := by simpa using hrel
  rw [rawInterpret_sort, RawFamily.sort_value] at hsort
  conv_lhs at hsort => arg 2; rw [hz]
  exact hsource.2.2.2.symm.trans (piLimit_rawExtend_prop _ hsort _ _)

end Metalean.CoherentShape
