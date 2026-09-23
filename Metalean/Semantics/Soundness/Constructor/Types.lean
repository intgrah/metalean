/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Beta
import Metalean.Typing.InstLevel

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf CoherentShape CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {Γ₁ Γ₂ : CtxCat E₂ ℓ}

namespace CoherentShape

def ctorTargetHom {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[(E₂.get η).block.params{ls}] ⊢ ok)
    (hΔ : TeleWF E₂ (fun _ => True) (E₂.get η).block.params{ls}
      ((E₂.get η).block.ctors s c).ordinaryTele{ls})
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p)
    (hf : ∀ f, E₂[Γ₁.as.ctx] ⊢ fds f : ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f) :
    Γ₁.as ⟶ (CtxCat.extendTele ⟨(E₂.get η).block.params{ls}, hctx⟩ _ hΔ).as :=
  ⟨Fin.append ps fds, by
    change E₂[Γ₁.as.ctx] ⊢ Fin.append ps fds ⊣
      (E₂.get η).block.params{ls} ++ ((E₂.get η).block.ctors s c).ordinaryTele{ls}
    rw [← Ctx.instL_append]
    exact Ctor.forall_ordinarySubst le_rfl hps hf⟩

def ctorParamHom {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[(E₂.get η).block.params{ls}] ⊢ ok)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p) :
    Γ₁.as ⟶ (⟨(E₂.get η).block.params{ls}, hctx⟩ : CtxCat E₂ ℓ).as :=
  ⟨ps, (Inductive.paramSubstEq hps).left⟩

theorem ctorFieldTypes_eq_pi {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
    (hctx : E₂[(E₂.get η).block.params{ls}] ⊢ ok)
    (hΔ : TeleWF E₂ (fun _ => True) (E₂.get η).block.params{ls}
      ((E₂.get η).block.ctors s c).ordinaryTele{ls})
    (pctx : RawTeleProperties E₂ .nil (E₂.get η).block.params{ls})
    (pbody : RawInterpretationProperties (⟨(E₂.get η).block.params{ls}, hctx⟩ : CtxCat E₂ ℓ)
      (((E₂.get η).block.ctors s c).ordinaryTele.pi (.sort (E₂.get η).block.level)){ls})
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (fps : ∀ p, HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (hf : ∀ f, E₂[Γ₁.as.ctx] ⊢ fds f : ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)) ≫
        RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
      σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps) ∧
    (RawFamily.closedApps
      (rawInterpret (piLimit E₂ ℓ) (CtxCat.nil E₂ ℓ) ((E₂.get η).block.ctorTypeFn s c){ls})
      (fun p => Tm.label Γ₁.as (hps p)) fun p => rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ =
      (rawInterpret (piLimit E₂ ℓ) ⟨_, hctx⟩ (Ctx.pi (.sort (E₂.get η).block.level{ls})
        ((E₂.get η).block.ctors s c).ordinaryTele{ls})).app _
        (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps)).op
        (RawValuation.pushFin (fun _ => ⊥) fun p =>
          (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ) ∧
    SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map (ctorParamHom hctx hps))
      (RawValuation.pushFin (fun _ => ⊥) fun p =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ) ∧
    (fun f => (Tm E₂ ℓ).map (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)).op
        (Tm.varLabel (CtxCat.extendTele ⟨_, hctx⟩ _ hΔ) (Fin.natAdd ι.nparams f))) =
      fun f => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hf f)) := by
  have hadm := pctx.admissible_of_images hctx (ctorParamHom hctx hps) σ₁ ρ hρ pps fun v => by
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
      rw [op_comp, Functor.map_comp_apply]
      refine congr((Tm E₂ ℓ).map σ₁.op (Tm.label _ (t := $(?_)) _))
      change ((E₂.get η).block.params{ls}.get p).subst ps = _
      rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    rw [hn] at hb
    rw [RawFamily.closedApps_value]
    simpa [ctorParamHom, Inductive.ctorTypeFn, CtxCat.hom_nil_eq (σ₁ ≫ CtxCat.toNil Γ₁) (CtxCat.toNil Γ₂),
      Expr.instL] using hb
  · rw [op_comp, Functor.map_comp_apply, Tm.map_varLabel]
    simp only [ctorTargetHom, Fin.append_right]
    apply congrArg ((Tm E₂ ℓ).map σ₁.op)
    refine congr(Tm.label _ (t := $(?_)) _)
    change (Ctx.get (Fin.natAdd ι.nparams f) ((E₂.get η).block.params{ls} ++
      ((E₂.get η).block.ctors s c).ordinaryTele{ls})).subst (Fin.append ps fds) = _
    rw [← Ctx.instL_append, Ctx.get_subst _ _ _ (ι.nparams + f.val) (by omega) rfl,
      ← Ctx.entry_instL, Ctx.entry_append_right (E₂.get η).block.params _ (by omega) (by simp)
        (by omega)]
    simp [Ctor.ordinaryFieldExpr]

end CoherentShape

variable (hsound : RawSound E₂ ℓ pre) (η) (hB : InductiveWF E₁ I)
  (hblock : (E₂.get η).block = I.map pre.sigs) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (ls : Fin ι.nlevels → Level ℓ)

include hsound hB hblock

theorem RawSound.ctorTypeFnProperties :
    RawInterpretationProperties (CtxCat.nil E₂ ℓ)
      ((E₂.get η).block.ctorTypeFn s c){ls} := by
  rw [hblock]
  have ⟨_, hf⟩ := hB.ctorTypeFn s c
  simpa using (hsound.properties .nil (hf.instLevel ls)).left

theorem RawSound.ctorFieldProperties
    (hctx : E₂[(E₂.get η).block.params{ls}] ⊢ ok) :
    RawInterpretationProperties (⟨(E₂.get η).block.params{ls}, hctx⟩ : CtxCat E₂ ℓ)
      (((E₂.get η).block.ctors s c).ordinaryTele.pi (.sort (E₂.get η).block.level)){ls} := by
  revert hctx
  rw [hblock]
  intro hctx
  have hp : E₁[I.params] ⊢ ok := by simpa using hB.params.appendCtxWF .nil
  have ⟨_, ht⟩ := Ctx.pi_isType (e := .sort I.level)
    (((hB.ctors s c).ordinaryTeleAux _ le_rfl).appendCtxWF hp) .sortDF
  convert (hsound.properties (hp.instLevel ls) (ht.instLevel ls)).left using 1 <;>
    simp [Inductive.map, Ctor.ordinaryTele, Expr.map]

theorem RawSound.ordinaryTeleProperties :
    RawTeleProperties E₂ (E₂.get η).block.params{ls}
      ((E₂.get η).block.ctors s c).ordinaryTele{ls} := by
  rw [hblock]
  have hΘ := ((hB.ctors s c).ordinaryTeleAux _ le_rfl).instLevel
    (Q := fun _ => True) ls fun _ => trivial
  simpa [Inductive.map, Ctor.ordinaryTele] using hsound.teleProperties (hB.paramClosedWF ls) hΘ

theorem RawSound.ordinaryPrefixProperties (count : Nat)
    (hcount : count ≤ (ι.ctors s c).nfields) :
    RawTeleProperties E₂ .nil ((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux count hcount){ls} := by
  rw [hblock]
  have hfields := (hB.ctors s c).ordinaryTeleAux count hcount
  have hp := hsound.teleProperties .nil
    ((hB.params.append (by simpa using hfields.mono fun _ => trivial)).instLevel
      (Q := fun _ => True) ls fun _ => trivial)
  simp only [Ctx.map_instL, Ctx.map_append, Ctor.ordinaryTeleAux_map] at hp
  exact hp

theorem RawSound.ordinaryTypeJudgment (f : Fin (ι.ctors s c).nfields)
    (hctx : E₂[((E₂.get η).block.params ++
      ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le){ls}] ⊢ ok) :
    RawJudgment
      (⟨((E₂.get η).block.params ++
        ((E₂.get η).block.ctors s c).ordinaryTeleAux f.val f.isLt.le){ls}, hctx⟩ : CtxCat E₂ ℓ)
      ((((E₂.get η).block.ctors s c).ordinary f).type{ls})
      ((((E₂.get η).block.ctors s c).ordinary f).type{ls})
      (.sort (((E₂.get η).block.ctors s c).ordinary f).level{ls}) := by
  revert hctx
  rw [hblock]
  intro hctx
  convert hsound.properties (hB.ordinaryClosedWF s c ls f.val f.isLt.le)
    (((hB.ctors s c).ordinary f).typeExact.instLevel ls) using 1 <;>
    simp [Inductive.map, Ctor.map, Field.map, Expr.map]

end Metalean
