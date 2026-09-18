/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.FixedPoints
public import Metalean.Semantics.Interpretation.Family.Basic
public import Metalean.Semantics.Interpretation.Recursor.Case
public import Metalean.Semantics.Interpretation.Recursor.Recovery

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf IndSig TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {ι : IndSig} {η : Head ζ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}

theorem RawFamily.decode_mono_right (D : CodeAssignment E ℓ) (n : Tm_ Γ₁)
    (C : RawFamily Γ₁) {X₁ X₂ : RawFamily Γ₁} (hX : X₁ ≤ X₂) : decode D n C X₁ ≤ decode D n C X₂ :=
  fun _ _ _ => D.rawExtend_mono_right _ (hX _ _ _)

theorem RawActionFamily.apply_mono {F₁ F₂ : RawActionFamily Γ₁} (hF : F₁ ≤ F₂) (X : RawFamily Γ₁)
    (label : Tm_ Γ₁) : F₁.apply X label ≤ F₂.apply X label :=
  fun Y σ ρ => hF Y σ ρ _ ((𝟙 Y.unop).op, (Tm E ℓ).map σ label) (X.app Y σ ρ)

theorem RawFamily.decode_apply_iSup_le (D : CodeAssignment E ℓ) (n : Tm_ Γ₁)
    (C : RawFamily Γ₁) (F : Nat → RawActionFamily Γ₁) (X : RawFamily Γ₁)
    (label : Tm_ Γ₁) :
    decode D n C ((⨆ k, F k).apply X label) ≤ ⨆ k, decode D n C ((F k).apply X label) := by
  intro Y σ ρ Γ₃ σ₂ y hy
  have ⟨code, hcode, x, hx, hy⟩ := (D.mem_rawExtend ..).mp hy
  change (((⨆ k, F k).app _ σ ρ).app _ ((𝟙 Y.unop).op, (Tm E ℓ).map σ label)
    (X.app _ σ ρ)).mem σ₂ x at hx
  rw [RawActionFamily.iSup_app, RawAction.iSup_app] at hx
  have ⟨k, hx⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hx
  change ((⨆ k, decode D n C ((F k).apply X label)).app Y σ ρ).mem σ₂ y
  rw [RawFamily.iSup_app]
  exact (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨k, (D.mem_rawExtend ..).mpr ⟨code, hcode, x, hx, hy⟩⟩

@[implicit_reducible] def RecApprox (E : Env ζ) (ℓ : Nat) (ι : IndSig) : Type _ :=
  Fin ι.nsorts → RawFamily (CtxCat.nil E ℓ)

noncomputable instance : CompleteLattice (RecApprox E ℓ ι) :=
  inferInstanceAs (CompleteLattice (Fin ι.nsorts → RawFamily (CtxCat.nil E ℓ)))

theorem RecApprox.iSup_apply {κ : Sort*} (V : κ → RecApprox E ℓ ι) (t : Fin ι.nsorts) :
    (⨆ k, V k) t = ⨆ k, V k t := by
  simp [RecApprox]

section Rank

theorem recrTele_headRank_lt (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (s : Fin ι.nsorts) : ((E.get η).block.recrTele η s ls l).headRank < η.rank :=
  Head.lt_rank_of_le (Inductive.headRank_recrTele_le (E.get_block_headRank_lt η).le le_rfl)

theorem recrBody_headRank_lt (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) :
    (ι.recrBody s : Expr ζ ℓ _).headRank < η.rank :=
  Head.lt_rank_of_le (Expr.headRank_motiveResult_le (Expr.headRank_var_le _)
    (fun _ => Expr.headRank_var_le _) (Expr.headRank_var_le _))

variable (h : IndData Γ₁ η ls ps) (hps : ∀ p, (ps p).headRank ≤ η.rank - 1) (s : Fin ι.nsorts)
  (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields)

include hps

variable (Γ₁ ps) in
theorem fieldTele_headRank_lt : (((E.get η).block.ctors s c).fieldTele η ls ps).headRank < η.rank :=
  Head.lt_rank_of_le (Inductive.headRank_fieldTele_le (E.get_block_headRank_lt η).le le_rfl hps)

theorem fieldArgs_headRank_le (v : Fin (ι.nparams + (ι.ctors s c).nfields)) :
    (Fin.append ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary v).headRank ≤ η.rank - 1 :=
  Fin.headRank_append_le (fun p => by simpa [CtorSig.fieldParams] using hps p)
    (fun _ => by simp [CtorSig.fieldOrdinary, Expr.headRank]) v

theorem fieldTelescope_headRank_lt : (fieldTelescope h s c f).headRank < η.rank :=
  Head.lt_rank_of_le (RecField.headRank_instantiatedTelescope_le
    (Inductive.headRank_recursive_le (E.get_block_headRank_lt η).le f) (fieldArgs_headRank_le hps s c))

end Rank

section Step

variable (D : CodeAssignment E ℓ)
  (interp : (Γ₁ : CtxCat E ℓ) → (e : Expr ζ ℓ Γ₁.as.len) → e.headRank < η.rank → RawFamily Γ₁)
  (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ)

theorem ihSubst_headRank_lt (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields)
    (v : Fin (ι.recrEnd ((ι.ctors s c).recursiveTarget f))) :
    (Inductive.recrSubst
      (fun p => ((ι.ctors s c).fieldParams (fun p => .var (RecrBinder.param p).resolve) p).wkN
        ((ι.ctors s c).recursiveArity f))
      (fun t => (Expr.var (RecrBinder.motive t).resolve).subst
        (CtxCat.ctorFieldTargetHom (RecTyping.generic hd ls s).toIndData s c f).subst)
      (fun t c₁ => (Expr.var (RecrBinder.case t c₁).resolve).subst
        (CtxCat.ctorFieldTargetHom (RecTyping.generic hd ls s).toIndData s c f).subst)
      (fieldIndices (RecTyping.generic hd ls s).toIndData s c f)
      (appliedMajor (RecTyping.generic hd ls s).toIndData s c f) v).headRank < η.rank := by
  have hσ (w : Var (CtxCat.recr hd ls s).as.len) :
      ((CtxCat.ctorFieldTargetHom (RecTyping.generic hd ls s).toIndData s c f).subst w).headRank ≤
        η.rank - 1 := by
    simp [CtxCat.ctorFieldTargetHom, CtxCat.ctorFieldsProjection, RawCtx.Hom.teleProjection,
      Expr.headRank]
  exact Inductive.forall_recrSubst_image
    (fun p => Head.lt_rank_of_le (by simp [CtorSig.fieldParams, Expr.headRank]))
    (fun t => Head.lt_rank_of_le (Expr.headRank_subst_le _ _ _ (Expr.headRank_var_le _) hσ))
    (fun t c₁ => Head.lt_rank_of_le (Expr.headRank_subst_le _ _ _ (Expr.headRank_var_le _) hσ))
    (fun i => Head.lt_rank_of_le (RecField.headRank_instantiatedIndices_le
      (Inductive.headRank_recursive_le (E.get_block_headRank_lt η).le f)
      (fieldArgs_headRank_le (fun _ => Expr.headRank_var_le _) s c) i))
    (Head.lt_rank_of_le (by simp [appliedMajor, CtorSig.fieldRecursive, Expr.headRank])) v

noncomputable def recursorHyp (V : RecApprox E ℓ ι) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) : RawFamily (CtxCat.recr hd ls s) :=
  RawFamily.ctxLam D interp (CtxCat.recr hd ls s) _
    (((RecTyping.generic hd ls s).block.ctors s c).fieldTele rfl (CtxCat.recr hd ls s).as.wf
      (RecTyping.generic hd ls s).param)
    (fieldTele_headRank_lt (CtxCat.recr hd ls s) (fun p => .var (RecrBinder.param p).resolve)
      (fun _ => Expr.headRank_var_le _) s c)
    (RawFamily.ctxLam D interp (CtxCat.ctorFields (RecTyping.generic hd ls s).toIndData s c) _
      (fieldTelescopeStrong (RecTyping.generic hd ls s).toIndData s c f)
      (fieldTelescope_headRank_lt (RecTyping.generic hd ls s).toIndData (fun _ => Expr.headRank_var_le _) s c f)
      (RawFamily.closedApps (V ((ι.ctors s c).recursiveTarget f))
        (fun v => Tm.label (CtxCat.ctorFieldTarget (RecTyping.generic hd ls s).toIndData s c f).as
          (((RecTyping.generic hd ls s).toRecData.ihTyping s c f).recrSubstWF v))
        fun v => interp _ _ (ihSubst_headRank_lt hd ls s c f v)))

noncomputable def recursorPayload (V : RecApprox E ℓ ι) (s : Fin ι.nsorts) :
    RawFamily (CtxCat.recr hd ls s) :=
  (rawRecCaseFamily (RecTyping.generic hd ls s).toRecData
      (fun c => RawFamily.lookup (Var.db (RecrBinder.case (s := s) s c).resolve))
      (recursorHyp D interp hd ls V s)).apply
    (recoverMajor (RecTyping.generic hd ls s).toRecData s (𝟙 _)
      (fun i => Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index i).resolve)
      (fun i => RawFamily.lookup (Var.db (RecrBinder.index i).resolve))
      (RawFamily.lookup (Var.db (RecrBinder.major (s := s)).resolve)))
    (Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.major (s := s)).resolve)

noncomputable def recursorBody (V : RecApprox E ℓ ι) (s : Fin ι.nsorts) :
    RawFamily (CtxCat.recr hd ls s) :=
  RawFamily.decode D (Tm.label (CtxCat.recr hd ls s).as (RecTyping.recrBody_typed hd ls s))
    (interp (CtxCat.recr hd ls s) (ι.recrBody s) (recrBody_headRank_lt η s))
    (recursorPayload D interp hd ls V s)

theorem recursorHyp_mono {V₁ V₂ : RecApprox E ℓ ι} (hV : V₁ ≤ V₂) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
    recursorHyp D interp hd ls V₁ s c f ≤ recursorHyp D interp hd ls V₂ s c f :=
  RawFamily.ctxLam_mono (RawFamily.ctxLam_mono (RawFamily.closedApps_mono (hV _) _ _))

theorem recursorBody_mono {V₁ V₂ : RecApprox E ℓ ι} (hV : V₁ ≤ V₂) (s : Fin ι.nsorts) :
    recursorBody D interp hd ls V₁ s ≤ recursorBody D interp hd ls V₂ s :=
  RawFamily.decode_mono_right D _ _
    (RawActionFamily.apply_mono (rawRecCaseFamily_mono _ _ (recursorHyp_mono D interp hd ls hV s)) _ _)

theorem recursorBody_isFinitary (hinterp : ∀ Γ₁ e he, (interp Γ₁ e he).IsFinitary) {V : RecApprox E ℓ ι}
    (hV : ∀ t, (V t).IsFinitary) (s : Fin ι.nsorts) : (recursorBody D interp hd ls V s).IsFinitary :=
  RawFamily.IsFinitary.decode D (hinterp _ _ _)
    (RawActionFamily.IsFinitary.apply
      (rawRecCaseFamily_isFinitary _ (fun _ => RawFamily.lookup_isFinitary _) fun _ _ =>
        RawFamily.IsFinitary.ctxLam hinterp (RawFamily.IsFinitary.ctxLam hinterp
          (RawFamily.IsFinitary.closedApps (hV _) _ fun _ => hinterp _ _ _)))
      (rawRecCaseFamily_isActionFinitary _ _ _)
      (recoverMajor_isFinitary _ _ _ _ _ _ (fun _ => RawFamily.lookup_isFinitary _)
        (RawFamily.lookup_isFinitary _)) _)

noncomputable def recursorStep : RecApprox E ℓ ι →o RecApprox E ℓ ι where
  toFun V s := RawFamily.ctxLam D interp (CtxCat.nil E ℓ) _ hd.block.recrTele (recrTele_headRank_lt η ls s)
    (recursorBody D interp hd ls V s)
  monotone' _ _ hV s := RawFamily.ctxLam_mono (recursorBody_mono D interp hd ls hV s)

noncomputable def recursorWith : RecApprox E ℓ ι :=
  OrderHom.lfp (recursorStep D interp hd ls)

theorem recursorWith_unfold :
    recursorStep D interp hd ls (recursorWith D interp hd ls) = recursorWith D interp hd ls :=
  OrderHom.map_lfp _

theorem recursorWith_isFinitary (hinterp : ∀ Γ₁ e he, (interp Γ₁ e he).IsFinitary) (s : Fin ι.nsorts) :
    (recursorWith D interp hd ls s).IsFinitary :=
  OrderHom.lfp_induction (p := fun V => ∀ t, (V t).IsFinitary) (recursorStep D interp hd ls)
    (fun _ hV _ t => RawFamily.IsFinitary.ctxLam (hb := recrTele_headRank_lt η ls t) hinterp
      (recursorBody_isFinitary D interp hd ls hinterp hV t))
    (fun S hS t => by
      change (⨆ V : S, (V : RecApprox E ℓ ι) t).IsFinitary
      exact RawFamily.IsFinitary.iSup fun V => hS V.1 V.2 t) s

theorem recursorStep_ωScottContinuous :
    OmegaCompletePartialOrder.ωScottContinuous (recursorStep D interp hd ls) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_map_ωSup_of_orderHom fun C => ?_
  change recursorStep D interp hd ls (⨆ n, C n) = ⨆ n, recursorStep D interp hd ls (C n)
  refine le_antisymm (fun s => ?_) (iSup_le fun n => (recursorStep D interp hd ls).monotone (le_iSup C n))
  rw [RecApprox.iSup_apply]
  refine (RawFamily.ctxLam_mono ?_).trans (RawFamily.ctxLam_iSup_le fun _ _ hab =>
    recursorBody_mono D interp hd ls (C.monotone hab) s)
  have hle (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
      recursorHyp D interp hd ls (⨆ n, C n) s c f ≤ ⨆ n, recursorHyp D interp hd ls (C n) s c f := by
    refine (RawFamily.ctxLam_mono ((RawFamily.ctxLam_mono ?_).trans (RawFamily.ctxLam_iSup_le
      fun _ _ hab => RawFamily.closedApps_mono (C.monotone hab _) _ _))).trans
      (RawFamily.ctxLam_iSup_le fun _ _ hab => RawFamily.ctxLam_mono
        (RawFamily.closedApps_mono (C.monotone hab _) _ _))
    rw [RecApprox.iSup_apply]
    exact RawFamily.closedApps_iSup_le _ _ _
  refine le_trans ?_ (RawFamily.decode_apply_iSup_le D _ _
    (fun n => rawRecCaseFamily (RecTyping.generic hd ls s).toRecData _ (recursorHyp D interp hd ls (C n) s))
    _ _)
  exact RawFamily.decode_mono_right D _ _ (RawActionFamily.apply_mono (rawRecCaseFamily_le_iSup _ _ hle
    (fun c f _ _ hab => recursorHyp_mono D interp hd ls (C.monotone hab) s c f)) _ _)

end Step

end Metalean.CoherentShape
