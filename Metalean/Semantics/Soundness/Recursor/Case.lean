/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Recursor.Fields
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

open CoherentShape TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ.as.len}

theorem RawSound.caseTypeProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (h : IndData Γ η ls ps)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (wf : E₂[Γ.as.ctx ++ (E₂.get η).block.caseTele η ls ps ms s c] ⊢ₛ ok) :
    RawInterpretationProperties
      (⟨Γ.as.ctx ++ (E₂.get η).block.caseTele η ls ps ms s c, wf⟩ : CtxCat E₂ ℓ)
      ((E₂.get η).block.caseType η ls ps ms s c) := by
  let T := CtxCat.ctorFields h s c
  let inst := CtorInstance.generic h s c
  have hfparam (p : Fin ι.nparams) : E₂[T.as.ctx] ⊢ₛ (ι.ctors s c).fieldParams ps p :
      (E₂.get η).block.paramType ls ((ι.ctors s c).fieldParams ps) p :=
    Ctor.WFStrong.fieldParams _ p h.param
  have hfmotive (t : Fin ι.nsorts) : E₂[T.as.ctx] ⊢ₛ
      ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields :
      (E₂.get η).block.motiveType η ls ((ι.ctors s c).fieldParams ps) l t :=
    Ctor.WFStrong.fieldMotive _ t fun t => (pms t).typed
  have pp (p) := (pps p).ctorFields_properties h s c
  have pΔ := hsound.motiveTeleProperties hB hblock h.block hfparam
    (fun p => (pp p).1)
    (fun p => by
      unfold CtorSig.fieldParams
      rw [← Inductive.paramType_wkN, ← Inductive.paramType_wkN]
      exact (pp p).2.2) s
  have ⟨pm, _, fm⟩ := (pms s).ctorFields_properties h s c
  simp only [Inductive.motiveType_wkN] at fm
  have pi := hsound.targetIndexProperties hB hblock s c h pps
  have hindex (i : Fin (ι.nindices s)) :=
    (h.block.ctors s c).targetIndex i (Ctor.targetSubstWFStrong hfparam inst.typed.ordinary)
  have hmajor := DefeqStrong.ctorDF hfparam inst.typed.ordinary inst.typed.recursive
    ((h.block.ctors s c).ordinaryFieldExprStrong · hfparam inst.typed.ordinary)
    (fun f => ((h.block.ctors s c).recursiveFieldExprStrong rfl f T.as.wf hfparam
      inst.typed.ordinary).choose_spec)
    (.indDF hfparam hindex)
  have pc := RawInterpretationProperties.ctor inst.typed
    (fun f => by
      change RawInterpretationProperties T ((ι.ctors s c).fieldOrdinary f)
      unfold CtorSig.fieldOrdinary
      rw [Expr.var_wkN]
      exact RawInterpretationProperties.var T _)
    fun f => RawInterpretationProperties.var T _
  have pr := RawInterpretationProperties.motiveResult h.block ⟨hfparam, hindex⟩ hmajor (hfmotive s)
    pΔ pm fm (fun i => (pi i).1) (fun i => (pi i).2) pc
  let Δ := ((E₂.get η).block.ctors s c).ihTele ls ps ms
  have hΔ := (h.block.ctors s c).ihTele h.block Γ.as.wf h.param fun t => (pms t).typed
  have pq := pr.wkN Δ hΔ
  have he : (Inductive.motiveResult
      (((ms s).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      (fun i => ((E₂.get η).block.ctors s c).targetIndex ls
        ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary i)
      (.ctor η s c ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary (ι.ctors s c).fieldRecursive)).wkN (ι.ctors s c).nrecFields =
        (E₂.get η).block.caseType η ls ps ms s c := by
    rw [Expr.wkN_eq_subst, Inductive.motiveResult_subst]
    simp only [Ctor.targetIndex_subst, Expr.subst, ← Expr.wkN_eq_subst]
    rfl
  erw [he] at pq
  have q (wf : E₂[Γ.as.ctx ++ ((E₂.get η).block.ctors s c).fieldTele η ls ps ++ Δ] ⊢ₛ ok) :
      RawInterpretationProperties
        (⟨Γ.as.ctx ++ ((E₂.get η).block.ctors s c).fieldTele η ls ps ++ Δ, wf⟩ : CtxCat E₂ ℓ)
        ((E₂.get η).block.caseType η ls ps ms s c) := pq
  rw [Tele.append_assoc] at q
  exact q wf

structure CaseTeleSplit (Γ : CtxCat E₂ ℓ) {a b d : Nat}
    (O : Ctx ζ₂ ℓ Γ.as.len (Γ.as.len + a)) (R : Ctx ζ₂ ℓ (Γ.as.len + a) (Γ.as.len + a + b))
    (H : Ctx ζ₂ ℓ (Γ.as.len + a + b) (Γ.as.len + a + b + d))
    (t : Expr ζ₂ ℓ (Γ.as.len + a + b + d)) (l : Level ℓ) : Prop where
  ordinaryWF : WFTeleStrong E₂ (fun _ => True) Γ.as.ctx O
  recursiveWF : WFTeleStrong E₂ (fun _ => True) (Γ.as.ctx ++ O) R
  ihWF : WFTeleStrong E₂ (fun _ => True) (Γ.as.ctx ++ O ++ R) H
  ordinary : RawTeleProperties E₂ Γ.as.ctx O
  recursive : RawTeleProperties E₂ (Γ.as.ctx ++ O) R
  ih : RawTeleProperties E₂ (Γ.as.ctx ++ O ++ R) H
  sort : E₂[Γ.as.ctx ++ O ++ R ++ H] ⊢ₛ t : .sort l
  type (wf : E₂[Γ.as.ctx ++ O ++ R ++ H] ⊢ₛ ok) :
    RawInterpretationProperties (⟨Γ.as.ctx ++ O ++ R ++ H, wf⟩ : CtxCat E₂ ℓ) t

namespace CaseTeleSplit

variable {a b d : Nat} {O : Ctx ζ₂ ℓ Γ.as.len (Γ.as.len + a)}
  {R : Ctx ζ₂ ℓ (Γ.as.len + a) (Γ.as.len + a + b)}
  {H : Ctx ζ₂ ℓ (Γ.as.len + a + b) (Γ.as.len + a + b + d)}
  {t : Expr ζ₂ ℓ (Γ.as.len + a + b + d)} (q : CaseTeleSplit Γ O R H t l)

include q

theorem ihPi_sort : ∃ u, E₂[Γ.as.ctx ++ O ++ R] ⊢ₛ Ctx.pi t H : .sort u :=
  Ctx.pi_isTypeStrong (q.ihWF.appendCtxWFStrong
    (q.recursiveWF.appendCtxWFStrong (q.ordinaryWF.appendCtxWFStrong Γ.as.wf))) q.sort

theorem ihPi :
    RawInterpretationProperties
      (CtxCat.extendTele (CtxCat.extendTele Γ O q.ordinaryWF) R q.recursiveWF) (Ctx.pi t H) :=
  .pi (Src := CtxCat.extendTele (CtxCat.extendTele Γ O q.ordinaryWF) R q.recursiveWF)
    H q.ihWF q.ih t q.sort (q.type _)

theorem recursivePi_sort : ∃ u, E₂[Γ.as.ctx ++ O] ⊢ₛ Ctx.pi (Ctx.pi t H) R : .sort u :=
  Ctx.pi_isTypeStrong (q.recursiveWF.appendCtxWFStrong (q.ordinaryWF.appendCtxWFStrong Γ.as.wf))
    q.ihPi_sort.choose_spec

theorem recursivePi :
    RawInterpretationProperties (CtxCat.extendTele Γ O q.ordinaryWF) (Ctx.pi (Ctx.pi t H) R) :=
  .pi (Src := CtxCat.extendTele Γ O q.ordinaryWF)
    R q.recursiveWF q.recursive _ q.ihPi_sort.choose_spec q.ihPi

theorem ordinaryPi : RawInterpretationProperties Γ (Ctx.pi (Ctx.pi (Ctx.pi t H) R) O) :=
  .pi O q.ordinaryWF q.ordinary _ q.recursivePi_sort.choose_spec q.recursivePi

end CaseTeleSplit

theorem RawSound.caseTeleSplit (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (h : IndData Γ η ls ps)
    (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    CaseTeleSplit Γ (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps)
      (((E₂.get η).block.ctors s c).recursiveFieldTele η ls
        (fun p => (ps p).wkN (ι.ctors s c).nfields)
        (Expr.boundVars Γ.as.len (ι.ctors s c).nfields 0))
      (((E₂.get η).block.ctors s c).ihTele ls ps ms)
      ((E₂.get η).block.caseType η ls ps ms s c) l := by
  have ⟨hO, hR'⟩ := ((h.block.ctors s c).fieldTele rfl Γ.as.wf h.param).of_append
  have ⟨pfield, pH⟩ := (hsound.caseTeleProperties hB hblock s c h hR pps pms).of_append
  have ⟨pO, pR⟩ := pfield.of_append
  have hcase := h.block.caseTele (s := s) (c := c) Γ.as.wf h.param fun t => (pms t).typed
  refine ⟨hO, hR', ?_, pO, pR, ?_, ?_, fun wf => ?_⟩
  · rw [Tele.append_assoc]
    exact (h.block.ctors s c).ihTele h.block Γ.as.wf h.param fun t => (pms t).typed
  · rwa [Tele.append_assoc]
  · have hh := h.block.caseType_hasTypeStrong (hcase.appendCtxWFStrong Γ.as.wf)
      (Inductive.caseParams_typed (ms := ms) (c := c) · h.param)
      (Inductive.caseMotives_typed (c := c) · fun t => (pms t).typed)
      (h.block.caseOrdinary_typed (ms := ms) · h.param)
      (h.block.caseRecursive_typed (ms := ms) · Γ.as.wf h.param)
    simp only [Inductive.caseTele, Ctor.fieldTele, ← Tele.append_assoc] at hh
    exact hh
  · have q := hsound.caseTypeProperties hB hblock h pps pms s c
    rw [Inductive.caseTele, Ctor.fieldTele, ← Tele.append_assoc, ← Tele.append_assoc] at q
    exact q wf

theorem RawSound.caseFnTypeProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (h : IndData Γ η ls ps)
    (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    RawInterpretationProperties Γ ((E₂.get η).block.caseFnType η ls ps ms s c) := by
  simpa [Inductive.caseFnType, Inductive.caseTele, Ctor.fieldTele, Ctx.pi,
    Tele.foldr_append] using (hsound.caseTeleSplit hB hblock h hR pps pms s c).ordinaryPi

end Metalean
