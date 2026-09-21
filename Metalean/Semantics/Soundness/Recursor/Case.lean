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

open CoherentShape

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
  have pp (p) := (pps p).ctorFields h s c
  have pm := (pms s).ctorFields h s c
  simp only [Inductive.paramType_wkN] at pp
  simp only [Inductive.motiveType_wkN] at pm
  have pΔ := hsound.motiveTeleProperties hB hblock h.block (fun p => (pp p).typed)
    (fun p => (pp p).term) (fun p => (pp p).fixed) s
  have pi i := (hsound.fieldTeleProperties hB hblock s c h pps).2.typed
    (hsound.sourceIndexProperties hB hblock s c h i)
  simp only [Inductive.indexType_subst, Expr.subst, CtxCat.ctorFieldsHom, Fin.append_left] at pi
  simp only [← Ctor.targetIndex.eq_def] at pi
  have hindex i := (pi i).typed
  have hmajor := DefeqStrong.ctorDF (fun p => (pp p).typed) inst.typed.ordinary inst.typed.recursive
    ((h.block.ctors s c).ordinaryFieldExprStrong · (fun p => (pp p).typed) inst.typed.ordinary)
    (fun f => ((h.block.ctors s c).recursiveFieldExprStrong rfl f T.as.wf (fun p => (pp p).typed)
      inst.typed.ordinary).choose_spec)
    (.indDF (fun p => (pp p).typed) hindex)
  have pc := RawInterpretationProperties.ctor inst.typed
    (fun f => by simpa [inst, CtorInstance.generic, CtorSig.fieldOrdinary] using
      RawInterpretationProperties.var T ((f.natAdd Γ.as.len).castAdd (ι.ctors s c).nrecFields))
    fun f => RawInterpretationProperties.var T _
  have pr := RawInterpretationProperties.motiveResult h.block ⟨(fun p => (pp p).typed), hindex⟩ hmajor pm.typed
    pΔ pm.term pm.fixed (fun i => (pi i).term) (fun i => (pi i).fixed) pc
  let Δ := ((E₂.get η).block.ctors s c).ihTele ls ps ms
  have hΔ := (h.block.ctors s c).ihTele h.block Γ.as.wf h.param fun t => (pms t).typed
  convert pr.wkN Δ hΔ using 1 <;>
    simp only [Δ, CtxCat.ctorFields, CtxCat.extendTele, Inductive.caseTele, Tele.append_assoc]
  symm
  rw [Expr.wkN_eq_subst, Inductive.motiveResult_subst]
  simp only [Ctor.targetIndex_subst, Expr.subst, ← Expr.wkN_eq_subst]
  rfl

end Metalean
