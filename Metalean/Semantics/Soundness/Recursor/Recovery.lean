/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Recovery
public import Metalean.Strong.ProofFields
public import Metalean.Semantics.Interpretation.Recursor.Recovery
public import Metalean.Semantics.Interpretation.Recursor.Section
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.Semantics.Soundness.Recursor.Fields
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (f : Fin (ι.ctors s c).nrecFields)

theorem CtorSection.eq_of_recovery (herased : (E.get η).block.level.inst ls = .zero)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {σ : Γ₂ ⟶ Γ₁}
    {indexNames : Fin (ι.nindices s) → Tm_ Γ₂}
    (sect : CtorSection h s c σ) (sect' : CtorSection h s c σ)
    (hn : RecoveryNames η s c ls indexNames sect.names)
    (hn' : RecoveryNames η s c ls indexNames sect'.names) : sect = sect' := by
  have ⟨α, hα⟩ := RawCtx.toCtx.map_surjective sect.hom
  have ⟨β, hβ⟩ := RawCtx.toCtx.map_surjective sect'.hom
  have heq : E[Γ₂.as.ctx] ⊢ₛ α.subst ≡ β.subst ⊣ (CtxCat.ctorFields h.toIndData s c).as.ctx := by
    refine .of_proof_or_eq (CtxCat.ctorFields h.toIndData s c).as.wf α.typed β.typed fun v => ?_
    have of_names (v : Var (CtxCat.ctorFields h.toIndData s c).as.len)
        (hv : (Tm E ℓ).map sect.hom.op (Tm.varLabel (CtxCat.ctorFields h.toIndData s c) v) =
          (Tm E ℓ).map sect'.hom.op (Tm.varLabel (CtxCat.ctorFields h.toIndData s c) v)) :
        E[Γ₂.as.ctx] ⊢ₛ α.subst v ≡ β.subst v :
          (Ctx.get v (CtxCat.ctorFields h.toIndData s c).as.ctx).subst α.subst := by
      rw [← hα, ← hβ] at hv
      exact (Quotient.exact
        (((Tm.map_varLabel α v).symm.trans hv).trans
          (Tm.map_varLabel β v))).2
    refine Fin.addCases (fun v => ?_) (fun f => ?_) v
    · refine Fin.addCases (fun v => ?_) (fun f => ?_) v
      · exact Or.inr (of_names (baseVar h.toIndData s c v) ((sect.base v).trans (sect'.base v).symm))
      · by_cases hf : Level.rel ((((E.get η).block.ctors s c).ordinary f).level.inst ls) = true
        · have ⟨i, hi, hni⟩ := hn f hf
          have ⟨j, hj, hnj⟩ := hn' f hf
          obtain rfl : i = j := Option.some.inj (hi.symm.trans hj)
          exact Or.inr (of_names _ (hni.trans hnj.symm))
        · have hz : (((E.get η).block.ctors s c).ordinary f).level.inst ls = .zero := by
            simpa using hf
          have hp := (h.block.ctors s c).ordinaryFieldExprStrong f
            (h.fields s c).param (CtorInstance.generic h.toIndData s c).typed.ordinary
          rw [hz] at hp
          refine Or.inl (DefeqStrong.substitution (t := .prop) α.typed ?_)
          change E[(CtxCat.ctorFields h.toIndData s c).as.ctx] ⊢ₛ
            Ctx.get (fieldVar h.toIndData s c (f.castAdd _))
              (CtxCat.ctorFields h.toIndData s c).as.ctx : .prop
          rw [CtxCat.ctorFields_get_ordinary]
          exact hp
    · rw [← fieldVar_natAdd h.toIndData s c f]
      have hi := h.ihTyping s c f
      have hp := DefeqStrong.indDF hi.param hi.index
      rw [herased] at hp
      have hp := Ctx.pi_propStrong (fieldTelescope h.toIndData s c f)
        (CtxCat.ctorFieldTarget h.toIndData s c f).as.wf hp
      refine Or.inl (DefeqStrong.substitution (t := .prop) α.typed ?_)
      rw [CtxCat.ctorFields_get_recursive]
      exact hp
  exact CtorSection.ext (hα ▸ hβ ▸ (RawCtx.toCtx_map_eq_iff α β).mpr heq)

theorem recoveredField_isDirected (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (indices : Fin (ι.nindices s) → RawValue Γ₂) (hindices : ∀ i, (indices i).IsDirected)
    (f : Fin (CtorHead.mk η s c).arity) :
    (recoveredField η s c ls indices f).IsDirected := by
  cases f using Fin.addCases with
  | left f =>
    simp only [recoveredField, Fin.append_left]
    split
    · split
      · exact hindices _
      · exact ΩLower.isDirected_bot
    · exact ΩLower.isDirected_bot
  | right f =>
    simp only [recoveredField, Fin.append_right]
    exact ΩLower.isDirected_bot

include h in
theorem RecData.recovery_eligible (hresult : l.rel = true)
    (herased : (E.get η).block.level.inst ls = .zero)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 ∧ ((E.get η).block.ctors s c).Eligible (E.get η).block.level := by
  rcases h.allowed with hl | hlarge
  · simp [hl] at hresult
  · exact (hlarge s).singleton_of_eval_zero ls (congrArg (Level.eval fun _ => 0) herased) c

theorem proofConstructor_isDirected (hresult : l.rel = true)
    (herased : (E.get η).block.level.inst ls = .zero)
    (s : Fin ι.nsorts) (σ₁ : Γ₂ ⟶ Γ₁)
    (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawValue Γ₂) (hindices : ∀ i, (indices i).IsDirected) :
    (proofConstructor h s σ₁ indexNames indices).IsDirected := by
  intro Γ₃ σ₂ a b ha hb
  rcases ha with ha | ⟨c, sect, hn, ha⟩
  · exact ⟨b, hb, ha.trans bot_le, le_rfl⟩
  rcases hb with hb | ⟨c', sect', hn', hb⟩
  · exact ⟨a, Or.inr ⟨c, sect, hn, ha⟩, le_rfl, hb.trans bot_le⟩
  have hsingle := (h.recovery_eligible hresult herased s c).1
  have hc : c' = c := Fin.ext (by have := c'.isLt; have := c.isLt; omega)
  subst c'
  obtain rfl := CtorSection.eq_of_recovery h herased sect sect' hn hn'
  have hfields : ∀ i,
      (recoveredField η s c ls (fun j => (indices j).pullback σ₂) i).IsDirected :=
    recoveredField_isDirected s c _ fun j => ΩLower.IsDirected.pullback (hindices j) σ₂
  have ⟨z, hz, haz, hbz⟩ := RawValue.ctor_isDirected ⟨η, s, c⟩ sect.names hfields (𝟙 Γ₃) ha hb
  exact ⟨z, Or.inr ⟨c, sect, hn, hz⟩, haz, hbz⟩

theorem recoverMajor_isDirected
    (hresult : l.rel = true) (s : Fin ι.nsorts)
    (source : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawFamily Γ₂) (major : RawFamily Γ₂)
    (σ : Γ₃ ⟶ Γ₂) (ρ : RawValuation Γ₃)
    (hindices : ∀ i, ((indices i).app _ σ.op ρ).IsDirected)
    (hmajor : (major.app _ σ.op ρ).IsDirected) :
    ((recoverMajor h s source indexNames indices major).app _ σ.op ρ).IsDirected := by
  by_cases hrel : Level.rel ((E.get η).block.level.inst ls) = true
  · simpa only [recoverMajor, hrel, ↓reduceIte] using hmajor
  · have hz : (E.get η).block.level.inst ls = .zero := by simpa using hrel
    simp only [recoverMajor, hrel]
    exact proofConstructor_isDirected h hresult hz s
      (σ ≫ source) (fun i => (Tm E ℓ).map σ.op (indexNames i))
      (fun i => (indices i).app _ σ.op ρ) hindices

end Metalean.CoherentShape
