module

public import Metalean.Syntax.Inductive.Recovery
public import Metalean.Strong.ProofFields
public import Metalean.Semantics.Interpretation.Recursor.Recovery
public import Metalean.Semantics.Interpretation.Recursor.Section
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.Semantics.Soundness.Recursor.Fields
import Metalean.Strong
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (f : Fin (ι.ctors s c).nrecFields)

theorem ordinary_recovery_field_prop (f : Fin (ι.ctors s c).nfields)
    (hf : Level.rel ((((E.get η).block.ctors s c).ordinary f).level.inst ls) = false) :
    E[(CtxCat.ctorFields h.toIndData s c).as.ctx] ⊢ₛ
      Ctx.get (fieldVar h.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f))
        (CtxCat.ctorFields h.toIndData s c).as.ctx : .prop := by
  rw [CtxCat.ctorFields_get_ordinary]
  have hz : (((E.get η).block.ctors s c).ordinary f).level.inst ls = .zero := by
    simpa using hf
  have hfield := (h.block.ctors s c).ordinaryFieldExprStrong f
    (h.fields s c).param (CtorInstance.generic h.toIndData s c).typed.ordinary
  rwa [hz] at hfield

theorem recursive_recovery_field_prop (herased : (E.get η).block.level.inst ls = .zero)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
    E[(CtxCat.ctorFields h.toIndData s c).as.ctx] ⊢ₛ
      Ctx.get (fieldVar h.toIndData s c (Fin.natAdd (ι.ctors s c).nfields f))
        (CtxCat.ctorFields h.toIndData s c).as.ctx : .prop := by
  rw [CtxCat.ctorFields_get_recursive, Ctor.recursiveFieldExpr_eq]
  have hparams (p : Fin ι.nparams) :
      E[(CtxCat.ctorFieldTarget h.toIndData s c f).as.ctx] ⊢ₛ
        ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f) :
        (E.get η).block.paramType ls
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f)) p := by
    have hp := ((h.fields s c).param p).wkN (Δ := fieldTelescope h.toIndData s c f)
    exact Inductive.paramType_wkN (I := (E.get η).block) (ls := ls)
      (ps := (ι.ctors s c).fieldParams ps) p ((ι.ctors s c).recursiveArity f) ▸ hp
  have hind : E[(CtxCat.ctorFieldTarget h.toIndData s c f).as.ctx] ⊢ₛ
      .ind η ((ι.ctors s c).recursiveTarget f) ls
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h.toIndData s c f) : .sort ((E.get η).block.level.inst ls) :=
    .indDF hparams (indexTyping h.toIndData s c f)
  rw [herased] at hind
  exact Ctx.pi_propStrong (fieldTelescope h.toIndData s c f)
    (CtxCat.ctorFieldTarget h.toIndData s c f).as.wf hind

theorem CtorSection.names_eq_recovery (herased : (E.get η).block.level.inst ls = .zero)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {σ : Γ₂ ⟶ Γ₁}
    {indexNames : Fin (ι.nindices s) → Tm_ Γ₂}
    (sect : CtorSection h s c σ) (sect' : CtorSection h s c σ)
    (hn : RecoveryNames η s c ls indexNames sect.names)
    (hn' : RecoveryNames η s c ls indexNames sect'.names) : sect.names = sect'.names := by
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
      exact (Tm.label_eq_iff.mp
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
        · have hf : Level.rel ((((E.get η).block.ctors s c).ordinary f).level.inst ls) = false :=
            Bool.eq_false_iff.mpr hf
          exact Or.inl ((ordinary_recovery_field_prop h s c f hf).substitution α.typed)
    · have hv : fieldVar h.toIndData s c (Fin.natAdd (ι.ctors s c).nfields f) =
          Fin.natAdd (Γ₁.as.len + (ι.ctors s c).nfields) f :=
        Fin.ext (Nat.add_assoc _ _ _).symm
      rw [← hv]
      exact Or.inl ((recursive_recovery_field_prop h herased s c f).substitution α.typed)
  exact sect.names_eq sect' (hα ▸ hβ ▸ (RawCtx.toCtx_map_eq_iff α β).mpr heq)

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
  obtain rfl := CtorSection.eq_of_names_eq (CtorSection.names_eq_recovery h herased sect sect' hn hn')
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
  · simpa only [recoverMajor, hrel, Bool.false_eq_true, ↓reduceIte] using hmajor
  · have hz : (E.get η).block.level.inst ls = .zero := by simpa using hrel
    simp only [recoverMajor, hrel, Bool.false_eq_true, ↓reduceIte]
    exact proofConstructor_isDirected h hresult hz s
      (σ ≫ source) (fun i => (Tm E ℓ).map σ.op (indexNames i))
      (fun i => (indices i).app _ σ.op ρ) hindices

end Metalean.CoherentShape
