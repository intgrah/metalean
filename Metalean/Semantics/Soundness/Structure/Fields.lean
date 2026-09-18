/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Structure
public import Metalean.Semantics.Soundness.Constructor.Fields
public import Metalean.Semantics.Soundness.Constructor.Types
public import Metalean.Semantics.Soundness.Telescope.Transport

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {maj : Expr ζ₂ ℓ Γ.as.len}

theorem structure_projection_type_properties
    (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ (ps p))
    (hpsfixed : ∀ p, HasFixedness Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (hmaj : E₂[Γ.as.ctx] ⊢ₛ maj : .ind η s ls ps hs.indices)
    (f : Fin (ι.ctors s c).nfields)
    (pprevious : ∀ g : Fin f.val,
      RawInterpretationProperties Γ (hs.projTerm η ls ps (g.castLE f.isLt.le) maj))
    (hprevious : ∀ g : Fin f.val,
      HasFixedness Γ (hs.projTerm η ls ps (g.castLE f.isLt.le) maj)
        (hs.projType η ls ps (g.castLE f.isLt.le) maj)) :
    RawInterpretationProperties Γ (hs.projType η ls ps f maj) ∧
      HasFixedness Γ (hs.projType η ls ps f maj)
        (.sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)) := by
  have hctx := hB.ordinaryClosedWF s c ls f.val f.isLt.le
  have pctx := hsound.blockOrdinaryPrefixProperties η hI hblock s c ls f.val f.isLt.le
  have pfield := hsound.blockOrdinaryTypeJudgment η hI hblock s c ls f
  have hp := ordinaryField_properties f hctx pctx (pfield hctx) hps pps hpsfixed
    (fun g => by
      rw [← hs.projType_eq]
      exact hs.projTerm_hasTypeStrong hB _ Γ.as.wf hps hmaj)
    pprevious fun g => by
      rw [← hs.projType_eq]
      exact hprevious g
  simpa only [← hs.projType_eq] using hp

theorem structure_field_telescope_properties
    (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hB : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ (ps p))
    (hpsfixed : ∀ p, HasFixedness Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ Γ.as.ctx (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) := by
  have hctx := hB.paramClosedWF ls
  have hd := hB.ordinaryTeleInstL s c ls
  have ppctx := hsound.paramTeleProperties hI hblock ls
  have ppfields := hsound.blockOrdinaryTeleProperties η hI hblock s c ls
  let Src : CtxCat E₂ ℓ := ⟨_, hctx⟩
  let σ : Γ.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEqStrong hps).left⟩
  have hp (v : Var Src.as.len) : HasFixedness Γ (σ.subst v) ((Src.as.ctx.get v).subst σ.subst) := by
    change HasFixedness Γ (ps v) _
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact hpsfixed v
  exact RawTeleProperties.substitution ppctx _ hd ppfields σ pps hp

end Metalean.CoherentShape
