module

public import Metalean.Semantics.Soundness.Structure.Evaluation
public import Metalean.Semantics.Soundness.Structure.Reconstruction
import Metalean.Strong.InstLevel
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {maj : Expr ζ₂ ℓ Γ.as.len}

theorem structure_projection_properties
    (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : (E₂.get η).block.WFStrong E₂)
    (f : Fin (ι.ctors s c).nfields) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawJudgment Γ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ maj maj (.ind η s ls ps hs.indices)) :
    StructureProjection hs ls f Γ ps maj := by
  induction f using Fin.strong_induction_on generalizing Γ with
  | h f ih =>
    have hprev : StructureProjection.Prev hs ls f := by
      intro g _ _ _ hR' pps' pmaj'
      exact ih (g.castLE f.isLt.le) g.isLt hR' pps' pmaj'
    have hps (p : Fin ι.nparams) := (pps p).syntactic.left
    have hbody := structure_projection_body_properties hsound hI hblock hs hB hR pps pmaj f hprev
    have hresult := (hs.projectionStrong hB Γ.as.wf hps pmaj.syntactic.left f).result
    have hp : RawInterpretationProperties Γ (hs.projTerm η ls ps f maj) ∧
        HasFixedness Γ (hs.projTerm η ls ps f maj)
          (Inductive.motiveResult (hs.projectionMotives η ls ps f s) hs.indices maj) := by
      rw [hs.projTerm_eq_recr]
      cases hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) with
      | false =>
        exact ⟨⟨HasIdeality.recr_prop hrel, HasSubstitution.recr_prop hrel⟩,
          HasFixedness.recr_prop hrel⟩
      | true =>
        have hargs := structure_projection_recrArgs hsound hI hblock hs hB hR pps pmaj f hrel hprev
        have hrec := RecTyping.structure_projection hs hB hps pmaj.syntactic.left f
        exact ⟨⟨hsound.recr_ideal hI hblock hrec fun v => (hargs v).1.ideal,
            HasSubstitution.recr hrec fun v => (hargs v).1.subst⟩,
          hsound.recr_fixed hI hblock hrec (fun v => (hargs v).1) fun v => (hargs v).2⟩
    exact ⟨hp.1, HasFixedness.convert hp.2 (.ofDefEq hresult)
        (HasEquality.structure_projection_motive_beta hs hps pmaj f hbody.1.ideal hbody.1.subst),
      fun σ ρ hρ => rawInterpret_structure_projection_of_previous hsound hI hblock hs hB hR pps
        pmaj f hprev σ ρ hρ⟩

theorem RawJudgment.etaStruct (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : (E₂.get η).block.WFStrong E₂)
    (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawJudgment Γ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ maj maj (.ind η s ls ps hs.indices))
    (prebuild : RawJudgment Γ (hs.rebuildTerm η ls ps maj) (hs.rebuildTerm η ls ps maj)
      (.ind η s ls ps hs.indices)) :
    RawJudgment Γ (hs.rebuildTerm η ls ps maj) maj (.ind η s ls ps hs.indices) := by
  have pfn (d : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hI hblock s d ls
  exact RawJudgment.of_typings
    (.etaStruct hs (fun p => (pps p).syntactic.left) pmaj.syntactic.left prebuild.syntactic.left)
    prebuild pmaj (HasEquality.structure_eta_of_projections hs hB pfn pps pmaj fun f =>
      (structure_projection_properties hsound hI hblock hs hB f hR pps pmaj).value)

end Metalean.CoherentShape
