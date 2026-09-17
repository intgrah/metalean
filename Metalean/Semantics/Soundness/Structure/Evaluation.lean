module

public import Metalean.Semantics.Soundness.Constructor.Admissible
public import Metalean.Semantics.Soundness.Constructor.Fields
public import Metalean.Semantics.Soundness.Structure.Projection
public import Metalean.Semantics.Soundness.Structure.Reconstruction
import Metalean.Strong.InstLevel
import Metalean.Semantics.Interpretation.Computation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len} {maj : Expr ζ₂ ℓ Γ₁.as.len}

theorem rawInterpret_structure_projection_of_previous
    (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : (E₂.get η).block.WFStrong E₂)
    (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields) (hprev : StructureProjection.Prev hs ls f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ₁.op ρ =
      RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ) := by
  have hps (p : Fin ι.nparams) := (pps p).syntactic.left
  have pparams (p : Fin ι.nparams) := (pps p).left
  have fparams (p : Fin ι.nparams) :
      HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p) := (pps p).fixed
  have pfields := structure_field_telescope_properties hsound hI hblock hB hps pparams fparams
    (s := s) (c := c)
  have hcurrent (g : Fin f.val) := hprev g hR pps pmaj
  cases hcarrier : Level.rel ((E₂.get η).block.level.inst ls) with
  | false =>
    have hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = false := by
      cases hfrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) with
      | false => rfl
      | true => exact Bool.noConfusion (hcarrier.symm.trans (structure_carrier_relevant hs f hfrel))
    rw [hs.projTerm_eq_recr, rawInterpret_recr_prop _ hrel,
      pmaj.structural_value_bot hs hB hps hcarrier σ₁ ρ hρ]
    simp
    rfl
  | true =>
    have hΔ := (hB.ctors s c).ordinaryFieldTele (η := η) hps
    have hctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) :
        E₂[Ctx.instL ls ((E₂.get η).block.params ++
          ((E₂.get η).block.ctors s c).ordinaryTeleAux k hk)] ⊢ₛ ok :=
      hB.ordinaryClosedWF s c ls k hk
    have hpctx := hB.paramClosedWF ls
    have hd := hB.ordinaryTeleInstL s c ls
    have ppctx := hsound.paramTeleProperties hI hblock ls
    have ppfields := hsound.blockOrdinaryTeleProperties η hI hblock s c ls
    have ppbody := hsound.blockCtorFieldProperties η hI hblock s c ls
    have pfn (d : Fin (ι.nctors s)) : HasIdeality (CtxCat.nil E₂ ℓ)
        (((E₂.get η).block.ctorTypeFn s d).instL fun p => ls p) :=
      (hsound.blockCtorTypeFnProperties η hI hblock s d ls).ideal
    have pf := hsound.blockOrdinaryTypeJudgment η hI hblock s c ls f
    have hf (g : Fin (ι.ctors s c).nfields) : E₂[Γ₁.as.ctx] ⊢ₛ hs.projTerm η ls ps g maj :
        ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps (fun g => hs.projTerm η ls ps g maj) g := by
      rw [← hs.projType_eq]
      exact hs.projTerm_hasTypeStrong hB g Γ₁.as.wf hps pmaj.syntactic.left
    let T : Domain Γ₂ := ctorFieldTypes pfn (fun p => Tm.label Γ₁.as (hps p)) σ₁ ρ
      (fun p => (pparams p).ideal σ₁ ρ hρ) c
    have hfixed := pmaj.structural_field_telescope hs hB hcarrier pfn hps (fun p => (pparams p).ideal)
      σ₁ ρ hρ T rfl
    have hfixed' : ((piLimit E₂ ℓ).telescope T
        (fun g => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hf g)))
        fun g => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ g) (pmaj.eval hρ)).1 =
        fun g => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ g) (pmaj.eval hρ) := by
      have hn (g) : (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hf g)) =
          (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
            (hs.projTerm_hasTypeStrong hB g Γ₁.as.wf hps pmaj.syntactic.left)) :=
        congrArg ((Tm E₂ ℓ).map σ₁.op) (Tm.label_congr (hs.projType_eq η ls ps g maj).symm)
      simp only [hn]
      exact hfixed
    have ⟨hsource, σ₂, hover, hnames, hadm⟩ := ctorFieldTypes_admissible hpctx hd ppctx ppfields
      (ppbody hpctx) hps pparams fparams hf σ₁ ρ hρ
      (fun g => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ g) (pmaj.eval hρ)) T rfl hfixed'
    cases hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) with
    | false =>
      have hzero := ordinaryField_eq_bot_of_admissible hctx hps hf f (pf _) hrel σ₁
        (RawValuation.pushFin (fun _ => ⊥) fun p =>
          (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ₁.op ρ)
        (fun g => RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ g)
          ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ)) hsource
      rw [hs.projTerm_eq_recr, rawInterpret_recr_prop _ hrel]
      exact hzero.symm
    | true =>
      have hn (g : Fin (ι.ctors s c).nfields) :
          (Tm E₂ ℓ).map σ₂.op (Tm.varLabel (CtxCat.extendTele Γ₁
            (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ) (Fin.natAdd Γ₁.as.len g)) =
          (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
            (hs.projTerm_hasTypeStrong hB g Γ₁.as.wf hps pmaj.syntactic.left)) :=
        (hnames g).trans (congrArg ((Tm E₂ ℓ).map σ₁.op)
          (Tm.label_congr (hs.projType_eq η ls ps g maj).symm))
      have hargs := structure_projection_recrArgs hsound hI hblock hs hB hR pps pmaj f hrel hprev
      have pbody :=
        (structure_projection_body_properties hsound hI hblock hs hB hR pps pmaj f hprev).1
      have he := rawInterpret_structure_projection_beta hsound hI hblock hs hB hps pmaj f hrel
        (fun v => (hargs v).1) (fun v => (hargs v).2)
        pbody.ideal pbody.subst hΔ pfields σ₁ ρ hρ σ₂ hover hn hadm
      have hfixed := rawExtend_ordinaryFieldExpr_of_admissible hctx hps hf f (pf _).left.subst
        (fun p => (pparams p).subst) (fun g => (hcurrent g).term.subst) σ₁ ρ hρ
        (fun g => RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ g)
          ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ))
        (fun g => (hcurrent g).value σ₁ ρ hρ) hsource
      rw [Tm.label_congr (hb := hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.syntactic.left)
        (hs.projType_eq η ls ps f maj).symm, ← hs.projType_eq] at hfixed
      exact he.trans hfixed

end Metalean.CoherentShape
