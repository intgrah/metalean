/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Structure
public import Metalean.Semantics.Soundness.Constructor.Types
public import Metalean.Semantics.Soundness.Telescope.Transport

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {maj : Expr ζ₂ ℓ Γ.as.len}

theorem structure_projection_type_properties
    (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hs : (E₂.get η).block.IsStructure s c) (hB : InductiveWF E₂ (E₂.get η).block)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (f : Fin (ι.ctors s c).nfields)
    (pprevious : ∀ g : Fin f.val, RawTyped Γ
      (hs.projTerm η ls ps (g.castLE f.isLt.le) maj) (hs.projType η ls ps (g.castLE f.isLt.le) maj)) :
    RawTyped Γ (hs.projType η ls ps f maj)
      (.sort ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)) := by
  have hctx := hB.ordinaryClosedWF s c ls f.val f.isLt.le
  have pctx := hsound.ordinaryPrefixProperties η hI hblock s c ls f.val f.isLt.le
  have pfield := hsound.ordinaryTypeJudgment η hI hblock s c ls f
  have pσ := Ctor.forall_ordinarySubst (ctor := (E₂.get η).block.ctors s c)
    (motive := fun e _ t => RawTyped Γ e t)
    (ps₂ := ps) (fds₂ := fun g : Fin f.val => hs.projTerm η ls ps (g.castLE f.isLt.le) maj)
    f.isLt.le pps fun g => by
      have pg := pprevious g
      rw [hs.projType_eq] at pg
      exact pg
  let σ : Γ.as ⟶ (⟨_, hctx⟩ : CtxCat E₂ ℓ).as := ⟨_, fun v => (pσ v).typed⟩
  have hp := (SemanticHom.ofImages hctx pctx σ
    (fun v => (pσ v).term) (fun v => (pσ v).fixed)).typed (pfield hctx).toRawTyped
  simpa [σ, hs.projType_eq, Ctor.ordinaryFieldExpr] using hp

theorem structure_field_telescope_properties (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hB : InductiveWF E₂ (E₂.get η).block)
    (hps : ∀ p, E₂[Γ.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ (ps p))
    (hpsfixed : ∀ p, HasFixedness Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ Γ.as.ctx (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) := by
  have hctx := hB.paramClosedWF ls
  have hd := ((hB.ctors s c).ordinaryTeleAux _ le_rfl).instLevel (Q := fun _ => True) ls fun _ => trivial
  have ppctx := hsound.paramTeleProperties hI hblock ls
  have ppfields := hsound.ordinaryTeleProperties η hI hblock s c ls
  let Src : CtxCat E₂ ℓ := ⟨_, hctx⟩
  let σ : Γ.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEq hps).left⟩
  have hp (v : Var Src.as.len) : HasFixedness Γ (σ.subst v) ((Src.as.ctx.get v).subst σ.subst) := by
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact hpsfixed v
  exact (SemanticHom.ofImages hctx ppctx σ pps hp).tele hd ppfields

end Metalean.CoherentShape
