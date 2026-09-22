/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Application
public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Typing.InstLevel
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf CoherentShape CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {is : Fin (ι.nindices s) → Expr ζ₂ ℓ Γ₁.as.len} {maj m : Expr ζ₂ ℓ Γ₁.as.len}

namespace CoherentShape

theorem RawTyped.motiveSpine (ht' : InductiveWF E₂ (E₂.get η).block) (h : IndTyping Γ₁ η s ls ps is)
    (hm : E₂[Γ₁.as.ctx] ⊢ m : (E₂.get η).block.motiveType η ls ps l s)
    (pΔ : RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s))
    (pm : RawInterpretationProperties Γ₁ m) (fm : HasFixedness Γ₁ m ((E₂.get η).block.motiveType η ls ps l s))
    (pis : ∀ i, RawInterpretationProperties Γ₁ (is i))
    (fis : ∀ i, HasFixedness Γ₁ (is i) ((E₂.get η).block.indexType ls s ps is i)) :
    RawTyped Γ₁ (m.apps is) (.forallE (.ind η s ls ps is) (.sort l)) ∧
      RawInterpretationProperties Γ₁ (.ind η s ls ps is) := by
  let Δ := (E₂.get η).block.indexTele ls s ps
  have hΔ := ht'.indexTele (s := s) h.param
  let T := CtxCat.extendTele Γ₁ Δ hΔ
  let t : Expr ζ₂ ℓ T.as.len := .ind η s ls (fun p => (ps p).wkN (ι.nindices s))
    fun i => .var (Fin.natAdd Γ₁.as.len i)
  let u := (ht'.motiveTele (s := s) Γ₁.as.wf h.param).last.choose
  have ht : E₂[T.as.ctx] ⊢ t : .sort u :=
    (ht'.motiveTele (s := s) Γ₁.as.wf h.param).last.choose_spec.2
  have pt : RawInterpretationProperties T t := pΔ.last T.as.wf
  let t' := Expr.forallE t (.sort l)
  have hcode : E₂[T.as.ctx] ⊢ t' : .sort (.imax u (.succ l)) :=
    .forallEDF ht .sortDF .sortDF
  have pcode : RawInterpretationProperties T t' :=
    .forallE ht .sortDF pt (RawInterpretationProperties.sort (T.extension ht) l)
  let σ₁ : Γ₁.as ⟶ T.as := ⟨Fin.append Subst.id is, by
    apply TeleWF.extendFamily hΔ (SubstWF.id Γ₁.as.wf)
    simpa using h.index⟩
  have hover : σ₁ ≫ RawCtx.Hom.teleProjection (Γ := Γ₁.as) hΔ = 𝟙 Γ₁.as :=
    RawCtx.Hom.ext (funext fun _ => Fin.append_left _ _ _)
  have pσ₁ (i) : RawInterpretationProperties Γ₁ (σ₁.subst (Fin.natAdd Γ₁.as.len i)) := by
    simpa [σ₁] using pis i
  have fσ₁ (i) : HasFixedness Γ₁ (σ₁.subst (Fin.natAdd Γ₁.as.len i))
      ((Ctx.get (Fin.natAdd Γ₁.as.len i) (Γ₁.as.ctx ++ Δ)).subst σ₁.subst) := by
    simpa [Δ, σ₁, Expr.subst] using fis i
  have hσ₁ := SemanticHom.extendTele rfl hΔ pΔ.init σ₁
    (by rw [hover]; exact .id Γ₁) pσ₁ fσ₁
  have hbound := RawTyped.applyBound hΔ pΔ.init hcode pcode
    ⟨hm, .pi _ hΔ pΔ.init _ hcode pcode, pm, fm⟩
  have papp := hσ₁.typed hbound
  have pc := hσ₁.props pt
  simpa [σ₁, t, t', Expr.applyBound_eq_apps, Expr.subst_apps, Expr.subst] using And.intro papp pc

variable (hB : InductiveWF E₂ (E₂.get η).block) (h : IndTyping Γ₁ η s ls ps is)
  (hmaj : E₂[Γ₁.as.ctx] ⊢ maj : .ind η s ls ps is)
  (hm : E₂[Γ₁.as.ctx] ⊢ m : (E₂.get η).block.motiveType η ls ps l s)
  (pΔ : RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s))
  (pm : RawInterpretationProperties Γ₁ m)
  (fm : HasFixedness Γ₁ m ((E₂.get η).block.motiveType η ls ps l s))
  (pis : ∀ i, RawInterpretationProperties Γ₁ (is i))
  (fis : ∀ i, HasFixedness Γ₁ (is i) ((E₂.get η).block.indexType ls s ps is i))
  (pmaj : RawInterpretationProperties Γ₁ maj)

include hB h hm pΔ pm fm pis fis hmaj pmaj

theorem RawInterpretationProperties.motiveResult :
    RawInterpretationProperties Γ₁ (Inductive.motiveResult m is maj) := by
  have ⟨papp, pc⟩ := RawTyped.motiveSpine hB h hm pΔ pm fm pis fis
  exact (RawInterpretationProperties.app (.indDF h.param h.index) .sortDF pc.ideal
    (HasIdeality.sort _ l) papp pmaj hmaj).1

theorem RawTyped.motiveResult (fmaj : HasFixedness Γ₁ maj (.ind η s ls ps is)) :
    RawTyped Γ₁ (Inductive.motiveResult m is maj) (.sort l) := by
  have ⟨papp, pc⟩ := RawTyped.motiveSpine hB h hm pΔ pm fm pis fis
  exact (papp.app (.indDF h.param h.index) .sortDF (.sort _ l)
    ⟨hmaj, pc, pmaj, fmaj⟩ (.sort _ l)).1

end CoherentShape

theorem RawSound.motiveTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hI : InductiveWF E₂ (E₂.get η).block)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (fps : ∀ p, HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (s : Fin ι.nsorts) :
    RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s) := by
  let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls (E₂.get η).block.params, hI.paramClosedWF ls⟩
  have pctx : RawTeleProperties E₂ .nil Src.as.ctx := by
    simpa using hsound.paramTeleProperties hB hblock ls
  have hindices := (hI.indices s).instLevel (Q := fun _ => True) ls fun _ => trivial
  have pindices : RawTeleProperties E₂ Src.as.ctx (Ctx.instL ls ((E₂.get η).block.indices s)) := by
    simpa [Src, hblock, Inductive.map] using hsound.teleProperties (hB.paramClosedWF ls)
      ((hB.indices s).instLevel (Q := fun _ => True) ls fun _ => trivial)
  let σ : Γ₁.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEq hps).left⟩
  have pf (v : Fin ι.nparams) :
      HasFixedness Γ₁ (σ.subst v) ((Src.as.ctx.get v).subst σ.subst) := by
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact fps v
  have hΔ := hI.indexTele (s := s) hps
  let T := CtxCat.extendTele Γ₁ ((E₂.get η).block.indexTele ls s ps) hΔ
  have ht : IndTyping T η s ls (fun p => (ps p).wkN (ι.nindices s))
      fun i => .var (Fin.natAdd Γ₁.as.len i) :=
    IndTyping.ofTyping hI
      (hI.motiveTele (s := s) Γ₁.as.wf hps).last.choose_spec.2
  have pfn (c : Fin (ι.nctors s)) := hsound.ctorTypeFnProperties η hB hblock s c ls
  refine .snoc ((SemanticHom.ofImages Src.as.wf pctx σ pps pf).tele hindices pindices) ?_
  intro wf
  exact {
    ideal := HasIdeality.ind ht hI (fun c => (pfn c).ideal) fun p =>
      ((pps p).wkN _ hΔ).ideal
    subst := HasSubstitution.ind ht hI fun p =>
      ((pps p).wkN _ hΔ).subst }

end Metalean
