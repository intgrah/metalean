/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Structure
public import Metalean.Semantics.Basis.Shape
public import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {ι : IndSig}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {η : Head ζ (.inductive ι)} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace Tm

noncomputable def proj (h : (E.get η).block.IsStructure s c) (hB : InductiveWF E (E.get η).block)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ ps p : (E.get η).block.paramType ls ps p)
    (f : Fin (ι.ctors s c).nfields) (n : Tm_ Γ)
    (hn : Tm.type n = Ty.ofTyping Γ.as (h.indType hps)) : Tm_ Γ :=
  elim n ⟨_, _, h.indType hps⟩ hn (fun _ he => label Γ.as (h.projTerm_hasType hB f Γ.as.wf hps he))
    fun _ _ _ _ he => label_eq (h.projType_congr hB f hps he) (h.projTerm_congr hB f hps he)

end Tm

namespace IndCode

structure StructWitness (code : IndCode Γ) (c : Fin code.toIndHead.nctors)
    (n : Tm_ Γ) : Type where
  params : Fin code.ι.nparams → Expr ζ ℓ Γ.as.len
  struct : (E.get code.η).block.IsStructure code.s c
  block : InductiveWF E (E.get code.η).block
  typed (p : Fin code.ι.nparams) :
    E[Γ.as.ctx] ⊢ params p : (E.get code.η).block.paramType code.ls params p
  params_eq (p : Fin code.ι.nparams) : Tm.label Γ.as (typed p) = code.params p
  guard : Tm.type n = Ty.ofTyping Γ.as (struct.indType typed)

def StructGuard (code : IndCode Γ) (c : Fin code.toIndHead.nctors)
    (n : Tm_ Γ) : Prop :=
  Nonempty (StructWitness code c n)

noncomputable def StructGuard.witness {code : IndCode Γ} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ} (hg : StructGuard code c n) : StructWitness code c n :=
  Classical.choice hg

def StructWitness.map {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (w : StructWitness code c n) (σ : Γ₂.as ⟶ Γ₁.as) :
    (code.map ((Tm E ℓ).map (RawCtx.toCtx.map σ).op)).StructWitness c
      ((Tm E ℓ).map (RawCtx.toCtx.map σ).op n) := by
  have htyped : ∀ p : Fin code.ι.nparams,
      E[Γ₂.as.ctx] ⊢ (w.params p).subst σ.subst :
        (E.get code.η).block.paramType code.ls (fun q => (w.params q).subst σ.subst) p := by
    intro p
    have hsub := (w.typed p).substitution σ.typed
    rwa [Inductive.paramType_subst] at hsub
  have hidx : (fun index => Expr.subst σ.subst (w.struct.indices index)) = w.struct.indices :=
    funext w.struct.no_indices.elim
  refine {
    params := fun p => (w.params p).subst σ.subst
    struct := w.struct
    block := w.block
    typed := htyped
    params_eq := ?_
    guard := ?_ }
  · intro p
    change Tm.label Γ₂.as (htyped p) =
      (Tm E ℓ).map (RawCtx.toCtx.map σ).op (code.params p)
    rw [← w.params_eq p]
    exact congr(Tm.label _ (t := $((Inductive.paramType_subst (I := (E.get code.η).block)
      (ls := code.ls) (ps := w.params) p σ.subst).symm)) _)
  · rw [Tm.type_map, w.guard]
    refine (Ty.map_ofTyping _ σ).trans congr(Ty.ofTyping _ (t := $(?_)) _)
    rw [Expr.subst, hidx]

theorem StructGuard.pullback {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (hg : StructGuard code c n) (σ : Γ₂ ⟶ Γ₁) :
    StructGuard (code.map ((Tm E ℓ).map σ.op)) c ((Tm E ℓ).map σ.op n) := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  exact Nonempty.map (·.map σ) hg

theorem StructGuard.cast {code code' : IndCode Γ} (e : code = code')
    {c : Fin code.toIndHead.nctors} {c' : Fin code'.toIndHead.nctors} (ec : c.val = c'.val)
    {n n' : Tm_ Γ} (en : n = n') (hg : StructGuard code c n) :
    StructGuard code' c' n' := by
  cases e
  cases en
  have hcc : c = c' := Fin.ext ec
  cases hcc
  exact hg

end IndCode

namespace Tm

noncomputable def projOfCode {code : IndCode Γ} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ} (hg : code.StructGuard c n)
    (f : Fin (code.ι.ctors code.s c).nfields) : Tm_ Γ :=
  proj hg.witness.struct hg.witness.block code.ls hg.witness.params
    hg.witness.typed f n hg.witness.guard

theorem projOfCode_eq_proj {code : IndCode Γ} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ} (hg : code.StructGuard c n)
    (w : code.StructWitness c n) (f : Fin (code.ι.ctors code.s c).nfields) :
    projOfCode hg f = proj w.struct w.block code.ls w.params w.typed f n w.guard := by
  obtain ⟨R⟩ := n
  have hparams (p : Fin code.ι.nparams) : E[Γ.as.ctx] ⊢ hg.witness.params p ≡ w.params p :
      (E.get code.η).block.paramType code.ls hg.witness.params p :=
    (Quotient.exact ((hg.witness.params_eq p).trans (w.params_eq p).symm)).2
  have he := (Quotient.exact hg.witness.guard).conv R.valWF
  exact label_eq (hg.witness.struct.projType_congr hg.witness.block f hparams he)
    (hg.witness.struct.projTerm_congr hg.witness.block f hparams he)

theorem proj_ctor_label (hs : (E.get η).block.IsStructure s c) (hB : InductiveWF E (E.get η).block)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ ps p : (E.get η).block.paramType ls ps p)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ.as.len)
    (hmaj : E[Γ.as.ctx] ⊢ .ctor η s c ls ps fds hs.recursive : .ind η s ls ps hs.indices)
    (hfields : ∀ f, E[Γ.as.ctx] ⊢ fds f : ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
    (f : Fin (ι.ctors s c).nfields) :
    proj hs hB ls ps hps f (label Γ.as hmaj) rfl = label Γ.as (hfields f) := by
  have hiota (current : Fin (ι.ctors s c).nfields) :=
    hs.projTerm_ctor hB current fds Γ.as.wf hps hmaj hfields
  have hprojected : ∀ current : Fin (ι.ctors s c).nfields,
      E[Γ.as.ctx] ⊢ hs.projTerm η ls ps current
          (.ctor η s c ls ps fds hs.recursive) ≡
        fds current :
          (((((E.get η).block.ctors s c).ordinary current).type).instL ls).subst
            (Fin.append ps fun previous : Fin current.val =>
              hs.projTerm η ls ps (previous.castLE current.isLt.le)
                (.ctor η s c ls ps fds hs.recursive)) := by
    intro current
    simpa [Inductive.IsStructure.projType_eq, Ctor.ordinaryFieldExpr] using hiota current
  have htypes := (hB.ctors s c).ordinaryFieldExpr_congr hB.params f
    hps (fun g _ => hprojected g)
  apply label_eq _ (hiota f)
  rw [Inductive.IsStructure.projType_eq]
  exact .ofDefEq htypes

theorem map_projOfCode {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (hg : code.StructGuard c n) (σ : Γ₂.as ⟶ Γ₁.as)
    (f : Fin (code.ι.ctors code.s c).nfields)
    (hg' : (code.map ((Tm E ℓ).map (RawCtx.toCtx.map σ).op)).StructGuard c
      ((Tm E ℓ).map (RawCtx.toCtx.map σ).op n)) :
    (Tm E ℓ).map (RawCtx.toCtx.map σ).op (projOfCode hg f) = projOfCode hg' f := by
  obtain ⟨R⟩ := n
  let w := hg.witness
  have hidx : (fun index => Expr.subst σ.subst (w.struct.indices index)) = w.struct.indices :=
    funext w.struct.no_indices.elim
  have he := (Quotient.exact w.guard).conv R.valWF
  have heσ : E[Γ₂.as.ctx] ⊢ R.val.subst σ.subst :
      .ind code.η code.s code.ls (fun q => (w.params q).subst σ.subst) w.struct.indices := by
    have h := he.substitution σ.typed
    rwa [Expr.subst, hidx] at h
  rw [projOfCode_eq_proj hg' (w.map σ) f, projOfCode_eq_proj hg w f]
  refine (map_label _ σ).trans (label_eq ?_ ?_)
  · rw [Inductive.IsStructure.projType_subst]
    exact w.struct.projType_congr w.block f (w.map σ).typed heσ
  · rw [Inductive.IsStructure.projTerm_subst, Inductive.IsStructure.projType_subst]
    exact w.struct.projTerm_congr w.block f (w.map σ).typed heσ

end Tm

end Metalean
