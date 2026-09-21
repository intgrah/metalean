/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Structure
public import Metalean.Semantics.Basis.Shape
public import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {ι : IndSig}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {η : Head ζ (.inductive ι)} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace Tm

noncomputable def proj (h : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (f : Fin (ι.ctors s c).nfields) (n : Tm_ Γ)
    (hn : Tm.type n = Ty.ofTyping Γ.as (h.indTypeStrong hps)) : Tm_ Γ :=
  elim n ⟨_, _, h.indTypeStrong hps⟩ hn
    (fun _ he => label Γ.as (h.projTerm_hasTypeStrong hB f Γ.as.wf hps he))
    fun _ _ _ _ he => label_eq (h.projType_congrStrong hB f hps he)
      (h.projTerm_congrStrong hB f hps he)

theorem proj_eq (h : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (f : Fin (ι.ctors s c).nfields) (n : Tm_ Γ)
    (hn : Tm.type n = Ty.ofTyping Γ.as (h.indTypeStrong hps)) {maj : Expr ζ ℓ Γ.as.len}
    (hmaj : E[Γ.as.ctx] ⊢ₛ maj : .ind η s ls ps h.indices) (hnmaj : n = label Γ.as hmaj) :
    proj h hB ls ps hps f n hn = label Γ.as (h.projTerm_hasTypeStrong hB f Γ.as.wf hps hmaj) :=
  elim_eq _ _ _ _ _ hmaj hnmaj

theorem proj_label (h : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    {maj : Expr ζ ℓ Γ.as.len}
    (hmaj : E[Γ.as.ctx] ⊢ₛ maj : .ind η s ls ps h.indices)
    (f : Fin (ι.ctors s c).nfields) :
    proj h hB ls ps hps f (label Γ.as hmaj) rfl =
      label Γ.as (h.projTerm_hasTypeStrong hB f Γ.as.wf hps hmaj) :=
  proj_eq h hB ls ps hps f _ rfl hmaj rfl

end Tm

namespace IndCode

structure StructWitness (code : IndCode Γ) (c : Fin code.toIndHead.nctors)
    (n : Tm_ Γ) : Type where
  params : Fin code.ι.nparams → Expr ζ ℓ Γ.as.len
  struct : (E.get code.η).block.IsStructure code.s c
  block : (E.get code.η).block.WFStrong E
  typed (p : Fin code.ι.nparams) :
    E[Γ.as.ctx] ⊢ₛ params p : (E.get code.η).block.paramType code.ls params p
  params_eq (p : Fin code.ι.nparams) : Tm.label Γ.as (typed p) = code.params p
  guard : Tm.type n = Ty.ofTyping Γ.as (struct.indTypeStrong typed)

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
      E[Γ₂.as.ctx] ⊢ₛ (w.params p).subst σ.subst :
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
    exact Tm.label_congr (Inductive.paramType_subst (I := (E.get code.η).block)
      (ls := code.ls) (ps := w.params) p σ.subst).symm
  · rw [Tm.type_map, w.guard]
    refine (Ty.map_ofTyping _ σ).trans (Ty.ofTyping_congr ?_)
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
  have hparams (p : Fin code.ι.nparams) : E[Γ.as.ctx] ⊢ₛ hg.witness.params p ≡ w.params p :
      (E.get code.η).block.paramType code.ls hg.witness.params p :=
    (label_eq_iff.mp ((hg.witness.params_eq p).trans (w.params_eq p).symm)).2
  have ⟨e, he, hn⟩ := exists_label n _ hg.witness.guard
  have hty := (Ty.ofRepr_eq_iff _ _).mp (hg.witness.guard.symm.trans w.guard)
  have he' := hty.convStrong he
  exact (proj_eq hg.witness.struct hg.witness.block code.ls hg.witness.params hg.witness.typed f n
    hg.witness.guard he hn).trans
    ((label_eq (hg.witness.struct.projType_congrStrong hg.witness.block f hparams he)
      (hg.witness.struct.projTerm_congrStrong hg.witness.block f hparams he)).trans
        (proj_eq w.struct w.block code.ls w.params w.typed f n w.guard he'
          (hn.trans (label_eq hty he))).symm)

theorem projOfCode_ctor_label {code : IndCode Γ} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ} (hg : code.StructGuard c n) (w : code.StructWitness c n)
    (fds : Fin (code.ι.ctors code.s c).nfields → Expr ζ ℓ Γ.as.len)
    (hmaj : E[Γ.as.ctx] ⊢ₛ .ctor code.η code.s c code.ls w.params fds w.struct.recursive :
      .ind code.η code.s code.ls w.params w.struct.indices)
    (hn : n = label Γ.as hmaj)
    (hfields : ∀ f, E[Γ.as.ctx] ⊢ₛ fds f :
      ((E.get code.η).block.ctors code.s c).ordinaryFieldExpr code.ls w.params fds f)
    (f : Fin (code.ι.ctors code.s c).nfields) :
    projOfCode hg f = label Γ.as (hfields f) := by
  trans proj w.struct w.block code.ls w.params w.typed f (label Γ.as hmaj) rfl
  · rw [projOfCode_eq_proj hg w f]
    congr
  have hiota (current : Fin (code.ι.ctors code.s c).nfields) :=
    w.struct.projTerm_ctorStrong w.block current fds Γ.as.wf w.typed hmaj hfields
  have hprojected : ∀ current : Fin (code.ι.ctors code.s c).nfields,
      E[Γ.as.ctx] ⊢ₛ w.struct.projTerm code.η code.ls w.params current
          (.ctor code.η code.s c code.ls w.params fds w.struct.recursive) ≡
        fds current :
          ((((E.get code.η).block.ctors code.s c).ordinaryType current).instL code.ls).subst
            (Fin.append w.params fun previous : Fin current.val =>
              w.struct.projTerm code.η code.ls w.params (previous.castLE current.isLt.le)
                (.ctor code.η code.s c code.ls w.params fds w.struct.recursive)) := by
    intro current
    simpa [Inductive.IsStructure.projType_eq, Ctor.ordinaryFieldExpr] using hiota current
  have ⟨_, htypes⟩ := (w.block.ctors code.s c).ordinaryFieldExpr_congr w.block.params f
    w.typed hprojected
  apply label_eq _ (hiota f)
  rw [Inductive.IsStructure.projType_eq]
  exact .ofDefEq htypes

theorem map_projOfCode {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (hg : code.StructGuard c n) (σ : Γ₂.as ⟶ Γ₁.as)
    (f : Fin (code.ι.ctors code.s c).nfields)
    (hg' : (code.map ((Tm E ℓ).map (RawCtx.toCtx.map σ).op)).StructGuard c
      ((Tm E ℓ).map (RawCtx.toCtx.map σ).op n)) :
    (Tm E ℓ).map (RawCtx.toCtx.map σ).op (projOfCode hg f) = projOfCode hg' f := by
  let w := hg.witness
  have hidx : (fun index => Expr.subst σ.subst (w.struct.indices index)) = w.struct.indices :=
    funext w.struct.no_indices.elim
  have ⟨e, he, hn⟩ := exists_label n _ w.guard
  have heσ : E[Γ₂.as.ctx] ⊢ₛ e.subst σ.subst :
      .ind code.η code.s code.ls (fun q => (w.params q).subst σ.subst) w.struct.indices := by
    have h := he.substitution σ.typed
    rwa [Expr.subst, hidx] at h
  have hnσ : (Tm E ℓ).map (RawCtx.toCtx.map σ).op n = label Γ₂.as heσ :=
    (congrArg ((Tm E ℓ).map (RawCtx.toCtx.map σ).op) hn).trans
      ((map_label he σ).trans (label_congr (by rw [Expr.subst, hidx])))
  rw [projOfCode_eq_proj hg' (w.map σ) f, proj_eq (w.map σ).struct (w.map σ).block _
    (w.map σ).params (w.map σ).typed f _ (w.map σ).guard heσ hnσ,
    projOfCode_eq_proj hg w f, proj_eq _ _ _ _ _ f n w.guard he hn]
  refine (map_label _ σ).trans (label_eq ?_ ?_)
  · rw [Inductive.IsStructure.projType_subst]
    exact w.struct.projType_congrStrong w.block f (w.map σ).typed heσ
  · rw [Inductive.IsStructure.projTerm_subst, Inductive.IsStructure.projType_subst]
    exact w.struct.projTerm_congrStrong w.block f (w.map σ).typed heσ

end Tm

end Metalean
