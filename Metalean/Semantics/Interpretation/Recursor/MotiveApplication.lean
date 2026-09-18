/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Inductive
public import Metalean.Semantics.Interpretation.Recursor.Telescope
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ} {ι : IndSig}
  {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} {maj : Expr ζ ℓ Γ₁.as.len}

namespace IndTyping

def indexHom (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is) :
    Γ₁.as ⟶ (CtxCat.extendTele Γ₁ ((E.get η).block.indexTele ls s ps) (hB.indexTele h.param)).as where
  subst := Fin.append Subst.id is
  typed := by
    apply WFTeleStrong.extendFamily (hB.indexTele h.param) (SubstWFStrong.id Γ₁.as.wf)
    intro i
    simpa [Inductive.indexType] using h.index i

def motiveHom (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) :
    Γ₁.as ⟶ (CtxCat.extendTele Γ₁ ((E.get η).block.motiveTele η ls ps s)
      (hB.motiveTele Γ₁.as.wf h.param)).as := by
  have hA := (hB.motiveTele (s := s) Γ₁.as.wf h.param).last.choose_spec.2
  refine (h.indexHom hB).snoc (e := maj) ⟨_, hA⟩ ?_
  change E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls
    (fun p => ((ps p).wkN (ι.nindices s)).subst (Fin.append Subst.id is))
    fun i => (Fin.append Subst.id is) (Fin.natAdd Γ₁.as.len i)
  simpa using hmaj

theorem motiveHom_over (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) :
    h.motiveHom hB hmaj ≫ RawCtx.Hom.teleProjection
      (Γ := Γ₁.as) (hB.motiveTele Γ₁.as.wf h.param) = 𝟙 Γ₁.as := by
  apply RawCtx.Hom.ext
  funext v
  change Subst.extend (Fin.append Subst.id is) maj
    (v.castAdd (ι.nindices s)).castSucc = .var v
  rw [Subst.extend_castSucc, Fin.append_left]
  rfl

@[simp] theorem motiveHom_index (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) (i : Fin (ι.nindices s)) :
    (h.motiveHom hB hmaj).subst (Fin.natAdd Γ₁.as.len i.castSucc) = is i := by
  change Subst.extend (Fin.append Subst.id is) maj
    (Fin.natAdd Γ₁.as.len i).castSucc = is i
  rw [Subst.extend_castSucc]
  exact Fin.append_right _ _ _

@[simp] theorem motiveHom_major (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) :
    (h.motiveHom hB hmaj).subst (Fin.natAdd Γ₁.as.len (Fin.last (ι.nindices s))) = maj := by
  change Subst.extend (Fin.append Subst.id is) maj (Fin.last _) = maj
  exact Subst.extend_last _ _

theorem motiveHom_index_type (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) (i : Fin (ι.nindices s)) :
    (Ctx.get (Fin.natAdd Γ₁.as.len i.castSucc)
      (Γ₁.as.ctx ++ (E.get η).block.motiveTele η ls ps s)).subst (h.motiveHom hB hmaj).subst =
      (E.get η).block.indexType ls s ps is i := by
  change (Ctx.get (Fin.natAdd Γ₁.as.len i).castSucc
    ((Γ₁.as.ctx ++ (E.get η).block.indexTele ls s ps).snoc _)).subst _ = _
  rw [Ctx.get_snoc _ _ (Fin.natAdd Γ₁.as.len i).castSucc
    (Nat.ne_of_lt (Fin.natAdd Γ₁.as.len i).isLt), Expr.wk_subst]
  erw [Inductive.indexTele_get, Inductive.indexType_subst]
  have hσ : Subst.wk.comp (h.motiveHom hB hmaj).subst = Fin.append Subst.id is :=
    funext fun v => Subst.extend_castSucc _ _ v
  rw [hσ]
  change (E.get η).block.indexType ls s
    (fun p => ((ps p).wkN (ι.nindices s)).subst (Fin.append Subst.id is))
    (fun j => (Fin.append Subst.id is) (Fin.natAdd Γ₁.as.len j)) i = _
  simp

theorem motiveHom_major_type (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) :
    (Ctx.get (Fin.natAdd Γ₁.as.len (Fin.last (ι.nindices s)))
      (Γ₁.as.ctx ++ (E.get η).block.motiveTele η ls ps s)).subst (h.motiveHom hB hmaj).subst =
      .ind η s ls ps is := by
  change (Ctx.get (Fin.last (Γ₁.as.len + ι.nindices s))
    ((Γ₁.as.ctx ++ (E.get η).block.indexTele ls s ps).snoc _)).subst _ = _
  rw [Ctx.get_last, Expr.wk_subst]
  have hσ : Subst.wk.comp (h.motiveHom hB hmaj).subst = Fin.append Subst.id is :=
    funext fun v => Subst.extend_castSucc _ _ v
  rw [hσ]
  change Expr.ind η s ls
    (fun p => ((ps p).wkN (ι.nindices s)).subst (Fin.append Subst.id is))
    (fun j => (Fin.append Subst.id is) (Fin.natAdd Γ₁.as.len j)) = _
  simp

theorem motiveHom_index_label (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) (i : Fin (ι.nindices s)) :
    Tm.label Γ₁.as ((h.motiveHom hB hmaj).typed (Fin.natAdd Γ₁.as.len i.castSucc)) =
      Tm.label Γ₁.as (h.index i) := by
  apply Tm.label_eq
  · rw [h.motiveHom_index_type hB hmaj i]
    exact IsTypeStrong.isTypeEq (h.index i).regular
  · rw [h.motiveHom_index_type hB hmaj i, h.motiveHom_index hB hmaj i]
    exact h.index i

theorem motiveHom_major_label (hB : (E.get η).block.WFStrong E) (h : IndTyping Γ₁ η s ls ps is)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is) :
    Tm.label Γ₁.as ((h.motiveHom hB hmaj).typed (Fin.natAdd Γ₁.as.len (Fin.last (ι.nindices s)))) =
      Tm.label Γ₁.as hmaj := by
  apply Tm.label_eq
  · rw [h.motiveHom_major_type hB hmaj]
    exact IsTypeStrong.isTypeEq hmaj.regular
  · rw [h.motiveHom_major_type hB hmaj, h.motiveHom_major hB hmaj]
    exact hmaj

end IndTyping

end Metalean.CoherentShape
