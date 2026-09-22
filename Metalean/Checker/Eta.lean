/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
import Metalean.Typing.Structure

@[expose] public section

namespace Metalean.Checker

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n} {is : Fin (ι.nindices s) → Expr ζ ℓ n}
  {e e₁ e₂ : Expr ζ ℓ n}

variable (ho : E.Ordered) (h : (E.get η).block.IsStructure s c)
include ho h

theorem structure_eta :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ e : .ind η s ls ps is →
    E[Γ] ⊢ e ≡ h.rebuildTerm η ls ps e : .ind η s ls ps is := by
  intro hΓ hps he
  obtain rfl : is = h.indices := funext h.no_indices.elim
  exact (Defeq.etaStruct h hps he
    (h.rebuildTerm_hasType (ho.entryWF η).block h.indices hΓ hps he)).symm

theorem unit_like_eta (hf : IsEmpty (Fin (ι.ctors s c).nfields)) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ e₁ : .ind η s ls ps is →
    E[Γ] ⊢ e₂ : .ind η s ls ps is →
    E[Γ] ⊢ e₁ ≡ e₂ : .ind η s ls ps is := by
  intro hΓ hps he₁ he₂
  obtain rfl : is = h.indices := funext h.no_indices.elim
  have hb := h.rebuildTerm_hasType (ho.entryWF η).block h.indices hΓ hps he₁
  have hr : h.rebuildTerm η ls ps e₁ = h.rebuildTerm η ls ps e₂ := by
    unfold Inductive.IsStructure.rebuildTerm
    congr 1
    exact funext hf.elim
  have hη := Defeq.etaStruct h hps he₁ hb
  rw [hr] at hη
  exact hη.symm.trans (.etaStruct h hps he₂ (hr ▸ hb))

end Metalean.Checker
