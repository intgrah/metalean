/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Substitution

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Opposite Limits TypeTheory TypeTheory.NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace Ty

@[implicit_reducible] def pairPresheaf (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ Type :=
  (ℒ (E := E) (ℓ := ℓ)).polynomial.obj (Ty E ℓ)

abbrev Pair (Γ : CtxCat E ℓ) := (pairPresheaf E ℓ).obj (op Γ)

namespace Repr

theorem forallE_wf (T : Repr Γ) (B : Repr ⟨Γ.as.snoc T.wf⟩) :
    E[Γ.as.ctx] ⊢ .forallE T.term B.term typ :=
  have ⟨_, ht⟩ := T.wf
  have ⟨_, hB⟩ := B.wf
  ⟨_, .forallEDF ht hB hB⟩

def forallE (T : Repr Γ) (B : Repr ⟨Γ.as.snoc T.wf⟩) : Repr Γ :=
  ⟨.forallE T.term B.term, forallE_wf T B⟩

def pi (T : Repr Γ) : Ty_ (⟨Γ.as.snoc T.wf⟩ : CtxCat E ℓ) → Ty_ Γ :=
  Quotient.lift (fun B => ⟦T.forallE B⟧) fun _ _ h =>
    have ⟨_, ht⟩ := T.wf
    Quotient.sound (IsTypeEq.forallE_cod ht h)

theorem pi_conversion (T₁ T₂ : Repr Γ) (h : E[Γ.as.ctx] ⊢ T₁.term ≡ T₂.term typ)
    (b : Ty_(⟨Γ.as.snoc T₁.wf⟩ : CtxCat E ℓ)) :
    T₂.pi ((Ty E ℓ).map (RawCtx.toCtx.map (RawCtx.Hom.convert Γ.as h)).op b) =
      T₁.pi b := by
  induction b using Quotient.inductionOn with
  | h B =>
    have ⟨_, hB⟩ := B.wf
    refine Quotient.sound (IsTypeEq.symm ?_)
    change E[Γ.as.ctx] ⊢ .forallE T₁.term B.term ≡ .forallE T₂.term (B.term.subst Subst.id) typ
    rw [Expr.subst_id]
    exact IsTypeEq.forallE_dom h hB

end Repr

def piApp (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ) : Ty_ Γ :=
  elim (yonedaEquiv A) (fun T hT => T.pi (T.comprehension.eval A B (comprehension_type_eq hT)))
    fun T₁ T₂ h₁ h₂ => by
      have h := Quotient.exact (h₁.symm.trans h₂)
      rw [Repr.eval_conversion T₁ T₂ h A B _ _, Repr.pi_conversion]

theorem piApp_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (T : Repr Γ) (hT : yonedaEquiv A = ⟦T⟧) :
    piApp A B = T.pi (T.comprehension.eval A B (comprehension_type_eq hT)) :=
  elim_eq _ _ _ T hT

theorem reindex_yonedaEquiv {A : y Γ₁ ⟶ Ty E ℓ} {T : Repr Γ₁}
    (hT : yonedaEquiv A = ⟦T⟧) (σ : Γ₂.as ⟶ Γ₁.as) :
    yonedaEquiv (y (RawCtx.toCtx.map σ) ≫ A) = ⟦T.reindex σ⟧ := by
  rw [← yonedaEquiv_naturality, hT]
  rfl

def pi (E : Env ζ) (ℓ : Nat) : pairPresheaf E ℓ ⟶ Ty E ℓ where
  app Γ₁ := ↾fun ⟨A, B⟩ => piApp A B
  naturality := by
    intro ⟨Γ₁⟩ ⟨Γ₂⟩ ⟨σ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    ext ⟨A, B⟩
    obtain ⟨T, hT⟩ := Quotient.exists_rep (yonedaEquiv A)
    have hT := hT.symm
    change piApp (y (RawCtx.toCtx.map σ) ≫ A)
        (ℒ.fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B) =
      (Ty E ℓ).map (RawCtx.toCtx.map σ).op (piApp A B)
    rw [piApp_eq _ _ (T.reindex σ) (reindex_yonedaEquiv hT σ), piApp_eq A B T hT,
      Repr.eval_reindex T σ A B (comprehension_type_eq hT)]
    generalize T.comprehension.eval A B (comprehension_type_eq hT) = b
    induction b using Quotient.inductionOn with
    | h B => rfl

@[simp] theorem map_piApp (A : y Γ₁ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (σ : Γ₂ ⟶ Γ₁) :
    (Ty E ℓ).map σ.op (piApp A B) =
      piApp (y σ ≫ A) (ℒ.fibreMap A (y σ) ≫ B) :=
  (NatTrans.naturality_apply (pi E ℓ) σ.op ⟨A, B⟩).symm

@[simp] theorem piApp_pairPresheaf_map (L : Pair Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    piApp ((pairPresheaf E ℓ).map σ.op L).1 ((pairPresheaf E ℓ).map σ.op L).2 =
      (Ty E ℓ).map σ.op (piApp L.1 L.2) :=
  (map_piApp L.1 L.2 σ).symm

theorem piApp_eq_ofRepr (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (T : Repr Γ) (hT : yonedaEquiv A = ⟦T⟧) (C : Repr ⟨Γ.as.snoc T.wf⟩)
    (hC : ⟦C⟧ = T.comprehension.eval A B (comprehension_type_eq hT)) :
    piApp A B = ⟦T.forallE C⟧ := by
  rw [piApp_eq A B T hT, ← hC]
  rfl

def forallE (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ) :
    y Γ ⟶ Ty E ℓ :=
  yonedaEquiv.symm (piApp A B)

theorem forallE_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (T : Repr Γ) (hT : yonedaEquiv A = ⟦T⟧) (C : Repr ⟨Γ.as.snoc T.wf⟩)
    (hC : ⟦C⟧ = T.comprehension.eval A B (comprehension_type_eq hT)) :
    yonedaEquiv (forallE A B) = ⟦T.forallE C⟧ := by
  rw [forallE, Equiv.apply_symm_apply, piApp_eq A B T hT, ← hC]
  rfl

theorem map_forallE (A : y Γ₁ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (σ : Γ₂ ⟶ Γ₁) :
    y σ ≫ forallE A B =
      forallE (y σ ≫ A) (ℒ.fibreMap A (y σ) ≫ B) :=
  (yonedaEquiv_symm_naturality_left σ (Ty E ℓ) (piApp A B)).trans
    (congrArg yonedaEquiv.symm
      (NatTrans.naturality_apply (pi E ℓ) σ.op ⟨A, B⟩).symm)

def familyOfTyping (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len} {t' : Expr ζ ℓ (Γ.len + 1)}
    {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ t : .sort u) (ht' : E[Γ.ctx.snoc t] ⊢ t' : .sort v) :
    pullback (CtxCat.rawComprehension ht).type (Tm.typing E ℓ) ⟶ Ty E ℓ :=
  (CtxCat.rawComprehension ht).family (⟦⟨t', v, ht'⟩⟧)

def pairOfTyping (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len} {t' : Expr ζ ℓ (Γ.len + 1)}
    {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ t : .sort u) (ht' : E[Γ.ctx.snoc t] ⊢ t' : .sort v) :
    Pair (⟨Γ⟩ : CtxCat E ℓ) :=
  ⟨(CtxCat.rawComprehension ht).type, familyOfTyping Γ ht ht'⟩

@[simp] theorem eval_familyOfTyping (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len}
    {t' : Expr ζ ℓ (Γ.len + 1)} {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ t : .sort u)
    (ht' : E[Γ.ctx.snoc t] ⊢ t' : .sort v) :
    (CtxCat.rawComprehension ht).eval (CtxCat.rawComprehension ht).type (familyOfTyping Γ ht ht') rfl =
      ⟦⟨t', v, ht'⟩⟧ :=
  Comprehension.eval_family _ _

@[simp] theorem piApp_ofTyping (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len}
    {t' : Expr ζ ℓ (Γ.len + 1)} {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ t : .sort u)
    (ht' : E[Γ.ctx.snoc t] ⊢ t' : .sort v) :
    piApp (pairOfTyping Γ ht ht').1 (pairOfTyping Γ ht ht').2 =
      ofTyping Γ (.forallEDF ht ht' ht') :=
  piApp_eq_ofRepr _ _ ⟨t, u, ht⟩ (yonedaEquiv.apply_symm_apply _) ⟨t', v, ht'⟩
    (eval_familyOfTyping Γ ht ht').symm

theorem pairOfTyping_eq_iff (Γ : RawCtx E ℓ) {t₁ t₂ : Expr ζ ℓ Γ.len}
    {t₁' t₂' : Expr ζ ℓ (Γ.len + 1)} {u₁ v₁ u₂ v₂ : Level ℓ}
    (ht₁ : E[Γ.ctx] ⊢ t₁ : .sort u₁) (ht₁' : E[Γ.ctx.snoc t₁] ⊢ t₁' : .sort v₁)
    (ht₂ : E[Γ.ctx] ⊢ t₂ : .sort u₂) (ht₂' : E[Γ.ctx.snoc t₂] ⊢ t₂' : .sort v₂) :
    pairOfTyping Γ ht₁ ht₁' = pairOfTyping Γ ht₂ ht₂' ↔
      E[Γ.ctx] ⊢ t₁ ≡ t₂ typ ∧
      E[Γ.ctx.snoc t₁] ⊢ t₁' ≡ t₂' typ ∧
      E[Γ.ctx.snoc t₂] ⊢ t₁' ≡ t₂' typ := by
  have hconv (hd : E[Γ.ctx] ⊢ t₁ ≡ t₂ typ)
      (hA : (CtxCat.rawComprehension ht₂).type = (CtxCat.rawComprehension ht₁).type) :
      (CtxCat.rawComprehension ht₁).eval (CtxCat.rawComprehension ht₂).type (familyOfTyping Γ ht₂ ht₂') hA =
        ⟦⟨t₂'.subst Subst.id, v₂, Defeq.substitution (RawCtx.Hom.convert Γ hd.symm).typed ht₂'⟩⟧ :=
    (Repr.eval_conversion ⟨t₂, u₂, ht₂⟩ ⟨t₁, u₁, ht₁⟩ hd.symm _ _ rfl hA).trans
      (congrArg ((Ty E ℓ).map (RawCtx.toCtx.map (RawCtx.Hom.convert Γ hd.symm)).op)
        (eval_familyOfTyping Γ ht₂ ht₂'))
  constructor
  · intro h
    have hA := congrArg Sigma.fst h
    have hd := Quotient.exact (yonedaEquiv.symm.injective hA)
    have e := ((eval_familyOfTyping Γ ht₁ ht₁').symm.trans
      ((CtxCat.rawComprehension ht₁).eval_congr h rfl hA.symm)).trans (hconv hd hA.symm)
    have hb := Quotient.exact e
    change E[Γ.ctx.snoc t₁] ⊢ t₁' ≡ t₂'.subst Subst.id typ at hb
    rw [Expr.subst_id] at hb
    exact ⟨hd, hb, hd.snocConvTy hb⟩
  · intro ⟨hd, hb, _⟩
    have hA : (CtxCat.rawComprehension ht₂).type = (CtxCat.rawComprehension ht₁).type :=
      congrArg yonedaEquiv.symm
        (Quotient.sound hd.symm)
    refine Eq.trans ?_ ((CtxCat.rawComprehension ht₁).label_eval (CtxCat.rawComprehension ht₂).type
      (familyOfTyping Γ ht₂ ht₂') hA)
    rw [hconv hd hA]
    exact congrArg (CtxCat.rawComprehension ht₁).label (Quotient.sound (by simpa))

theorem pairOfTyping_congr (Γ : RawCtx E ℓ) {t₁ t₂ : Expr ζ ℓ Γ.len}
    {t₁' t₂' : Expr ζ ℓ (Γ.len + 1)} {u v : Level ℓ}
    (ht : E[Γ.ctx] ⊢ t₁ ≡ t₂ : .sort u) (ht' : E[Γ.ctx.snoc t₁] ⊢ t₁' ≡ t₂' : .sort v) :
    pairOfTyping Γ ht.left ht'.left =
      pairOfTyping Γ ht.right (Defeq.snocConvTy (.ofDefEq ht) ht').right :=
  (pairOfTyping_eq_iff _ _ _ _ _).mpr
    ⟨.ofDefEq ht, .ofDefEq ht', .ofDefEq (Defeq.snocConvTy (.ofDefEq ht) ht')⟩

@[simp] theorem pairPresheaf_map_ofTyping {t : Expr ζ ℓ Γ₁.as.len} {t' : Expr ζ ℓ (Γ₁.as.len + 1)}
    {u v : Level ℓ} (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ t' : .sort v)
    (σ : Γ₂.as ⟶ Γ₁.as) :
    (pairPresheaf E ℓ).map (RawCtx.toCtx.map σ).op (pairOfTyping Γ₁.as ht ht') =
      pairOfTyping Γ₂.as (ht.substitution σ.typed)
        (ht'.substitution (SubstWF.lift ⟨u, ht⟩ σ.typed)) :=
  (CtxCat.rawComprehension ht).label_reindex (CtxCat.rawComprehension (ht.substitution σ.typed))
    (RawCtx.toCtx.map σ) (CtxCat.extensionMap ht σ) (CtxCat.extensionMap_projection ht σ)
    (CtxCat.map_extensionMap_binderVar ht σ)
    ((⟨t, u, ht⟩ : Repr Γ₁).comprehension_type_reindex σ) _

end Ty

end Metalean
