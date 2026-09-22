/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Pi.Type

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Opposite Limits TypeTheory TypeTheory.NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace Ty.Repr

def lam (T : Repr Γ) : Tm_ (⟨Γ.as.snoc T.wf⟩ : CtxCat E ℓ) → Tm_ Γ :=
  Quotient.lift
    (fun R => ⟦(⟨.forallE T.term R.ty, .lam T.term R.val, forallE_wf T ⟨R.ty, R.tyWF⟩,
      have ⟨_, ht⟩ := T.wf
      have ⟨_, hB⟩ := R.tyWF
      .lamDF ht hB hB R.valWF R.valWF⟩ : Tm.Repr Γ)⟧)
    fun R₁ _ ⟨hty, hval⟩ =>
      have ⟨_, ht⟩ := T.wf
      have ⟨_, hB⟩ := R₁.tyWF
      Quotient.sound ⟨IsTypeEq.forallE_cod ht hty, .lamDF ht hB hB hval hval⟩

theorem lam_conversion (T₁ T₂ : Repr Γ) (h : E[Γ.as.ctx] ⊢ T₁.term ≡ T₂.term typ)
    (c : Tm_(⟨Γ.as.snoc T₁.wf⟩ : CtxCat E ℓ)) :
    T₂.lam ((Tm E ℓ).map (RawCtx.toCtx.map (RawCtx.Hom.convert Γ.as h)).op c) =
      T₁.lam c := by
  induction c using Quotient.inductionOn with
  | h R =>
    have ⟨_, hB⟩ := R.tyWF
    have hty : E[Γ.as.ctx] ⊢ .forallE T₂.term (R.ty.subst Subst.id) ≡
        .forallE T₁.term R.ty typ := by
      rw [Expr.subst_id]
      exact IsTypeEq.forallE_dom h.symm (Defeq.snocConvTy h hB)
    have hval : E[Γ.as.ctx] ⊢ .lam T₂.term (R.val.subst Subst.id) ≡ .lam T₁.term R.val :
        .forallE T₂.term (R.ty.subst Subst.id) := by
      rw [Expr.subst_id, Expr.subst_id]
      exact IsTypeEq.lam_dom h.symm (Defeq.snocConvTy h hB) (Defeq.snocConvTy h R.valWF)
    exact Quotient.sound ⟨hty, hval⟩

end Ty.Repr

namespace Tm

def lamApp (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Tm E ℓ) : Tm_ Γ :=
  Ty.elim (yonedaEquiv A) (fun T hT => T.lam (T.comprehension.eval A B (Ty.comprehension_type_eq hT)))
    fun T₁ T₂ h₁ h₂ => by
      have h := Quotient.exact (h₁.symm.trans h₂)
      rw [Ty.Repr.eval_conversion T₁ T₂ h A B _ _, Ty.Repr.lam_conversion]

theorem lamApp_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Tm E ℓ)
    (T : Ty.Repr Γ) (hT : yonedaEquiv A = ⟦T⟧) :
    lamApp A B = T.lam (T.comprehension.eval A B (Ty.comprehension_type_eq hT)) :=
  Ty.elim_eq _ _ _ T hT

def lam (E : Env ζ) (ℓ : Nat) :
    ℒ.polynomial.obj (Tm E ℓ) ⟶ Tm E ℓ where
  app Γ := ↾fun ⟨A, B⟩ => lamApp A B
  naturality := by
    intro ⟨Γ₁⟩ ⟨Γ₂⟩ ⟨σ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    ext ⟨A, B⟩
    obtain ⟨T, hT⟩ := Quotient.exists_rep (yonedaEquiv A)
    have hT := hT.symm
    change lamApp (y (RawCtx.toCtx.map σ) ≫ A)
        (ℒ.fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B) =
      (Tm E ℓ).map (RawCtx.toCtx.map σ).op (lamApp A B)
    rw [lamApp_eq _ _ (T.reindex σ) (Ty.reindex_yonedaEquiv hT σ), lamApp_eq A B T hT,
      Ty.Repr.eval_reindex T σ A B (Ty.comprehension_type_eq hT)]
    generalize T.comprehension.eval A B (Ty.comprehension_type_eq hT) = c
    induction c using Quotient.inductionOn with
    | h R => rfl

end Tm

namespace Tm

open Ty

namespace Repr

theorem app_wf (T : Ty.Repr Γ) (B : Ty.Repr ⟨Γ.as.snoc T.wf⟩) {f a : Expr ζ ℓ Γ.as.len}
    (hf : E[Γ.as.ctx] ⊢ f : .forallE T.term B.term) (ha : E[Γ.as.ctx] ⊢ a : T.term) :
    E[Γ.as.ctx] ⊢ .app f a : B.term.inst a :=
  have ⟨_, ht⟩ := T.wf
  have ⟨_, hB⟩ := B.wf
  .appDF ht hB hf ha (Defeq.inst_congr hB ha)

def apply (T : Ty.Repr Γ) (B : Ty.Repr ⟨Γ.as.snoc T.wf⟩) (n m : Tm_ Γ)
    (hn : Tm.type n = ⟦T.forallE B⟧) (hm : Tm.type m = ⟦T⟧) : Tm_ Γ :=
  Tm.elim n (T.forallE B) hn
    (fun f hf => Tm.elim m T hm (fun a ha => label Γ.as (app_wf T B hf ha))
      fun a₁ a₂ ha₁ _ ha => by
        have ⟨_, hB⟩ := B.wf
        have ⟨_, ht⟩ := T.wf
        exact label_eq (.ofDefEq (Defeq.inst_congr hB ha))
          (.appDF ht hB hf ha (Defeq.inst_congr hB ha)))
    fun f₁ f₂ hf₁ _ hf => by
      obtain ⟨a, ha, rfl⟩ := Tm.exists_label m T hm
      have ⟨_, hB⟩ := B.wf
      have ⟨_, ht⟩ := T.wf
      exact label_eq (.ofDefEq (Defeq.inst_congr hB ha))
        (.appDF ht hB hf ha (Defeq.inst_congr hB ha))

theorem apply_congr (T₁ T₂ : Ty.Repr Γ) (B₁ : Ty.Repr ⟨Γ.as.snoc T₁.wf⟩)
    (B₂ : Ty.Repr ⟨Γ.as.snoc T₂.wf⟩)
    (hB : E[Γ.as.ctx.snoc T₁.term] ⊢ B₁.term ≡ B₂.term typ) (n m : Tm_ Γ)
    (hn₁ : Tm.type n = ⟦T₁.forallE B₁⟧) (hm₁ : Tm.type m = ⟦T₁⟧)
    (hn₂ : Tm.type n = ⟦T₂.forallE B₂⟧) (hm₂ : Tm.type m = ⟦T₂⟧) :
    apply T₁ B₁ n m hn₁ hm₁ = apply T₂ B₂ n m hn₂ hm₂ := by
  obtain ⟨f, hf, rfl⟩ := Tm.exists_label n _ hn₁
  obtain ⟨a, ha, rfl⟩ := Tm.exists_label m _ hm₁
  exact label_eq (hB.inst_congr₂ ha) (app_wf T₁ B₁ hf ha)

end Repr

def apply (L : Ty.Pair Γ) (n m : Tm_ Γ)
    (h : Tm.type n = Ty.piApp L.1 L.2) (hm : Tm.type m = yonedaEquiv L.1) : Tm_ Γ :=
  Ty.elim (yonedaEquiv L.1)
    (fun T hT => Ty.elim (T.comprehension.eval L.1 L.2 (Ty.comprehension_type_eq hT))
      (fun C hC => Repr.apply T C n m (h.trans (Ty.piApp_eq_ofRepr L.1 L.2 T hT C hC.symm)) (hm.trans hT))
      fun C₁ C₂ hC₁ hC₂ => Repr.apply_congr T T C₁ C₂
        (Quotient.exact (hC₁.symm.trans hC₂)) n m _ _ _ _)
    fun T₁ T₂ h₁ h₂ => by
      have hT := Quotient.exact (h₁.symm.trans h₂)
      have ⟨C₁, hC₁⟩ := Quotient.exists_rep (T₁.comprehension.eval L.1 L.2 (Ty.comprehension_type_eq h₁))
      have hC₂ : ⟦(⟨C₁.term.subst Subst.id, C₁.wf.substitution
          (RawCtx.Hom.convert Γ.as hT).typed⟩ : Ty.Repr ⟨Γ.as.snoc T₂.wf⟩)⟧ =
          T₂.comprehension.eval L.1 L.2 (Ty.comprehension_type_eq h₂) := by
        rw [T₁.eval_conversion T₂ hT L.1 L.2 (Ty.comprehension_type_eq h₁) (Ty.comprehension_type_eq h₂),
          ← hC₁]
        rfl
      rw [Ty.elim_eq _ _ _ C₁ hC₁.symm, Ty.elim_eq _ _ _ _ hC₂.symm]
      exact Repr.apply_congr T₁ T₂ C₁ _
        ((congrArg (E[Γ.as.ctx.snoc T₁.term] ⊢ C₁.term ≡ · typ) (Expr.subst_id C₁.term)).mpr
          C₁.wf.isTypeEq) n m _ _ _ _

theorem apply_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A ℒ.typing ⟶ Ty E ℓ)
    (T : Ty.Repr Γ) (hT : yonedaEquiv A = ⟦T⟧)
    (C : Ty.Repr ⟨Γ.as.snoc T.wf⟩) (hC : ⟦C⟧ = T.comprehension.eval A B (Ty.comprehension_type_eq hT))
    {f a : Expr ζ ℓ Γ.as.len} (hf : E[Γ.as.ctx] ⊢ f : .forallE T.term C.term)
    (ha : E[Γ.as.ctx] ⊢ a : T.term) :
    apply ⟨A, B⟩ (label Γ.as hf) (label Γ.as ha)
      (Ty.piApp_eq_ofRepr A B T hT C hC).symm hT.symm = label Γ.as (Repr.app_wf T C hf ha) := by
  unfold apply
  rw [Ty.elim_eq _ _ _ T hT, Ty.elim_eq _ _ _ C hC.symm]
  rfl

theorem apply_label (Γ : RawCtx E ℓ) {t e f : Expr ζ ℓ Γ.len}
    {t' : Expr ζ ℓ (Γ.len + 1)} {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ t : .sort u)
    (ht' : E[Γ.ctx.snoc t] ⊢ t' : .sort v) (hf : E[Γ.ctx] ⊢ f : .forallE t t')
    (he : E[Γ.ctx] ⊢ e : t) :
    apply (Ty.pairOfTyping Γ ht ht') (label Γ hf) (label Γ he)
        (Ty.piApp_ofTyping Γ ht ht').symm (CtxCat.rawComprehension_type ht).symm =
      label Γ (.appDF ht ht' hf he (Defeq.inst_congr ht' he)) :=
  apply_eq _ _ ⟨t, u, ht⟩ (yonedaEquiv.apply_symm_apply _) ⟨t', v, ht'⟩
    (Ty.eval_familyOfTyping Γ ht ht').symm hf he

theorem map_apply (L : Ty.Pair Γ₁)
    (n m : Tm_ Γ₁) (h : Tm.type n = Ty.piApp L.1 L.2)
    (hm : Tm.type m = yonedaEquiv L.1) (σ : Γ₂ ⟶ Γ₁) :
    (Tm E ℓ).map σ.op (apply L n m h hm) =
      apply ((Ty.pairPresheaf E ℓ).map σ.op L)
        ((Tm E ℓ).map σ.op n) ((Tm E ℓ).map σ.op m)
        (by rw [Tm.type_map, h, Ty.piApp_pairPresheaf_map])
        (by rw [Tm.type_map, hm]; exact yonedaEquiv_naturality L.1 σ) := by
  obtain ⟨A, B⟩ := L
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  obtain ⟨T, hT⟩ := Quotient.exists_rep (yonedaEquiv A)
  have hT := hT.symm
  have ⟨C, hC⟩ := Quotient.exists_rep (T.comprehension.eval A B (Ty.comprehension_type_eq hT))
  have hn := h.trans (Ty.piApp_eq_ofRepr A B T hT C hC)
  obtain ⟨f, hf, rfl⟩ := Tm.exists_label n _ hn
  obtain ⟨a, ha, rfl⟩ := Tm.exists_label m _ (hm.trans hT)
  have hTσ := Ty.reindex_yonedaEquiv hT σ
  have hCσ : ⟦(⟨C.term.subst σ.subst.lift, C.wf.substitution (σ.lift T.wf).typed⟩ :
      Ty.Repr ⟨Γ₂.as.snoc (T.reindex σ).wf⟩)⟧ =
      (T.reindex σ).comprehension.eval (y (RawCtx.toCtx.map σ) ≫ A)
        (ℒ.fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B)
        (Ty.comprehension_type_eq hTσ) := by
    refine Eq.trans ?_ (T.eval_reindex σ A B (Ty.comprehension_type_eq hT)).symm
    rw [← hC]
    rfl
  calc
    _ = _ := congr((Tm E ℓ).map (RawCtx.toCtx.map σ).op $(apply_eq A B T hT C hC hf ha))
    _ = _ := congr(label _ (t := $(Expr.inst_subst _ _ _)) _)
    _ = _ :=
      (apply_eq _ _ (T.reindex σ) hTσ _ hCσ (hf.substitution σ.typed)
        (ha.substitution σ.typed)).symm

end Tm

end Metalean
