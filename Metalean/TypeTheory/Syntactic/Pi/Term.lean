/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Pi.Type
import Metalean.Strong

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

theorem lam_conversion (T₁ T₂ : Repr Γ) (h : E[Γ.as.ctx] ⊢ₛ T₁.term ≡ T₂.term typ)
    (c : Tm_(⟨Γ.as.snoc T₁.wf⟩ : CtxCat E ℓ)) :
    T₂.lam ((Tm E ℓ).map (RawCtx.toCtx.map (RawCtx.Hom.convert Γ.as h)).op c) =
      T₁.lam c := by
  induction c using Quotient.inductionOn with
  | h R =>
    have ⟨_, hB⟩ := R.tyWF
    have hty : E[Γ.as.ctx] ⊢ₛ .forallE T₂.term (R.ty.subst Subst.id) ≡
        .forallE T₁.term R.ty typ := by
      rw [Expr.subst_id]
      exact IsTypeEq.forallE_dom h.symm (DefeqStrong.snocConvTy h hB)
    have hval : E[Γ.as.ctx] ⊢ₛ .lam T₂.term (R.val.subst Subst.id) ≡ .lam T₁.term R.val :
        .forallE T₂.term (R.ty.subst Subst.id) := by
      rw [Expr.subst_id, Expr.subst_id]
      exact IsTypeEq.lam_dom h.symm (DefeqStrong.snocConvTy h hB)
        (DefeqStrong.snocConvTy h R.valWF)
    exact Quotient.sound ⟨hty, hval⟩

end Ty.Repr

namespace Tm

def lamApp (A : y Γ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ Tm E ℓ) : Tm_ Γ :=
  Ty.elim (yonedaEquiv A) (fun T hT => T.lam (T.comprehension.eval A B (Ty.comprehension_type_eq hT)))
    fun T₁ T₂ h₁ h₂ => by
      have h := (Ty.ofRepr_eq_iff _ _).mp (h₁.symm.trans h₂)
      rw [Ty.Repr.eval_conversion T₁ T₂ h A B _ _, Ty.Repr.lam_conversion]

theorem lamApp_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ Tm E ℓ)
    (T : Ty.Repr Γ) (hT : yonedaEquiv A = Ty.ofRepr T) :
    lamApp A B = T.lam (T.comprehension.eval A B (Ty.comprehension_type_eq hT)) :=
  Ty.elim_eq _ _ _ T hT

def lam (E : Env ζ) (ℓ : Nat) :
    (polynomial (Ty E ℓ)).obj (Tm E ℓ) ⟶ Tm E ℓ where
  app Γ := ↾fun ⟨A, B⟩ => lamApp A B
  naturality := by
    intro ⟨Γ₁⟩ ⟨Γ₂⟩ ⟨σ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    apply ConcreteCategory.hom_ext
    intro ⟨A, B⟩
    obtain ⟨T, hT⟩ := Ty.exists_ofRepr (yonedaEquiv A)
    change lamApp (y (RawCtx.toCtx.map σ) ≫ A)
        (fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B) =
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
    (hf : E[Γ.as.ctx] ⊢ₛ f : .forallE T.term B.term) (ha : E[Γ.as.ctx] ⊢ₛ a : T.term) :
    E[Γ.as.ctx] ⊢ₛ .app f a : B.term.inst a :=
  have ⟨_, ht⟩ := T.wf
  have ⟨_, hB⟩ := B.wf
  .appDF ht hB hf ha (DefeqStrong.inst_congr hB ha)

def apply (T : Ty.Repr Γ) (B : Ty.Repr ⟨Γ.as.snoc T.wf⟩) (n m : Tm_ Γ)
    (hn : Tm.type n = ofRepr (T.forallE B)) (hm : Tm.type m = ofRepr T) : Tm_ Γ :=
  Tm.elim n (T.forallE B) hn
    (fun f hf => Tm.elim m T hm (fun a ha => label Γ.as (app_wf T B hf ha))
      fun a₁ a₂ ha₁ _ ha => by
        have ⟨_, hB⟩ := B.wf
        have ⟨_, ht⟩ := T.wf
        exact label_eq (.ofDefEq (DefeqStrong.inst_congr hB ha))
          (.appDF ht hB hf ha (DefeqStrong.inst_congr hB ha)))
    fun f₁ f₂ hf₁ _ hf => by
      have ⟨a, ha, hma⟩ := Tm.exists_label m T hm
      rw [Tm.elim_eq m T hm _ _ ha hma, Tm.elim_eq m T hm _ _ ha hma]
      have ⟨_, hB⟩ := B.wf
      have ⟨_, ht⟩ := T.wf
      exact label_eq (.ofDefEq (DefeqStrong.inst_congr hB ha))
        (.appDF ht hB hf ha (DefeqStrong.inst_congr hB ha))

theorem apply_eq (T : Ty.Repr Γ) (B : Ty.Repr ⟨Γ.as.snoc T.wf⟩) (n m : Tm_ Γ)
    (hn : Tm.type n = ofRepr (T.forallE B)) (hm : Tm.type m = ofRepr T) {f a : Expr ζ ℓ Γ.as.len}
    (hf : E[Γ.as.ctx] ⊢ₛ f : .forallE T.term B.term) (ha : E[Γ.as.ctx] ⊢ₛ a : T.term)
    (hnf : n = label Γ.as hf) (hma : m = label Γ.as ha) :
    apply T B n m hn hm = label Γ.as (app_wf T B hf ha) := by
  rw [apply, Tm.elim_eq _ _ _ _ _ hf hnf, Tm.elim_eq _ _ _ _ _ ha hma]

theorem apply_congr (T₁ T₂ : Ty.Repr Γ) (B₁ : Ty.Repr ⟨Γ.as.snoc T₁.wf⟩)
    (B₂ : Ty.Repr ⟨Γ.as.snoc T₂.wf⟩) (hT : E[Γ.as.ctx] ⊢ₛ T₁.term ≡ T₂.term typ)
    (hB : E[Γ.as.ctx.snoc T₁.term] ⊢ₛ B₁.term ≡ B₂.term typ) (n m : Tm_ Γ)
    (hn₁ : Tm.type n = ofRepr (T₁.forallE B₁)) (hm₁ : Tm.type m = ofRepr T₁)
    (hn₂ : Tm.type n = ofRepr (T₂.forallE B₂)) (hm₂ : Tm.type m = ofRepr T₂) :
    apply T₁ B₁ n m hn₁ hm₁ = apply T₂ B₂ n m hn₂ hm₂ := by
  have ⟨f, hf, hnf⟩ := Tm.exists_label n _ hn₁
  have ⟨a, ha, hma⟩ := Tm.exists_label m _ hm₁
  have hpi : E[Γ.as.ctx] ⊢ₛ .forallE T₁.term B₁.term ≡ .forallE T₂.term B₂.term typ :=
    (ofRepr_eq_iff _ _).mp (hn₁.symm.trans hn₂)
  have ⟨_, hB₁⟩ := B₁.wf
  rw [apply_eq T₁ B₁ n m hn₁ hm₁ hf ha hnf hma,
    apply_eq T₂ B₂ n m hn₂ hm₂ (hpi.convStrong hf) (hT.convStrong ha)
      (hnf.trans (label_eq hpi hf)) (hma.trans (label_eq hT ha))]
  exact label_eq (hB.inst_congr₂ ha) (app_wf T₁ B₁ hf ha)

end Repr

def apply (A : y Γ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ Ty E ℓ) (n m : Tm_ Γ)
    (h : Tm.type n = Ty.piApp A B) (hm : Tm.type m = yonedaEquiv A) : Tm_ Γ :=
  Ty.elim (yonedaEquiv A)
    (fun T hT => Quotient.liftFibre (T.comprehension.eval A B (Ty.comprehension_type_eq hT))
      (fun C hC => Repr.apply T C n m (h.trans (Ty.piApp_eq_ofRepr A B T hT C hC)) (hm.trans hT))
      fun C₁ C₂ hC₁ hC₂ => Repr.apply_congr T T C₁ C₂ T.wf.isTypeEq
        (Quotient.exact (hC₁.trans hC₂.symm)) n m _ _ _ _)
    fun T₁ T₂ h₁ h₂ => by
      have hT := (ofRepr_eq_iff _ _).mp (h₁.symm.trans h₂)
      have ⟨C₁, hC₁⟩ := Quotient.exists_rep (T₁.comprehension.eval A B (Ty.comprehension_type_eq h₁))
      have hC₂ : ⟦(⟨C₁.term.subst Subst.id, C₁.wf.substitution
          (RawCtx.Hom.convert Γ.as hT).typed⟩ : Ty.Repr ⟨Γ.as.snoc T₂.wf⟩)⟧ =
          T₂.comprehension.eval A B (Ty.comprehension_type_eq h₂) := by
        rw [T₁.eval_conversion T₂ hT A B (Ty.comprehension_type_eq h₁) (Ty.comprehension_type_eq h₂),
          ← hC₁]
        rfl
      rw [Quotient.liftFibre_eq _ _ _ C₁ hC₁, Quotient.liftFibre_eq _ _ _ _ hC₂]
      exact Repr.apply_congr T₁ T₂ C₁ _ hT
        ((congrArg (E[Γ.as.ctx.snoc T₁.term] ⊢ₛ C₁.term ≡ · typ) (Expr.subst_id C₁.term)).mpr
          C₁.wf.isTypeEq) n m _ _ _ _

theorem apply_eq (A : y Γ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ Ty E ℓ)
    (n m : Tm_ Γ) (h : Tm.type n = Ty.piApp A B)
    (hm : Tm.type m = yonedaEquiv A) (T : Ty.Repr Γ) (hT : yonedaEquiv A = ofRepr T)
    (C : Ty.Repr ⟨Γ.as.snoc T.wf⟩) (hC : ⟦C⟧ = T.comprehension.eval A B (Ty.comprehension_type_eq hT))
    {f a : Expr ζ ℓ Γ.as.len} (hf : E[Γ.as.ctx] ⊢ₛ f : .forallE T.term C.term)
    (ha : E[Γ.as.ctx] ⊢ₛ a : T.term) (hnf : n = label Γ.as hf) (hma : m = label Γ.as ha) :
    apply A B n m h hm = label Γ.as (Repr.app_wf T C hf ha) := by
  rw [apply, Ty.elim_eq _ _ _ T hT, Quotient.liftFibre_eq _ _ _ C hC]
  exact Repr.apply_eq T C n m _ _ hf ha hnf hma

theorem apply_congr {A A' : y Γ ⟶ Ty E ℓ} {B : pullback A (Tm.typing E ℓ) ⟶ Ty E ℓ}
    {B' : pullback A' (Tm.typing E ℓ) ⟶ Ty E ℓ}
    (e : (⟨A, B⟩ : Ty.Pair Γ) = ⟨A', B'⟩) {n n' m m' : Tm_ Γ} (en : n = n') (em : m = m')
    (h : Tm.type n = Ty.piApp A B) (hm : Tm.type m = yonedaEquiv A)
    (h' : Tm.type n' = Ty.piApp A' B') (hm' : Tm.type m' = yonedaEquiv A') :
    apply A B n m h hm = apply A' B' n' m' h' hm' := by
  cases e
  cases en
  cases em
  rfl

theorem apply_label (Γ : RawCtx E ℓ) {t e f : Expr ζ ℓ Γ.len}
    {t' : Expr ζ ℓ (Γ.len + 1)} {u v : Level ℓ} (ht : E[Γ.ctx] ⊢ₛ t : .sort u)
    (ht' : E[Γ.ctx.snoc t] ⊢ₛ t' : .sort v) (hf : E[Γ.ctx] ⊢ₛ f : .forallE t t')
    (he : E[Γ.ctx] ⊢ₛ e : t) (hres : E[Γ.ctx] ⊢ₛ t'.inst e : .sort v)
    (h : Tm.type (label Γ hf) =
      Ty.piApp (CtxCat.rawComprehension ht).type (Ty.familyOfTyping Γ ht ht'))
    (hm : Tm.type (label Γ he) = yonedaEquiv (CtxCat.rawComprehension ht).type) :
    apply (CtxCat.rawComprehension ht).type (Ty.familyOfTyping Γ ht ht')
        (label Γ hf) (label Γ he) h hm =
      label Γ (.appDF ht ht' hf he hres) :=
  apply_eq (Γ := ⟨Γ⟩) _ _ _ _ h hm ⟨t, u, ht⟩ (yonedaEquiv.apply_symm_apply _) ⟨t', v, ht'⟩
    (Ty.eval_familyOfTyping Γ ht ht').symm hf he rfl rfl

theorem map_apply (A : y Γ₁ ⟶ Ty E ℓ) (B : pullback A (Tm.typing E ℓ) ⟶ Ty E ℓ)
    (n m : Tm_ Γ₁) (h : Tm.type n = Ty.piApp A B)
    (hm : Tm.type m = yonedaEquiv A) (σ : Γ₂ ⟶ Γ₁)
    (h' : Tm.type ((Tm E ℓ).map σ.op n) =
      Ty.piApp (y σ ≫ A) (fibreMap A (y σ) ≫ B))
    (hm' : Tm.type ((Tm E ℓ).map σ.op m) = yonedaEquiv (y σ ≫ A)) :
    (Tm E ℓ).map σ.op (apply A B n m h hm) =
      apply (y σ ≫ A) (fibreMap A (y σ) ≫ B)
        ((Tm E ℓ).map σ.op n) ((Tm E ℓ).map σ.op m) h' hm' := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  have ⟨T, hT⟩ := exists_ofRepr (yonedaEquiv A)
  have ⟨C, hC⟩ := Quotient.exists_rep (T.comprehension.eval A B (Ty.comprehension_type_eq hT))
  have hn := h.trans (Ty.piApp_eq_ofRepr A B T hT C hC)
  have ⟨f, hf, hnf⟩ := Tm.exists_label n _ hn
  have ⟨a, ha, hma⟩ := Tm.exists_label m _ (hm.trans hT)
  have hTσ := Ty.reindex_yonedaEquiv hT σ
  have hCσ : ⟦(⟨C.term.subst σ.subst.lift, C.wf.substitution (σ.lift T.wf).typed⟩ :
      Ty.Repr ⟨Γ₂.as.snoc (T.reindex σ).wf⟩)⟧ =
      (T.reindex σ).comprehension.eval (y (RawCtx.toCtx.map σ) ≫ A)
        (fibreMap A (y (RawCtx.toCtx.map σ)) ≫ B)
        (Ty.comprehension_type_eq hTσ) := by
    refine Eq.trans ?_ (T.eval_reindex σ A B (Ty.comprehension_type_eq hT)).symm
    rw [← hC]
    rfl
  rw [apply_eq A B n m h hm T hT C hC hf ha hnf hma, map_label]
  refine Eq.trans ?_ (apply_eq _ _ _ _ h' hm' (T.reindex σ) hTσ _ hCσ (hf.substitution σ.typed)
    (ha.substitution σ.typed) (by rw [hnf, map_label]; exact label_congr rfl)
    (by rw [hma, map_label]; exact label_congr rfl)).symm
  exact label_congr (Expr.inst_subst _ _ _)

end Tm

end Metalean
