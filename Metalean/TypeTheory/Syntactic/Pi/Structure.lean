/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Metalean.TypeTheory.NaturalModel.Pi
public import Metalean.TypeTheory.Syntactic.Pi.Term
import Metalean.Strong

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Opposite Limits TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

theorem piStructure_isPullback (E : Env ζ) (ℓ : Nat) :
    IsPullback (Tm.lam E ℓ) ((polynomial (Ty E ℓ)).map (Tm.typing E ℓ))
      (Tm.typing E ℓ) (Ty.pi E ℓ) := by
  refine IsPullback.of_forall_isPullback_app fun Γ => (Types.isPullback_iff _ _ _ _).mpr
    ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro ⟨A, B⟩
    obtain ⟨T, hT⟩ := Ty.exists_ofRepr (yonedaEquiv A)
    change Tm.type (Tm.lamApp A B) = Ty.piApp A (B ≫ Tm.typing E ℓ)
    rw [Tm.lamApp_eq A B T hT, Ty.piApp_eq A _ T hT]
    change Tm.type (T.lam (T.comprehension.eval A B (Ty.comprehension_type_eq hT))) =
      T.pi (Tm.type (T.comprehension.eval A B (Ty.comprehension_type_eq hT)))
    generalize T.comprehension.eval A B (Ty.comprehension_type_eq hT) = c
    induction c using Quotient.inductionOn with
    | h R => rfl
  · intro ⟨A₁, B₁⟩ ⟨A₂, B₂⟩ ⟨hlam, hp⟩
    change Tm.lamApp A₁ B₁ = Tm.lamApp A₂ B₂ at hlam
    have h₁₂ : A₁ = A₂ := congrArg Sigma.fst hp
    obtain ⟨T, hT₁⟩ := Ty.exists_ofRepr (yonedaEquiv A₁)
    have hT₂ := (congrArg yonedaEquiv h₁₂).symm.trans hT₁
    rw [Tm.lamApp_eq A₁ B₁ T hT₁, Tm.lamApp_eq A₂ B₂ T hT₂] at hlam
    have hpe := T.comprehension.eval_congr hp (Ty.comprehension_type_eq hT₁) (Ty.comprehension_type_eq hT₂)
    change Tm.type (T.comprehension.eval A₁ B₁ (Ty.comprehension_type_eq hT₁)) =
      Tm.type (T.comprehension.eval A₂ B₂ (Ty.comprehension_type_eq hT₂)) at hpe
    rw [← T.comprehension.label_eval A₁ B₁ (Ty.comprehension_type_eq hT₁),
      ← T.comprehension.label_eval A₂ B₂ (Ty.comprehension_type_eq hT₂)]
    refine congrArg T.comprehension.label ?_
    generalize T.comprehension.eval A₁ B₁ (Ty.comprehension_type_eq hT₁) = c₁ at hlam hpe ⊢
    generalize T.comprehension.eval A₂ B₂ (Ty.comprehension_type_eq hT₂) = c₂ at hlam hpe ⊢
    induction c₁ using Quotient.inductionOn with | h R₁ => ?_
    induction c₂ using Quotient.inductionOn with | h R₂ => ?_
    have hty : E[Γ.unop.as.ctx.snoc T.term] ⊢ₛ R₁.ty ≡ R₂.ty typ := Quotient.exact hpe
    have ⟨_, hval⟩ := Quotient.exact hlam
    have ⟨_, ht⟩ := T.wf
    have ⟨_, hB⟩ := R₁.tyWF
    exact Quotient.sound ⟨hty, DefeqStrong.lam_body Γ.unop.as.wf ht hB R₁.valWF
      (hty.symm.convStrong R₂.valWF) hval⟩
  · intro c ⟨A, B⟩ h
    change Tm.type c = Ty.piApp A B at h
    obtain ⟨T, hT⟩ := Ty.exists_ofRepr (yonedaEquiv A)
    have ⟨C, hC⟩ := Quotient.exists_rep (T.comprehension.eval A B (Ty.comprehension_type_eq hT))
    have ⟨R, hR⟩ := Quotient.exists_rep c
    rw [Ty.piApp_eq A B T hT, ← hC, ← hR] at h
    have hRty : E[Γ.unop.as.ctx] ⊢ₛ R.ty ≡ .forallE T.term C.term typ := Quotient.exact h
    have hf := hRty.convStrong R.valWF
    have ⟨_, ht⟩ := T.wf
    have ⟨v, hCt⟩ := C.wf
    have hΓ := Γ.unop.as.wf
    have hwk := SubstWFStrong.wk T.term hΓ
    have hlift := SubstWFStrong.lift T.wf hwk
    have hx : E[Γ.unop.as.ctx.snoc T.term] ⊢ₛ .var (Fin.last _) : T.term.subst Subst.wk := by
      rw [Expr.subst_wk]
      exact CtxWFStrong.varLast (Tele.Forall.snoc hΓ T.wf)
    have hCσ := hCt.substitution hlift
    have hres : E[Γ.unop.as.ctx.snoc T.term] ⊢ₛ
        (C.term.subst Subst.wk.lift).inst (.var (Fin.last _)) : .sort v := by
      rw [Expr.inst_subst_lift_wk_last]
      exact hCt
    have hfσ : E[Γ.unop.as.ctx.snoc T.term] ⊢ₛ R.val.subst Subst.wk :
        .forallE (T.term.subst Subst.wk) (C.term.subst Subst.wk.lift) :=
      hf.substitution hwk
    have happ := DefeqStrong.appDF (ht.substitution hwk) hCσ hfσ hx hres
    rw [Expr.inst_subst_lift_wk_last] at happ
    let k : Tm_ (⟨Γ.unop.as.snoc T.wf⟩ : CtxCat E ℓ) :=
      ⟦⟨C.term, .app (R.val.subst Subst.wk) (.var (Fin.last _)), C.wf, happ⟩⟧
    refine ⟨T.comprehension.label (X := Tm E ℓ) k, ?_, ?_⟩
    · refine (Tm.lamApp_eq T.comprehension.type (T.comprehension.family k) T
        (yonedaEquiv.apply_symm_apply _)).trans ?_
      rw [Comprehension.eval_family, ← hR]
      have htw := ht.substitution hwk
      have hfw := hfσ
      rw [Expr.subst_wk, Expr.subst_wk, ← Subst.wkFrom_eq_lift_wk, ← Expr.wkFrom_eq_subst] at hfw
      rw [Expr.subst_wk] at htw
      have hη := DefeqStrong.eta ht hCt htw hfw hf
      rw [← Expr.subst_wk] at hη
      exact Quotient.sound ⟨hRty.symm, hη⟩
    · refine (Comprehension.map_label T.comprehension (Tm.typing E ℓ) _).trans ?_
      rw [← T.comprehension.label_eval A B (Ty.comprehension_type_eq hT), ← hC]
      rfl

instance : HasPi (Ty E ℓ) (Tm E ℓ) where
  pi := Ty.pi E ℓ
  lam := Tm.lam E ℓ
  isPullback := piStructure_isPullback E ℓ

end Metalean
