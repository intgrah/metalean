/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Comprehension
public import Metalean.TypeTheory.Syntactic.Universe
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Metalean.Strong

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Limits Opposite TypeTheory TypeTheory.NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

namespace CtxCat

def projectionRaw (Γ : CtxCat E ℓ) {t : Expr ζ ℓ Γ.as.len} {u : Level ℓ}
    (ht : E[Γ.as.ctx] ⊢ₛ t : .sort u) :
    (extension Γ ht).as ⟶ Γ.as where
  subst := Subst.wk
  typed := SubstWFStrong.wk t Γ.as.wf

def rawProjection (Γ : CtxCat E ℓ) {t : Expr ζ ℓ Γ.as.len} {u : Level ℓ}
    (ht : E[Γ.as.ctx] ⊢ₛ t : .sort u) :
    extension Γ ht ⟶ Γ :=
  RawCtx.toCtx.map (projectionRaw Γ ht)

@[simp]
theorem snoc_projection {Γ₁ : CtxCat E ℓ} (Γ₂ : CtxCat E ℓ) {t : Expr ζ ℓ Γ₂.as.len} {u : Level ℓ}
    (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) {e : Expr ζ ℓ Γ₁.as.len}
    (he : E[Γ₁.as.ctx] ⊢ₛ e : t.subst σ.subst) :
    RawCtx.toCtx.map (σ.snoc ⟨u, ht⟩ he) ≫ rawProjection Γ₂ ht = RawCtx.toCtx.map σ := by
  change RawCtx.toCtx.map (σ.snoc ⟨u, ht⟩ he) ≫ RawCtx.toCtx.map (projectionRaw Γ₂ ht) =
    RawCtx.toCtx.map σ
  rw [← RawCtx.toCtx.map_comp]
  congr 1
  exact RawCtx.Hom.ext (funext fun v => Subst.extend_castSucc _ _ v)

theorem extension_hom_ext {Γ₁ Γ₂ : CtxCat E ℓ} {t : Expr ζ ℓ Γ₂.as.len} {u : Level ℓ}
    {ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u} {σ₁ σ₂ : Γ₁ ⟶ extension Γ₂ ht}
    (hover : σ₁ ≫ rawProjection Γ₂ ht = σ₂ ≫ rawProjection Γ₂ ht)
    (hgeneric : (Tm E ℓ).map σ₁.op (Tm.rawBinderVar Γ₂.as ht) =
      (Tm E ℓ).map σ₂.op (Tm.rawBinderVar Γ₂.as ht)) : σ₁ = σ₂ := by
  obtain ⟨σ₁, rfl⟩ := RawCtx.toCtx.map_surjective σ₁
  obtain ⟨σ₂, rfl⟩ := RawCtx.toCtx.map_surjective σ₂
  apply (RawCtx.toCtx_map_eq_iff _ _).mpr
  have htail : E[Γ₁.as.ctx] ⊢ₛ Subst.wk.comp σ₁.subst ≡ Subst.wk.comp σ₂.subst ⊣ Γ₂.as.ctx :=
    (RawCtx.toCtx_map_eq_iff (σ₁ ≫ projectionRaw Γ₂ ht)
      (σ₂ ≫ projectionRaw Γ₂ ht)).mp hover
  have h := (Tm.label_eq_iff.mp ((Tm.map_varLabel σ₁ _).symm.trans
    (hgeneric.trans (Tm.map_varLabel σ₂ _)))).2
  rw [Ctx.get_last, ← Expr.subst_wk, Expr.subst_subst] at h
  simpa using htail.extend h

theorem rawExtensionIsRepresented {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) :
    IsPullback (yonedaEquiv.symm (Tm.rawBinderVar Γ₁.as ht))
      (y (rawProjection Γ₁ ht)) (Tm.typing E ℓ)
      (yonedaEquiv.symm (Ty.ofTyping Γ₁.as ht)) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨Γ₂⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro σ
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    apply (Ty.ofRepr_eq_iff _ _).mpr
    change E[Γ₂.as.ctx] ⊢ₛ ((Γ₁.as.ctx.snoc t).get (Fin.last _)).subst σ.subst ≡
      t.subst (σ ≫ projectionRaw Γ₁ ht).subst typ
    rw [Ctx.get_last, ← Expr.subst_wk, Expr.subst_subst]
    exact (IsTypeStrong.substitution ⟨u, ht⟩ (σ ≫ projectionRaw Γ₁ ht).typed).isTypeEq
  · intro σ₁ σ₂ ⟨hgeneric, hover⟩
    exact extension_hom_ext hover hgeneric
  · intro a σ h
    obtain ⟨a⟩ := a
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    have hty : E[Γ₂.as.ctx] ⊢ₛ a.ty ≡ t.subst σ.subst typ := (Ty.ofRepr_eq_iff _ _).mp h
    have ha : E[Γ₂.as.ctx] ⊢ₛ a.val : t.subst σ.subst := hty.convStrong a.valWF
    refine ⟨RawCtx.toCtx.map (σ.snoc ⟨u, ht⟩ ha), ?_, snoc_projection Γ₁ ht σ ha⟩
    apply Quotient.sound
    change E[Γ₂.as.ctx] ⊢ₛ ((Γ₁.as.ctx.snoc t).get (Fin.last _)).subst (σ.subst.extend a.val) ≡
        a.ty typ ∧
      E[Γ₂.as.ctx] ⊢ₛ (σ.subst.extend a.val) (Fin.last _) ≡ a.val :
        ((Γ₁.as.ctx.snoc t).get (Fin.last _)).subst (σ.subst.extend a.val)
    rw [Ctx.get_last, Expr.wk_subst_extend, Subst.extend_last]
    exact ⟨hty.symm, ha⟩

end CtxCat

theorem Tm.typing_relativelyRepresentable :
    yoneda.relativelyRepresentable (Tm.typing E ℓ) := by
  intro Γ₁ A
  obtain ⟨T, hT⟩ := Ty.exists_ofRepr (yonedaEquiv A)
  obtain rfl : A = yonedaEquiv.symm (Ty.ofRepr T) := by
    rw [← hT, Equiv.symm_apply_apply]
  have ⟨_, ht⟩ := T.wf
  exact ⟨_, _, _, CtxCat.rawExtensionIsRepresented ht⟩

instance : NaturalModel (Ty E ℓ) (Tm E ℓ) where
  typing := Tm.typing E ℓ
  representable := Tm.typing_relativelyRepresentable

def Ty.Repr.comprehension (T : Ty.Repr Γ₁) :
    Comprehension (Ty E ℓ) Γ₁ ⟨Γ₁.as.snoc T.wf⟩ where
  type := yonedaEquiv.symm (Ty.ofRepr T)
  disp := RawCtx.toCtx.map ⟨Subst.wk, SubstWFStrong.wk T.term Γ₁.as.wf⟩
  generic := Tm.varLabel ⟨Γ₁.as.snoc T.wf⟩ (Fin.last Γ₁.as.len)
  isPullback := by
    have ⟨_, ht⟩ := T.wf
    exact CtxCat.rawExtensionIsRepresented ht

theorem Ty.comprehension_type_eq {A : y Γ₁ ⟶ Ty E ℓ} {T : Ty.Repr Γ₁}
    (hT : yonedaEquiv A = Ty.ofRepr T) : A = T.comprehension.type := by
  simp [Repr.comprehension, ← hT]

abbrev CtxCat.rawComprehension {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ} (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) :
    Comprehension (Ty E ℓ) Γ₁ (Γ₁.extension ht) :=
  (⟨t, u, ht⟩ : Ty.Repr Γ₁).comprehension

namespace Ty.Repr

def reindex (T : Repr Γ₁) (σ : Γ₂.as ⟶ Γ₁.as) : Repr Γ₂ :=
  ⟨T.term.subst σ.subst, T.wf.substitution σ.typed⟩

theorem ofRepr_reindex (T : Repr Γ₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    (Ty E ℓ).map (RawCtx.toCtx.map σ).op (ofRepr T) = ofRepr (T.reindex σ) :=
  rfl

theorem comprehension_type_reindex (T : Repr Γ₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    y (RawCtx.toCtx.map σ) ≫ T.comprehension.type = (T.reindex σ).comprehension.type :=
  yonedaEquiv_symm_naturality_left _ _ _

end Ty.Repr

theorem Tm.map_rawProjection_varLabel {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (v : Var Γ₁.as.len) :
    (Tm E ℓ).map (Γ₁.rawProjection ht).op (Tm.varLabel Γ₁ v) =
      Tm.varLabel (Γ₁.extension ht) v.castSucc := by
  refine Tm.label_congr ?_
  simp [CtxCat.projectionRaw, Expr.subst_wk]

theorem Tm.map_extension_varLabel {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₂ ⟶ Γ₁.extension ht) (v : Var Γ₁.as.len) :
    (Tm E ℓ).map σ.op (Tm.varLabel (Γ₁.extension ht) v.castSucc) =
      (Tm E ℓ).map (σ ≫ Γ₁.rawProjection ht).op (Tm.varLabel Γ₁ v) := by
  rw [← Tm.map_rawProjection_varLabel ht v, ← Functor.map_comp_apply, ← op_comp]

@[simp] theorem CtxCat.rawComprehension_type {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) :
    yonedaEquiv (CtxCat.rawComprehension ht).type = Ty.ofTyping Γ₁.as ht :=
  yonedaEquiv.apply_symm_apply _

theorem CtxCat.rawComprehension_generic {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) :
    (CtxCat.rawComprehension ht).generic = Tm.varLabel (Γ₁.extension ht) (Fin.last Γ₁.as.len) :=
  rfl

end Metalean
