/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Context.Substitution
import Metalean.Semantics.Interpretation.Binder.Ideality
public import Metalean.Typing.WeakenEnv
import Metalean.Typing.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory CoherentShape CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ n m : Nat}
  {Γ : Ctx ζ₂ ℓ 0 n} {Δ : Ctx ζ₂ ℓ n m} {A : Expr ζ₂ ℓ m}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {e e₁ e₂ e₃ t t₁ t₂ : Expr ζ₂ ℓ Γ₁.as.len}

namespace CoherentShape

def HasFixedness (Γ₁ : CtxCat E₂ ℓ) (e t : Expr ζ₂ ℓ Γ₁.as.len) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E₂ ℓ⦄ (he : E₂[Γ₁.as.ctx] ⊢ e : t) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂),
    SourceAdmissible σ ρ →
      (piLimit E₂ ℓ).rawExtend ((rawInterpret (piLimit E₂ ℓ) Γ₁ t).app _ σ.op ρ)
        ((Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as he))
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ.op ρ) =
        (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ.op ρ

def HasEquality (Γ₁ : CtxCat E₂ ℓ) (e₁ e₂ : Expr ζ₂ ℓ Γ₁.as.len) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E₂ ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂),
    SourceAdmissible σ ρ →
      (rawInterpret (piLimit E₂ ℓ) Γ₁ e₁).app _ σ.op ρ = (rawInterpret (piLimit E₂ ℓ) Γ₁ e₂).app _ σ.op ρ

structure RawInterpretationProperties (Γ₁ : CtxCat E₂ ℓ) (e : Expr ζ₂ ℓ Γ₁.as.len) : Prop where
  ideal : HasIdeality Γ₁ e
  subst : HasSubstitution Γ₁ e

def RawTeleProperties (E₂ : Env ζ₂) (Γ : Ctx ζ₂ ℓ 0 n) (Δ : Ctx ζ₂ ℓ n m) : Prop :=
  Δ.Forall fun Δ' A =>
    ∀ wf : E₂[Γ ++ Δ'] ⊢ ok, RawInterpretationProperties ⟨Γ ++ Δ', wf⟩ A

namespace RawTeleProperties

theorem extension {Δ : Ctx ζ₂ ℓ 0 m} (h : RawTeleProperties E₂ .nil Δ) (wf : E₂[Δ] ⊢ ok)
    (pt : RawInterpretationProperties ⟨Δ, wf⟩ A) : RawTeleProperties E₂ .nil (Δ.snoc A) :=
  .snoc h fun wf' => by
    revert wf'
    rw [Tele.nil_append]
    exact fun _ => pt

theorem append {a b c : Nat} {Γ : Ctx ζ₂ ℓ 0 a}
    {Δ : Ctx ζ₂ ℓ a b} {Θ : Ctx ζ₂ ℓ b c}
    (hΔ : RawTeleProperties E₂ Γ Δ) (hΘ : RawTeleProperties E₂ (Γ ++ Δ) Θ) :
    RawTeleProperties E₂ Γ (Δ ++ Θ) := by
  induction hΘ with
  | nil => exact hΔ
  | snoc _ hA ih =>
    exact .snoc ih (by rwa [Tele.append_assoc] at hA)

theorem of_append {a b c : Nat} {Γ : Ctx ζ₂ ℓ 0 a}
    {Δ : Ctx ζ₂ ℓ a b} {Θ : Ctx ζ₂ ℓ b c}
    (h : RawTeleProperties E₂ Γ (Δ ++ Θ)) :
    RawTeleProperties E₂ Γ Δ ∧ RawTeleProperties E₂ (Γ ++ Δ) Θ := by
  induction Θ with
  | nil => exact ⟨h, .nil⟩
  | snoc Θ A ih =>
    have ⟨pΔ, pΘ⟩ := ih h.init
    refine ⟨pΔ, .snoc pΘ ?_⟩
    rw [Tele.append_assoc]
    exact h.last

end RawTeleProperties

structure RawJudgment (Γ₁ : CtxCat E₂ ℓ) (e₁ e₂ t : Expr ζ₂ ℓ Γ₁.as.len) : Prop where
  syntactic : E₂[Γ₁.as.ctx] ⊢ e₁ ≡ e₂ : t
  type : RawInterpretationProperties Γ₁ t
  left : RawInterpretationProperties Γ₁ e₁
  right : RawInterpretationProperties Γ₁ e₂
  equal : HasEquality Γ₁ e₁ e₂
  fixed : HasFixedness Γ₁ e₁ t

structure RawTyped (Γ₁ : CtxCat E₂ ℓ) (e t : Expr ζ₂ ℓ Γ₁.as.len) : Prop where
  typed : E₂[Γ₁.as.ctx] ⊢ e : t
  type : RawInterpretationProperties Γ₁ t
  term : RawInterpretationProperties Γ₁ e
  fixed : HasFixedness Γ₁ e t

theorem RawJudgment.toRawTyped {e₁ e₂ t : Expr ζ₂ ℓ Γ₁.as.len} (p : RawJudgment Γ₁ e₁ e₂ t) :
    RawTyped Γ₁ e₁ t :=
  ⟨p.syntactic.left, p.type, p.left, p.fixed⟩

theorem RawFamily.bodyAction_isIdealValued {t : Expr ζ₂ ℓ Γ₁.as.len}
    {u : Level ℓ} (ht : E₂[Γ₁.as.ctx] ⊢ t : .sort u) (pt : HasIdeality Γ₁ t)
    {B : RawFamily (Γ₁.extension ht)}
    (hB : ∀ ⦃Γ₃ : CtxCat E₂ ℓ⦄ (σ : Γ₃ ⟶ Γ₁.extension ht) (ρ : RawValuation Γ₃),
      SourceAdmissible σ ρ → (B.app _ σ.op ρ).IsDirected)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (RawFamily.normalizedBodyAction (piLimit E₂ ℓ) (CtxCat.rawComprehension ht)
      (rawInterpret (piLimit E₂ ℓ) Γ₁ t) B σ ρ).IsIdealValued :=
  RawFamily.normalizedBodyAction_isIdealValued (CtxCat.rawComprehension ht) _ _ σ ρ (pt σ ρ hρ)
    fun σ₂ _ s J hJ =>
      hB s.hom _ ((hρ.pullback σ₂).push ht s (pt _ _ (hρ.pullback σ₂)) J.property hJ)

theorem HasSubstitution.instantiate {C : Expr ζ₂ ℓ (Γ₁.as.len + 1)} {u : Level ℓ}
    (ht : E₂[Γ₁.as.ctx] ⊢ t : .sort u) (he : E₂[Γ₁.as.ctx] ⊢ e : t)
    (htI : HasIdeality Γ₁ t) (heI : HasIdeality Γ₁ e) (heF : HasFixedness Γ₁ e t)
    (heS : HasSubstitution Γ₁ e) (hC : HasSubstitution (CtxCat.extension Γ₁ ht) C)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) (CtxCat.extension Γ₁ ht) C).app _ (σ ≫ (Raw.ContextSection.ofTerm ht he).hom).op
        (ρ.push ((rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ.op ρ)) =
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (C.inst e)).app _ σ.op ρ :=
  have hsource := hρ.push ht ((Raw.ContextSection.ofTerm ht he).pullbackId σ)
    (htI σ ρ hρ) (heI σ ρ hρ) (heF he σ ρ hρ)
  have he' : E₂[Γ₁.as.ctx] ⊢ e : t.subst (RawCtx.Hom.subst (𝟙 Γ₁.as)) := by
    rwa [RawCtx.Hom.id_subst, Expr.subst_id]
  (hC (RawCtx.Hom.snoc (𝟙 Γ₁.as) ⟨u, ht⟩ he') σ _ ρ
    (SemanticSubstitution.snoc ht (𝟙 _) he' heS σ ρ ρ hρ (.id σ ρ)) hsource).symm

namespace HasEquality

theorem refl (Γ₁ : CtxCat E₂ ℓ) (e : Expr ζ₂ ℓ Γ₁.as.len) : HasEquality Γ₁ e e := fun _ _ _ _ ↦ rfl

theorem symm (h : HasEquality Γ₁ e₁ e₂) : HasEquality Γ₁ e₂ e₁ :=
  fun _ σ ρ hρ ↦ (h σ ρ hρ).symm

theorem trans (h₁ : HasEquality Γ₁ e₁ e₂) (h₂ : HasEquality Γ₁ e₂ e₃) :
    HasEquality Γ₁ e₁ e₃ := fun _ σ ρ hρ ↦ (h₁ σ ρ hρ).trans (h₂ σ ρ hρ)

theorem eval (h : HasEquality Γ₁ e₁ e₂) {σ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ ρ) (he₁ : HasIdeality Γ₁ e₁) (he₂ : HasIdeality Γ₁ e₂) :
    hρ.eval he₁ = hρ.eval he₂ := Subtype.val_injective (h σ ρ hρ)

theorem fixed_right (h : HasEquality Γ₁ e₁ e₂) (he : E₂[Γ₁.as.ctx] ⊢ e₁ ≡ e₂ : t)
    (hf : HasFixedness Γ₁ e₁ t) : HasFixedness Γ₁ e₂ t := by
  intro Γ₂ he₂ σ ρ hρ
  rw [← h σ ρ hρ,
    ← Tm.label_eq (IsType.isTypeEq he.regular) he]
  exact hf he.left σ ρ hρ

end HasEquality

namespace HasFixedness

theorem convert (h : HasFixedness Γ₁ e t₁) (ht : E₂[Γ₁.as.ctx] ⊢ t₁ ≡ t₂ typ)
    (hteq : HasEquality Γ₁ t₁ t₂) : HasFixedness Γ₁ e t₂ := by
  intro Γ₂ he σ ρ hρ
  have he₁ : E₂[Γ₁.as.ctx] ⊢ e : t₁ := ht.symm.conv he
  rw [← hteq σ ρ hρ, ← Tm.label_eq ht he₁]
  exact h he₁ σ ρ hρ

end HasFixedness

namespace RawJudgment

theorem fixed_right (h : RawJudgment Γ₁ e₁ e₂ t) : HasFixedness Γ₁ e₂ t :=
  HasEquality.fixed_right h.equal h.syntactic h.fixed

theorem symm (h : RawJudgment Γ₁ e₁ e₂ t) : RawJudgment Γ₁ e₂ e₁ t :=
  ⟨h.syntactic.symm, h.type, h.right, h.left, HasEquality.symm h.equal, h.fixed_right⟩

theorem trans :
    RawJudgment Γ₁ e₁ e₂ t →
    RawJudgment Γ₁ e₂ e₃ t →
    RawJudgment Γ₁ e₁ e₃ t :=
  fun h₁ h₂ ↦ ⟨h₁.syntactic.trans h₂.syntactic, h₁.type, h₁.left, h₂.right,
    HasEquality.trans h₁.equal h₂.equal, h₁.fixed⟩

theorem convert {u : Level ℓ} :
    RawJudgment Γ₁ t₁ t₂ (.sort u) →
    RawJudgment Γ₁ e₁ e₂ t₁ →
    RawJudgment Γ₁ e₁ e₂ t₂ :=
  fun h he ↦ ⟨.defeqDF h.syntactic he.syntactic, h.right, he.left, he.right, he.equal,
    HasFixedness.convert he.fixed (.ofDefEq h.syntactic) h.equal⟩

end RawJudgment

end CoherentShape

def RawSound (E₂ : Env ζ₂) (ℓ : Nat) (pre : E₁.as ⟶ E₂.as) : Prop :=
  ∀ {n : Nat} {Δ₁ : Ctx ζ₁ ℓ 0 n} {e₁ e₂ t : Expr ζ₁ ℓ n},
  E₁[Δ₁] ⊢ e₁ ≡ e₂ : t →
  ∀ (hΔ₂ : E₂[Δ₁.map pre.sigs] ⊢ ok), RawTeleProperties E₂ .nil (Δ₁.map pre.sigs) →
  RawJudgment ⟨Δ₁.map pre.sigs, hΔ₂⟩ (e₁.map pre.sigs) (e₂.map pre.sigs) (t.map pre.sigs)

theorem RawSound.properties (hsound : RawSound E₂ ℓ pre)
    {Δ₁ : Ctx ζ₁ ℓ 0 n} (hΔ₁ : E₁[Δ₁] ⊢ ok)
    {e₁ e₂ t : Expr ζ₁ ℓ n} (d : E₁[Δ₁] ⊢ e₁ ≡ e₂ : t) :
    RawJudgment ⟨Δ₁.map pre.sigs, CtxWF.envMono pre hΔ₁⟩
      (e₁.map pre.sigs) (e₂.map pre.sigs) (t.map pre.sigs) := by
  refine hsound d _ ?_
  clear d e₁ e₂ t
  induction hΔ₁ with
  | nil => exact .nil
  | @snoc _ Δ₁ t hΔ₁ ht ih =>
    have ⟨_, ht⟩ := ht
    refine .snoc ih ?_
    rw [Tele.nil_append]
    exact fun wf => (hsound ht wf ih).left

end Metalean
