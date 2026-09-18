/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Decoder.Extension
public import Metalean.Semantics.Domain.Quotient.Basic
public import Metalean.Semantics.Interpretation.Family.Application
public import Metalean.Semantics.Interpretation.Family.Basic
import Mathlib.Order.Filter.Basic
import Metalean.Strong
import Metalean.Strong.Quot

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

section QuotElimination

inductive QuotEvaluates (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawValue Γ₁) : CoherentShape Γ₁ → Prop where
  | bottom {y : CoherentShape Γ₁} :
    y ≤ ⊥ →
    QuotEvaluates D η A F Q y
  | mk (name : Tm_ Γ₁) (x : CoherentShape Γ₁) {y : CoherentShape Γ₁} :
    Q.mem (𝟙 Γ₁) (quotMkAtom η name x) →
    (rawApplication F {name}
      (D.rawExtend A name (ΩLower.principal (pointedOrder E ℓ) x))).mem (𝟙 Γ₁) y →
    QuotEvaluates D η A F Q y

namespace QuotEvaluates

variable {D : CodeAssignment E ℓ} {η : Head ζ .quot} {A A' F F' Q Q' : RawValue Γ₁}
  {y z : CoherentShape Γ₁}

theorem mono (hA : A ≤ A') (hF : F ≤ F') (hQ : Q ≤ Q')
    (h : QuotEvaluates D η A F Q y) : QuotEvaluates D η A' F' Q' y := by
  cases h with
  | bottom h => exact .bottom h
  | mk name x hq hy =>
    exact .mk name x (hQ _ _ hq)
      (rawApplication_mono hF (Set.Subset.refl _) (D.rawExtend_mono hA (@le_rfl _ _ _)) _ _ hy)

theorem lower (hyz : y ≤ z) (h : QuotEvaluates D η A F Q z) : QuotEvaluates D η A F Q y := by
  cases h with
  | bottom h => exact .bottom (hyz.trans h)
  | mk name x hq hz => exact .mk name x hq ((rawApplication ..).lower _ hyz hz)

theorem reindex (σ : Γ₂ ⟶ Γ₁) (h : QuotEvaluates D η A F Q y) :
    QuotEvaluates D η (A.pullback σ) (F.pullback σ) (Q.pullback σ) (CoherentShape.reindex σ y) := by
  cases h with
  | bottom h => exact .bottom (Le.reindex σ h)
  | mk name x hq hy =>
    refine .mk ((Tm E ℓ).map σ.op name) (CoherentShape.reindex σ x) ?_ ?_
    · simpa using Q.natural (𝟙 Γ₁) σ _ hq
    · have hy := (rawApplication ..).natural (𝟙 Γ₁) σ _ hy
      have heq := pullback_rawApplication F
        (D.rawExtend A name (ΩLower.principal (pointedOrder E ℓ) x)) {name} σ
      rw [D.pullback_rawExtend, ΩLower.presheaf_map_principal, pointedOrder_map, Set.image_singleton] at heq
      simp only [Quiver.Hom.unop_op] at heq
      rw [← heq]
      simpa using hy

theorem upper (hA : A.IsDirected) (hF : F.IsDirected) (hQ : Q.IsDirected)
    (hy : QuotEvaluates D η A F Q y) (hz : QuotEvaluates D η A F Q z) :
    ∃ w, QuotEvaluates D η A F Q w ∧ y ≤ w ∧ z ≤ w := by
  cases hy with
  | bottom hy => exact ⟨z, hz, hy.trans bot_le, le_rfl⟩
  | mk name x hx hy =>
    cases hz with
    | bottom hz => exact ⟨y, .mk name x hx hy, le_rfl, hz.trans bot_le⟩
    | mk name' x' hx' hz =>
      have ⟨q, hq, hxq, hx'q⟩ := hQ (𝟙 Γ₁) hx hx'
      have ⟨w, hqw, hxw⟩ := quotMkAtom_upper hxq
      subst q
      have ⟨_, hn, hx'w⟩ := quotMkAtom_le_iff.mp hx'q
      subst name'
      let W := D.rawExtend A name (ΩLower.principal (pointedOrder E ℓ) w)
      have hW : W.IsDirected := D.rawExtend_isDirected name hA (principalIdeal w).property
      have hdir : (rawApplication F {name} W).IsDirected := by
        rw [rawApplication_singleton ⟨F, hF⟩ ⟨W, hW⟩ name]
        exact (application ..).property
      have hy : (rawApplication F {name} W).mem (𝟙 Γ₁) y :=
        rawApplication_mono (fun _ _ h => h) (Set.Subset.refl {name})
          (D.rawExtend_mono_right name (ΩLower.principal_mono hxw)) _ _ hy
      have hz : (rawApplication F {name} W).mem (𝟙 Γ₁) z :=
        rawApplication_mono (fun _ _ h => h) (Set.Subset.refl {name})
          (D.rawExtend_mono_right name (ΩLower.principal_mono hx'w)) _ _ hz
      have ⟨v, hv, hyv, hzv⟩ := hdir (𝟙 Γ₁) hy hz
      exact ⟨v, .mk name w hq hv, hyv, hzv⟩

end QuotEvaluates

noncomputable def rawQuotLift (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := QuotEvaluates D η (A.pullback σ) (F.pullback σ) (Q.pullback σ) y
  natural σ₁ σ₂ y := fun h => by simpa using h.reindex σ₂
  bottom σ := .bottom le_rfl
  lower σ hyz := fun h => h.lower hyz

@[simp] theorem mem_rawQuotLift (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (rawQuotLift D η A F Q).mem σ y ↔
      QuotEvaluates D η (A.pullback σ) (F.pullback σ) (Q.pullback σ) y := Iff.rfl

@[simp] theorem pullback_rawQuotLift (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (rawQuotLift D η A F Q).pullback σ₁ =
      rawQuotLift D η (A.pullback σ₁) (F.pullback σ₁) (Q.pullback σ₁) := by
  ext Γ₃ σ₂ y
  simp [ΩLower.pullback]

theorem rawQuotLift_isDirected (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    {A F Q : RawValue Γ₁} (hA : A.IsDirected) (hF : F.IsDirected) (hQ : Q.IsDirected) :
    (rawQuotLift D η A F Q).IsDirected :=
  fun σ _ _ hy hz => hy.upper (hA.pullback σ) (hF.pullback σ) (hQ.pullback σ) hz

theorem rawQuotLift_quotMk (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F X : Domain Γ₁) (name : Tm_ Γ₁) :
    rawQuotLift D η A.val F.val (RawValue.quotMk η name X.val) =
      rawApplication F.val {name} (D.rawExtend A.val name X.val) := by
  ext Γ₂ σ y
  have heq := pullback_rawApplication F.val (D.rawExtend A.val name X.val) {name} σ
  rw [D.pullback_rawExtend, Set.image_singleton] at heq
  have heq := congrArg (fun V : RawValue Γ₂ => V.mem (𝟙 Γ₂) y) heq
  simp only [ΩLower.pullback, Category.id_comp] at heq
  rw [heq]
  simp only [mem_rawQuotLift, RawValue.pullback_quotMk]
  constructor
  · intro h
    cases h with
    | bottom h => exact (rawApplication ..).lower _ h ((rawApplication ..).bottom _)
    | mk name' x hq hy =>
      have ⟨z, hz, hxz⟩ := hq
      simp at hxz
      have ⟨_, hn, hvalue⟩ := quotMkAtom_le_iff.mp hxz
      subst name'
      exact rawApplication_mono
        (fun _ _ h => h) (Set.Subset.refl _)
        (D.rawExtend_mono_right _ (ΩLower.principal_le_iff.mpr
          ((X.val.pullback σ).lower _ hvalue hz))) _ _ hy
  · intro hy
    change (rawApplication (F.pullback σ).val {(Tm E ℓ).map σ.op name}
      (D.rawExtend (A.pullback σ).val ((Tm E ℓ).map σ.op name)
        (X.pullback σ).val)).mem (𝟙 Γ₂) y at hy
    have hfin := (application_argument_finitary (F.pullback σ)
      ((Tm E ℓ).map σ.op name)).comp
        (D.extend_finitary_right (A.pullback σ) ((Tm E ℓ).map σ.op name))
        fun _ _ h => application_mono (@le_rfl _ _ _) h
    rw [D.rawExtend_toLower (A.pullback σ) ((Tm E ℓ).map σ.op name) (X.pullback σ),
      rawApplication_singleton (F.pullback σ)
        (D.extend (A.pullback σ) ((Tm E ℓ).map σ.op name) (X.pullback σ))] at hy
    have ⟨x, hx, hy⟩ := hfin (X.pullback σ) hy
    refine .mk ((Tm E ℓ).map σ.op name) x ⟨x, hx, by simp⟩ ?_
    change (rawApplication (F.pullback σ).val {(Tm E ℓ).map σ.op name}
      (D.rawExtend (A.pullback σ).val ((Tm E ℓ).map σ.op name)
        (principalIdeal x).val)).mem (𝟙 Γ₂) y
    rwa [D.rawExtend_toLower (A.pullback σ) ((Tm E ℓ).map σ.op name) (principalIdeal x),
      rawApplication_singleton (F.pullback σ)
        (D.extend (A.pullback σ) ((Tm E ℓ).map σ.op name) (principalIdeal x))]

end QuotElimination

section ProofElimination

noncomputable def rawProofApplication (C : Ty_ Γ₁) (F : RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := (rawApplication (F.pullback σ) {n | Tm.type n = (Ty E ℓ).map σ.op C} ⊥).mem (𝟙 _) y
  natural σ₁ σ₂ y := fun h => by
    have h := (rawApplication (F.pullback σ₁) {n | Tm.type n = (Ty E ℓ).map σ₁.op C} ⊥).natural
      (𝟙 _) σ₂ y h
    rw [Category.comp_id, ← ΩLower.presheaf_map_mem_id, pullback_rawApplication,
      ΩLower.pullback_pullback, ΩLower.presheaf_map_bot] at h
    refine rawApplication_mono (fun _ _ h => h) ?_ (fun _ _ h => h) _ _ h
    rintro _ ⟨n, hn, rfl⟩
    change Tm.type ((Tm E ℓ).map σ₂.op n) = _
    rw [Tm.type_map, hn, ← Functor.map_comp_apply, ← op_comp]
  bottom _ := ΩLower.bottom _ _
  lower _ hyz := ΩLower.lower _ _ hyz

@[simp] theorem mem_rawProofApplication (C : Ty_ Γ₁) (F : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (y : CoherentShape Γ₂) :
    (rawProofApplication C F).mem σ y ↔
      (rawApplication (F.pullback σ) {n | Tm.type n = (Ty E ℓ).map σ.op C} ⊥).mem (𝟙 Γ₂) y := Iff.rfl

@[simp] theorem pullback_rawProofApplication (C : Ty_ Γ₁) (F : RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (rawProofApplication C F).pullback σ₁ =
      rawProofApplication ((Ty E ℓ).map σ₁.op C) (F.pullback σ₁) := by
  ext Γ₃ σ₂ y
  simp only [ΩLower.presheaf_map_mem, mem_rawProofApplication, ΩLower.pullback_pullback,
    ← Functor.map_comp_apply, ← op_comp]

end ProofElimination

section QuotFamily

variable {η : Head ζ .quot} {u : Level ℓ} {α α' r r' : Expr ζ ℓ Γ₁.as.len}

structure QuotTyping (Γ : CtxCat E ℓ) (u : Level ℓ) (α r : Expr ζ ℓ Γ.as.len) : Prop where
  carrier : E[Γ.as.ctx] ⊢ₛ α : .sort u
  relation : E[Γ.as.ctx] ⊢ₛ r : Quot.relType α

namespace QuotTyping

variable (Γ₁) in
theorem ofTyping {t : Expr ζ ℓ Γ₁.as.len} (h : E[Γ₁.as.ctx] ⊢ₛ .quot η u α r : t) :
    QuotTyping Γ₁ u α r :=
  have ⟨hα, hr⟩ := h.quot_formation_inv (Or.inl rfl)
  ⟨hα, hr⟩

theorem ofLift {v : Level ℓ} {β f h a t : Expr ζ ℓ Γ₁.as.len}
    (hlift : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a : t) :
    QuotTyping Γ₁ u α r :=
  have ⟨_, _, _, _, _, _, hα, hr, _⟩ := hlift.quotLift_prem (Or.inl rfl)
  ⟨hα.right, .defeqDF (Quot.relType_congr hα) hr.right⟩

noncomputable def code (h : QuotTyping Γ₁ u α r) (η : Head ζ .quot) : QuotCode Γ₁ :=
  ⟨η, u, Tm.label Γ₁.as h.carrier, Tm.label Γ₁.as h.relation⟩

theorem left (hα : E[Γ₁.as.ctx] ⊢ₛ α ≡ α' : .sort u)
    (hr : E[Γ₁.as.ctx] ⊢ₛ r ≡ r' : Quot.relType α) : QuotTyping Γ₁ u α r :=
  ⟨hα.left, hr.left⟩

theorem right (hα : E[Γ₁.as.ctx] ⊢ₛ α ≡ α' : .sort u)
    (hr : E[Γ₁.as.ctx] ⊢ₛ r ≡ r' : Quot.relType α) : QuotTyping Γ₁ u α' r' :=
  ⟨hα.right, .defeqDF (Quot.relType_congr hα) hr.right⟩

theorem subst (h : QuotTyping Γ₁ u α r) (σ : Γ₂.as ⟶ Γ₁.as) :
    QuotTyping Γ₂ u (α.subst σ.subst) (r.subst σ.subst) where
  carrier := h.carrier.substitution σ.typed
  relation := by simpa using h.relation.substitution σ.typed

theorem code_map (h : QuotTyping Γ₁ u α r) (η : Head ζ .quot) (σ : Γ₂.as ⟶ Γ₁.as) :
    (h.code η).map ((Tm E ℓ).map (RawCtx.toCtx.map σ).op) = (h.subst σ).code η := by
  simp only [code, QuotCode.map, Tm.map_label]
  congr 1
  exact Tm.label_congr (by simp)

theorem code_congr (hα : E[Γ₁.as.ctx] ⊢ₛ α ≡ α' : .sort u)
    (hr : E[Γ₁.as.ctx] ⊢ₛ r ≡ r' : Quot.relType α)
    (h : QuotTyping Γ₁ u α r) (h' : QuotTyping Γ₁ u α' r') (η : Head ζ .quot) :
    h.code η = h'.code η := by
  unfold code
  congr 1
  · exact Tm.label_eq (.ofDefEq .sortDF) hα
  · exact Tm.label_eq (.ofDefEq (Quot.relType_congr hα)) hr

end QuotTyping

namespace RawFamily

noncomputable def quot (code : QuotCode Γ₁) : RawFamily Γ₁ :=
  constant (principalIdeal (quotAtom code)).val

@[simp] theorem quot_value (code : QuotCode Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (quot code).app _ σ.op ρ =
      (principalIdeal (quotAtom (code.map ((Tm E ℓ).map σ.op)))).val :=
  ΩLower.presheaf_map_principal (R := pointedOrder E ℓ) (quotAtom code) σ

theorem quot_isFinitary (code : QuotCode Γ₁) : (quot code).IsFinitary := constant_isFinitary _

noncomputable def quotMk (η : Head ζ .quot) (name : Tm_ Γ₁)
    (F : RawFamily Γ₁) : RawFamily Γ₁ where
  app X σ := Preord.ofHom {
    toFun ρ := RawValue.quotMk η ((Tm E ℓ).map σ.unop.op name) (F.app X σ ρ)
    monotone' _ _ h := RawValue.quotMk_mono _ _ ((F.app X σ).hom.monotone h) }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change RawValue.quotMk _ _ _ = (RawValue.quotMk _ _ _).pullback σ₂.unop
    rw [RawValue.pullback_quotMk]
    congr 1
    · simp
    · exact (F.app_pullback σ₁ σ₂.unop ρ).symm

theorem IsFinitary.quotMk (η : Head ζ .quot) (name : Tm_ Γ₁)
    {F : RawFamily Γ₁} (hF : F.IsFinitary) : (quotMk η name F).IsFinitary := by
  intro Γ₂ σ i ρ
  refine ΩLower.IsFinitary.of_eventually fun I y hy => ?_
  have ⟨x, hx, hy⟩ := hy
  exact (hF.eventually σ i ρ I hx).mono fun J hJ => ⟨x, hJ, hy⟩

noncomputable def quotLift (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawFamily Γ₁) : RawFamily Γ₁ where
  app X σ := Preord.ofHom {
    toFun ρ := rawQuotLift D η (A.app X σ ρ) (F.app X σ ρ) (Q.app X σ ρ)
    monotone' _ _ h _ σ₂ _ hy := hy.mono
      (ΩLower.pullback_mono ((A.app X σ).hom.monotone h) σ₂)
      (ΩLower.pullback_mono ((F.app X σ).hom.monotone h) σ₂)
      (ΩLower.pullback_mono ((Q.app X σ).hom.monotone h) σ₂) }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change rawQuotLift _ _ _ _ _ = (rawQuotLift _ _ _ _ _).pullback σ₂.unop
    rw [pullback_rawQuotLift, A.app_pullback, F.app_pullback, Q.app_pullback]
    rfl

@[simp] theorem quotLift_value (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    (A F Q : RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (quotLift D η A F Q).app _ σ.op ρ =
      rawQuotLift D η (A.app _ σ.op ρ) (F.app _ σ.op ρ) (Q.app _ σ.op ρ) := rfl

theorem IsFinitary.quotLift (D : CodeAssignment E ℓ) (η : Head ζ .quot)
    {A F Q : RawFamily Γ₁} (hA : A.IsFinitary) (hF : F.IsFinitary) (hQ : Q.IsFinitary) :
    (quotLift D η A F Q).IsFinitary := by
  intro Γ₂ σ i ρ
  refine ΩLower.IsFinitary.of_eventually fun I _ hy => ?_
  simp only [quotLift_value, mem_rawQuotLift, ΩLower.pullback_id] at hy ⊢
  cases hy with
  | bottom hy => exact Filter.Eventually.of_forall fun _ => .bottom hy
  | mk name x hq hy =>
    have happ := rawApplication_eventually (hF.eventually σ i ρ I)
      (D.rawExtend_eventually name (hA.eventually σ i ρ I)
        fun hx => Filter.Eventually.of_forall fun _ => hx) hy
    exact ((hQ.eventually σ i ρ I hq).and happ).mono fun _ ⟨hq, hy⟩ => .mk name x hq hy

noncomputable def proofApplication (C : Ty_ Γ₁) (F : RawFamily Γ₁) : RawFamily Γ₁ where
  app X σ := Preord.ofHom {
    toFun ρ := rawProofApplication ((Ty E ℓ).map σ C) (F.app X σ ρ)
    monotone' _ _ h _ σ₂ _ hy := rawApplication_mono
      (ΩLower.pullback_mono ((F.app X σ).hom.monotone h) σ₂) (Set.Subset.refl _)
      (fun _ _ h => h) _ _ hy }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change rawProofApplication _ _ = (rawProofApplication _ _).pullback σ₂.unop
    rw [pullback_rawProofApplication, F.app_pullback, ← Functor.map_comp_apply]
    rfl

@[simp] theorem proofApplication_value (C : Ty_ Γ₁) (F : RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (ρ : RawValuation Γ₂) :
    (proofApplication C F).app _ σ.op ρ =
      rawProofApplication ((Ty E ℓ).map σ.op C) (F.app _ σ.op ρ) := rfl

theorem proofApplication_isDirected {C : Ty_ Γ₁}
    (hC : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁),
      {n : Tm_ Γ₂ | Tm.type n = (Ty E ℓ).map σ.op C}.Subsingleton)
    (F : RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hF : (F.app _ σ.op ρ).IsDirected) :
    (rawProofApplication ((Ty E ℓ).map σ.op C) (F.app _ σ.op ρ)).IsDirected := by
  intro Γ₃ σ₂
  refine rawApplication_isDirected ?_ (hF.pullback σ₂) ΩLower.isDirected_bot (𝟙 _)
  rw [← Functor.map_comp_apply, ← op_comp]
  exact hC (σ₂ ≫ σ)

theorem proofApplication_eq {C : Ty_ Γ₁}
    (hC : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁),
      {n : Tm_ Γ₂ | Tm.type n = (Ty E ℓ).map σ.op C}.Subsingleton)
    (F : RawFamily Γ₁) (name : Tm_ Γ₁) (hname : Tm.type name = C)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (proofApplication C F).app _ σ.op ρ =
      rawApplication (F.app _ σ.op ρ) {(Tm E ℓ).map σ.op name} ⊥ := by
  change rawProofApplication ((Ty E ℓ).map σ.op C) (F.app _ σ.op ρ) = _
  ext Γ₃ σ₂ y
  have hQ : {n : Tm_ Γ₃ | Tm.type n = (Ty E ℓ).map σ₂.op ((Ty E ℓ).map σ.op C)} =
      {(Tm E ℓ).map σ₂.op ((Tm E ℓ).map σ.op name)} := by
    rw [← Functor.map_comp_apply, ← op_comp]
    refine (hC (σ₂ ≫ σ)).eq_singleton_of_mem ?_
    change Tm.type ((Tm E ℓ).map σ₂.op ((Tm E ℓ).map σ.op name)) = _
    rw [Tm.type_map, Tm.type_map, hname, ← Functor.map_comp_apply, ← op_comp]
  rw [mem_rawProofApplication,
    ← ΩLower.presheaf_map_mem_id (rawApplication (F.app _ σ.op ρ) {(Tm E ℓ).map σ.op name} ⊥),
    pullback_rawApplication, Set.image_singleton, ΩLower.presheaf_map_bot, hQ]

theorem IsFinitary.proofApplication (C : Ty_ Γ₁) {F : RawFamily Γ₁} (hF : F.IsFinitary) :
    (proofApplication C F).IsFinitary := by
  intro Γ₂ σ i ρ
  refine ΩLower.IsFinitary.of_eventually fun I _ hy => ?_
  simp only [proofApplication_value, mem_rawProofApplication, ΩLower.pullback_id] at hy ⊢
  exact rawApplication_eventually (hF.eventually σ i ρ I)
    (fun hx => Filter.Eventually.of_forall fun _ => hx) hy

end RawFamily

end QuotFamily

end Metalean.CoherentShape
