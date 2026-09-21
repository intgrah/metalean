/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Filter.Defs
public import Metalean.Semantics.Domain.Action
import Metalean.Order.Presheaf.Finitary

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

section CodeExtension

open CategoryTheory MonoidalCategory Presheaf

abbrev CodeAssignment (E : Env ζ) (ℓ : Nat) := order E ℓ ⟶ IdealAction.presheaf E ℓ

namespace CodeAssignment

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

@[simp] theorem app_reindex (F : CodeAssignment E ℓ) (a : CoherentShape Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    F.app _ (reindex σ a) = IdealAction.pullback (F.app _ a) σ :=
  ConcreteCategory.congr_hom (F.naturality σ.op) a

noncomputable def eval (F : CodeAssignment E ℓ) (a : CoherentShape Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) : Domain Γ₁ :=
  (F.app _ a).val.app _ ((𝟙 Γ₁).op, n) X

theorem pullback_eval (F : CodeAssignment E ℓ) (a : CoherentShape Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (F.eval a n X).pullback σ =
      F.eval (reindex σ a) ((Tm E ℓ).map σ.op n) (X.pullback σ) := by
  rw [eval, eval, F.app_reindex, IdealAction.pullback_app]
  simpa using (IdealAction.app_pullback (F.app _ a) (𝟙 Γ₁).op σ n X).symm

theorem eval_mono_code (F : CodeAssignment E ℓ) {a b : CoherentShape Γ₁} (h : a ≤ b)
    (n : Tm_ Γ₁) (X : Domain Γ₁) : F.eval a n X ≤ F.eval b n X :=
  (F.app _).hom.monotone h _ ((𝟙 Γ₁).op, n) X

theorem eval_mono_payload (F : CodeAssignment E ℓ) (a : CoherentShape Γ₁)
    (n : Tm_ Γ₁) {X Y : Domain Γ₁} (h : X ≤ Y) : F.eval a n X ≤ F.eval a n Y :=
  ((F.app _ a).val.app _ ((𝟙 Γ₁).op, n)).hom.monotone h

noncomputable def evalStep (F : CodeAssignment E ℓ) (n : Tm_ Γ₁) :
    Functor.HomObj ((order E ℓ) ⊗ (order E ℓ)) (ΩIdeal.presheaf (pointedOrder E ℓ))
      (uliftYoneda.{0}.obj Γ₁) where
  app _ f := Preord.ofHom {
    toFun := fun (c, x) => F.eval c ((Tm E ℓ).map f.down.op n) (principalIdeal x)
    monotone' := fun _ _ ⟨hc, hx⟩ => fun g a ha =>
      F.eval_mono_payload _ _ (ΩLower.principal_mono hx) g a
        (F.eval_mono_code hc _ _ g a ha) }
  naturality σ f := by
    ext ⟨c, x⟩
    change F.eval (reindex σ.unop c) ((Tm E ℓ).map (σ.unop ≫ f.down).op n)
        (principalIdeal (reindex σ.unop x)) =
      (F.eval c ((Tm E ℓ).map f.down.op n) (principalIdeal x)).pullback σ.unop
    rw [F.pullback_eval, ΩIdeal.presheaf_map_principal, op_comp, Functor.map_comp_apply]
    rfl

noncomputable def rawExtend (F : CodeAssignment E ℓ) (T : RawValue Γ₁)
    (n : Tm_ Γ₁) (X : RawValue Γ₁) : RawValue Γ₁ :=
  ΩLower.bind₂ T X ((F.evalStep n).comp (.ofNatTrans (ΩIdeal.toLowerNatTrans (pointedOrder E ℓ))))

theorem rawExtend_isDirected (F : CodeAssignment E ℓ) {T X : RawValue Γ₁}
    (n : Tm_ Γ₁) (hT : T.IsDirected) (hX : X.IsDirected) :
    (F.rawExtend T n X).IsDirected :=
  ΩLower.IsDirected.bind₂ hT hX _ fun _ _ p => ((F.evalStep n).app _ _ p).property

noncomputable def extend (F : CodeAssignment E ℓ) (T : Domain Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) : Domain Γ₁ :=
  ⟨F.rawExtend T.val n X.val, F.rawExtend_isDirected n T.property X.property⟩

theorem rawExtend_toLower (F : CodeAssignment E ℓ) (T : Domain Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) :
    F.rawExtend T.val n X.val = (F.extend T n X).val :=
  rfl

@[simp] theorem mem_rawExtend (F : CodeAssignment E ℓ) (T : RawValue Γ₁)
    (n : Tm_ Γ₁) (X : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (F.rawExtend T n X).mem σ y ↔
      ∃ c, T.mem σ c ∧ ∃ x, X.mem σ x ∧
        (F.eval c ((Tm E ℓ).map σ.op n) (principalIdeal x)).mem (𝟙 Γ₂) y := by
  rw [rawExtend, ΩLower.mem_bind₂]
  exact ⟨fun ⟨c, x, hc, hx, hy⟩ => ⟨c, hc, x, hx, hy⟩, fun ⟨c, hc, x, hx, hy⟩ => ⟨c, x, hc, hx, hy⟩⟩

@[simp] theorem mem_extend (F : CodeAssignment E ℓ)
    (T : Domain Γ₂) (n : Tm_ Γ₂) (X : Domain Γ₂)
    (σ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (F.extend T n X).mem σ y ↔ ∃ a, T.mem σ a ∧
      (F.eval a ((Tm E ℓ).map σ.op n) (X.pullback σ)).mem (𝟙 Γ₁) y := by
  rw [← ΩIdeal.val_mem, ← rawExtend_toLower, mem_rawExtend]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    refine ⟨c, hc, F.eval_mono_payload c _ ?_ (𝟙 Γ₁) y hy⟩
    apply ΩLower.principal_le_iff.mpr
    exact (ΩIdeal.presheaf_map_mem_id X σ x).mpr hx
  · intro ⟨c, hc, hy⟩
    have ⟨x, hx, hy⟩ := (F.app _ c).property _ ((𝟙 Γ₁).op, (Tm E ℓ).map σ.op n)
      (X.pullback σ) hy
    exact ⟨c, hc, x, (ΩIdeal.presheaf_map_mem_id X σ x).mp hx, hy⟩

theorem rawExtend_mono (F : CodeAssignment E ℓ) {T T' X X' : RawValue Γ₁} {n : Tm_ Γ₁}
    (hT : T ≤ T') (hX : X ≤ X') : F.rawExtend T n X ≤ F.rawExtend T' n X' :=
  ΩLower.bind₂_mono hT hX _

theorem rawExtend_mono_right (F : CodeAssignment E ℓ) {T : RawValue Γ₁}
    (n : Tm_ Γ₁) {X X' : RawValue Γ₁} (h : X ≤ X') :
    F.rawExtend T n X ≤ F.rawExtend T n X' :=
  F.rawExtend_mono (@le_rfl _ _ _) h

theorem extend_mono (F : CodeAssignment E ℓ) {T T' X X' : Domain Γ₁} {n : Tm_ Γ₁}
    (hT : T ≤ T') (hX : X ≤ X') : F.extend T n X ≤ F.extend T' n X' :=
  F.rawExtend_mono hT hX

theorem pullback_rawExtend (F : CodeAssignment E ℓ) (T : RawValue Γ₁)
    (n : Tm_ Γ₁) (X : RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (F.rawExtend T n X).pullback σ₁ =
      F.rawExtend (T.pullback σ₁) ((Tm E ℓ).map σ₁.op n) (X.pullback σ₁) := by
  ext Γ₃ σ₂ y
  simp [← Functor.map_comp_apply, ← op_comp]

theorem pullback_extend (F : CodeAssignment E ℓ) (T : Domain Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (F.extend T n X).pullback σ =
      F.extend (T.pullback σ) ((Tm E ℓ).map σ.op n) (X.pullback σ) :=
  Subtype.val_injective (F.pullback_rawExtend T.val n X.val σ)

noncomputable def rawExtendHom (F : CodeAssignment E ℓ) :
    Functor.HomObj (ΩLower.presheaf (pointedOrder E ℓ) ⊗ ΩLower.presheaf (pointedOrder E ℓ))
      (ΩLower.presheaf (pointedOrder E ℓ)) (Tm E ℓ) where
  app _ n := Preord.ofHom {
    toFun := fun (T, X) => F.rawExtend T n X
    monotone' := fun _ _ ⟨hT, hX⟩ => ΩLower.bind₂_mono hT hX _ }
  naturality σ n := Preord.ext fun (T, X) => (F.pullback_rawExtend T n X σ.unop).symm

theorem rawExtend_eventually (F : CodeAssignment E ℓ) {α : Type*} {l : Filter α}
    {T X : RawValue Γ₁} {Ts Xs : α → RawValue Γ₁} (n : Tm_ Γ₁)
    (hT : ∀ {x}, T.mem (𝟙 Γ₁) x → ∀ᶠ a in l, (Ts a).mem (𝟙 Γ₁) x)
    (hX : ∀ {x}, X.mem (𝟙 Γ₁) x → ∀ᶠ a in l, (Xs a).mem (𝟙 Γ₁) x)
    {y : CoherentShape Γ₁} (hy : (F.rawExtend T n X).mem (𝟙 Γ₁) y) :
    ∀ᶠ a in l, (F.rawExtend (Ts a) n (Xs a)).mem (𝟙 Γ₁) y :=
  ΩLower.bind₂_eventually _ hT hX hy

theorem extend_principal (F : CodeAssignment E ℓ) (a : CoherentShape Γ₁)
    (n : Tm_ Γ₁) (X : Domain Γ₁) :
    F.extend (principalIdeal a) n X = F.eval a n X := by
  ext Γ₂ σ y
  rw [mem_extend]
  constructor
  · intro ⟨c, hc, hy⟩
    have hy := F.eval_mono_code ((principalIdeal_mem a σ c).mp hc) _ _ (𝟙 Γ₂) y hy
    rw [← F.pullback_eval] at hy
    exact (ΩIdeal.presheaf_map_mem_id _ σ y).mp hy
  · intro hy
    refine ⟨reindex σ a, (principalIdeal_mem a σ _).mpr le_rfl, ?_⟩
    rw [← F.pullback_eval]
    exact (ΩIdeal.presheaf_map_mem_id _ σ y).mpr hy

theorem eval_le_extend (F : CodeAssignment E ℓ) {T : Domain Γ₁}
    {a : CoherentShape Γ₁} (ha : T.mem (𝟙 Γ₁) a)
    (n : Tm_ Γ₁) (X : Domain Γ₁) : F.eval a n X ≤ F.extend T n X :=
  (F.extend_principal a n X).symm.le.trans (F.extend_mono (ΩLower.principal_le_iff.mpr ha) (@le_rfl _ _ _))

theorem rawExtend_eq_map (F : CodeAssignment E ℓ) {T X : RawValue Γ₁} {n : Tm_ Γ₁}
    (G : Functor.HomObj (order E ℓ) (order E ℓ) (uliftYoneda.{0}.obj Γ₁))
    (hT : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (c : CoherentShape Γ₂), T.mem σ c →
      ∃ d, T.mem σ d ∧ c ≤ d ∧ ∀ x,
        F.eval d ((Tm E ℓ).map σ.op n) (principalIdeal x) = principalIdeal (G.app _ ⟨σ⟩ x)) :
    F.rawExtend T n X = X.map G := by
  ext Γ₂ σ y
  rw [mem_rawExtend]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    have ⟨d, _, hcd, hd⟩ := hT σ c hc
    have hy := F.eval_mono_code hcd _ (principalIdeal x) (𝟙 Γ₂) y hy
    rw [hd] at hy
    exact ⟨x, hx, by simpa using hy⟩
  · intro ⟨x, hx, hy⟩
    have ⟨d, hd, _, hdx⟩ := hT σ ⊥ (T.bottom σ)
    exact ⟨d, hd, x, hx, by rw [hdx]; simpa using hy⟩

theorem extend_finitary_left (F : CodeAssignment E ℓ) (n : Tm_ Γ₁) (X : Domain Γ₁) :
    ΩIdeal.IsFinitary fun T => F.extend T n X := by
  intro T y hy
  have ⟨a, ha, hy⟩ := (mem_extend _ _ _ _ _ _).mp hy
  exact ⟨a, ha, (mem_extend _ _ _ _ _ _).mpr ⟨a, by simp, hy⟩⟩

theorem extend_finitary_right (F : CodeAssignment E ℓ) (T : Domain Γ₁)
    (n : Tm_ Γ₁) : ΩIdeal.IsFinitary (F.extend T n) := by
  intro X y hy
  have ⟨a, ha, x, hx, hy⟩ := (mem_rawExtend F T.val n X.val (𝟙 Γ₁) y).mp hy
  exact ⟨x, hx, (mem_rawExtend _ _ _ _ _ _).mpr ⟨a, ha, x, by simp, hy⟩⟩

def IsIdempotent (F : CodeAssignment E ℓ) : Prop :=
  ∀ ⦃Γ₁ : CtxCat E ℓ⦄ (a : CoherentShape Γ₁), IdealAction.IsIdempotent (F.app _ a)

theorem eval_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (a : CoherentShape Γ₁) (n : Tm_ Γ₁) (X : Domain Γ₁) :
    F.eval a n (F.eval a n X) = F.eval a n X :=
  hF a (𝟙 Γ₁) n X

theorem extend_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (T : Domain Γ₁) (n : Tm_ Γ₁) (X : Domain Γ₁) :
    F.extend T n (F.extend T n X) = F.extend T n X := by
  apply le_antisymm
  · intro Γ₂ σ y
    simp_rw [mem_extend]
    intro ⟨a, ha, hy⟩
    have ⟨x, hx, hy⟩ := (F.app _ a).property _ ((𝟙 Γ₂).op, (Tm E ℓ).map σ.op n)
      ((F.extend T n X).pullback σ) hy
    rw [ΩIdeal.presheaf_map_mem_id] at hx
    have ⟨b, hb, hx⟩ := (mem_extend _ _ _ _ _ _).mp hx
    have ⟨c, hc, hac, hbc⟩ := T.property σ ha hb
    have hxc := F.eval_mono_code hbc _ (X.pullback σ) (𝟙 Γ₂) x hx
    have hyc := F.eval_mono_code hac _ (principalIdeal x) (𝟙 Γ₂) y hy
    have hyc' := F.eval_mono_payload c _ (ΩLower.principal_le_iff.mpr hxc) (𝟙 Γ₂) y hyc
    rw [F.eval_idempotent hF] at hyc'
    exact ⟨c, hc, hyc'⟩
  · intro Γ₂ σ y
    simp_rw [mem_extend]
    intro ⟨a, ha, hy⟩
    have ha' : (T.pullback σ).mem (𝟙 Γ₂) a :=
      (ΩIdeal.presheaf_map_mem_id T σ a).mpr ha
    have hy' : (F.eval a ((Tm E ℓ).map σ.op n)
        (F.eval a ((Tm E ℓ).map σ.op n) (X.pullback σ))).mem (𝟙 Γ₂) y := by
      rw [F.eval_idempotent hF]
      exact hy
    refine ⟨a, ha, ?_⟩
    rw [F.pullback_extend]
    exact F.eval_mono_payload a _
      (F.eval_le_extend ha' ((Tm E ℓ).map σ.op n) (X.pullback σ)) (𝟙 Γ₂) y hy'

theorem rawExtend_idempotent (F : CodeAssignment E ℓ) (hF : F.IsIdempotent)
    {T X : RawValue Γ₁} (n : Tm_ Γ₁) (hT : T.IsDirected) (hX : X.IsDirected) :
    F.rawExtend T n (F.rawExtend T n X) = F.rawExtend T n X :=
  congrArg Subtype.val (F.extend_idempotent hF ⟨T, hT⟩ n ⟨X, hX⟩)

noncomputable def bottom (E : Env ζ) (ℓ : Nat) : CodeAssignment E ℓ where
  app _ := Preord.ofHom (OrderHom.const _ IdealAction.bottom)
  naturality _ _ _ := rfl

theorem bottom_isIdempotent : (bottom E ℓ).IsIdempotent :=
  fun _ _ _ _ _ _ => rfl

end CodeAssignment

end CodeExtension

end Metalean.CoherentShape
