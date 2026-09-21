/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Filter.Defs
public import Metalean.Semantics.Domain.Application
public import Metalean.Semantics.Interpretation.Family.Basic
import Mathlib.Order.Filter.Basic
import Metalean.Order.Presheaf.Finitary
import Metalean.Semantics.Domain.Action

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

section Application

open CategoryTheory MonoidalCategory Opposite Presheaf

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

noncomputable def stepApplication (label : Tm_ Γ₁) :
    Functor.HomObj ((order E ℓ) ⊗ (order E ℓ)) (ΩIdeal.presheaf (pointedOrder E ℓ))
      (uliftYoneda.{0}.obj Γ₁) where
  app _ f := Preord.ofHom {
    toFun p := application (principalIdeal p.1) ((Tm E ℓ).map f.down.op label)
      (principalIdeal p.2)
    monotone' _ _ h :=
      application_mono (ΩLower.principal_mono h.1) (ΩLower.principal_mono h.2) }
  naturality σ f := by
    ext ⟨u, x⟩
    change application (principalIdeal (reindex σ.unop u))
        ((Tm E ℓ).map (σ.unop ≫ f.down).op label)
        (principalIdeal (reindex σ.unop x)) =
      (application (principalIdeal u) ((Tm E ℓ).map f.down.op label)
        (principalIdeal x)).pullback σ.unop
    rw [pullback_application, ΩIdeal.presheaf_map_principal,
      ΩIdeal.presheaf_map_principal, op_comp, Functor.map_comp_apply]
    rfl

noncomputable abbrev stepApplicationRaw (label : Tm_ Γ₁) :=
  (stepApplication label).comp (.ofNatTrans (ΩIdeal.toLowerNatTrans (pointedOrder E ℓ)))

@[simp] theorem stepApplication_app (label : Tm_ Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (u x : CoherentShape Γ₂) :
    (stepApplication label).app (op Γ₂) ⟨σ⟩ (u, x) =
      application (principalIdeal u) ((Tm E ℓ).map σ.op label) (principalIdeal x) :=
  rfl

@[simp] theorem stepApplicationRaw_app (label : Tm_ Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (u x : CoherentShape Γ₂) :
    (stepApplicationRaw label).app (op Γ₂) ⟨σ⟩ (u, x) =
      (application (principalIdeal u) ((Tm E ℓ).map σ.op label)
        (principalIdeal x)).val :=
  rfl

theorem application_eq_bind₂ (I : Domain Γ₁) (label : Tm_ Γ₁) (X : Domain Γ₁) :
    application I label X = ΩIdeal.bind₂ I X (stepApplication label) := by
  ext Γ₂ σ y
  rw [ΩIdeal.mem_bind₂]
  constructor
  · intro ⟨x, hx, heval⟩
    have ⟨u, hu, heval'⟩ := Evaluates.function_ideal_finitary heval
    refine ⟨u, x, by simpa using hu, hx, ?_⟩
    exact ⟨x, by simp, by simpa using heval'⟩
  · intro ⟨u, x, hu, hx, hy⟩
    rw [stepApplication_app] at hy
    have ⟨x', hx', heval⟩ := hy
    refine ⟨x, hx, ?_⟩
    have hle : principalIdeal u ≤ I.pullback σ :=
      ΩLower.principal_le_iff.mpr (by simpa using hu)
    exact ((by simpa using heval : Evaluates (principalIdeal u)
      ((Tm E ℓ).map σ.op label) x' y).mono (by simpa using hx')).mono_ideal hle

noncomputable def rawApplication (F : RawValue Γ₁) (Q : Set (Tm_ Γ₁)) (X : RawValue Γ₁) :
    RawValue Γ₁ :=
  ⨆ label ∈ Q, ΩLower.bind₂ F X (stepApplicationRaw label)

theorem mem_rawApplication (F : RawValue Γ₁) (Q : Set (Tm_ Γ₁)) (X : RawValue Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (rawApplication F Q X).mem σ y ↔ y ≤ ⊥ ∨ ∃ label ∈ Q, ∃ u x, F.mem σ u ∧ X.mem σ x ∧
      (application (principalIdeal u) ((Tm E ℓ).map σ.op label)
        (principalIdeal x)).mem (𝟙 Γ₂) y := by
  simp only [rawApplication, ΩLower.mem_iSup, ΩLower.mem_bind₂]
  constructor
  · rintro (h | ⟨label, h | ⟨hlabel, h⟩⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr ⟨label, hlabel, h⟩
  · rintro (h | ⟨label, hlabel, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨label, Or.inr ⟨hlabel, h⟩⟩

theorem rawApplication_mono {F G X Y : RawValue Γ₁} {Q R : Set (Tm_ Γ₁)}
    (hFG : F ≤ G) (hQR : Q ⊆ R) (hXY : X ≤ Y) :
    rawApplication F Q X ≤ rawApplication G R Y := by
  intro Γ₂ σ y hy
  rw [mem_rawApplication] at hy ⊢
  rcases hy with hy | ⟨label, hlabel, u, x, hu, hx, hy⟩
  · exact Or.inl hy
  · exact Or.inr ⟨label, hQR hlabel, u, x, hFG σ u hu, hXY σ x hx, hy⟩

theorem pullback_rawApplication (F X : RawValue Γ₁)
    (Q : Set (Tm_ Γ₁)) (σ₁ : Γ₂ ⟶ Γ₁) :
    (rawApplication F Q X).pullback σ₁ =
      rawApplication (F.pullback σ₁) ((Tm E ℓ).map σ₁.op '' Q) (X.pullback σ₁) := by
  ext Γ₃ σ₂ y
  rw [ΩLower.presheaf_map_mem, mem_rawApplication, mem_rawApplication]
  simp

theorem rawApplication_singleton (F X : Domain Γ₁) (label : Tm_ Γ₁) :
    rawApplication F.val {label} X.val = (application F label X).val := by
  rw [rawApplication, iSup_singleton, application_eq_bind₂]
  rfl

theorem rawApplication_isDirected {F X : RawValue Γ₁} {Q : Set (Tm_ Γ₁)}
    (hQ : Q.Subsingleton) (hF : F.IsDirected) (hX : X.IsDirected) :
    (rawApplication F Q X).IsDirected := by
  rcases hQ.eq_empty_or_singleton with rfl | ⟨label, rfl⟩
  · rw [show rawApplication F ∅ X = ⊥ by simp [rawApplication]]
    exact ΩLower.isDirected_bot
  · rw [rawApplication_singleton ⟨F, hF⟩ ⟨X, hX⟩]
    exact (application ..).property

theorem rawApplication_eq_of_support (F X : Domain Γ₁)
    {Q : Set (Tm_ Γ₁)} (label : Tm_ Γ₁) (hlabel : label ∈ Q)
    (hsupport : ∀ {Γ₂} (σ : Γ₂ ⟶ Γ₁) (label' : Tm_ Γ₂),
      label' ∈ (Tm E ℓ).map σ.op '' Q →
      ∀ {x y : CoherentShape Γ₂}, OutputAtom (F.pullback σ).val label' x y →
        y ≤ ⊥ ∨ label' = (Tm E ℓ).map σ.op label) :
    rawApplication F.val Q X.val = (application F label X).val := by
  apply le_antisymm
  · intro Γ₂ σ y hy
    rcases (mem_rawApplication _ _ _ _ _).mp hy with hy | ⟨name, hname, u, x, hu, hx, hy⟩
    · exact (application F label X).lower σ hy ((application F label X).bottom σ)
    rw [mem_application] at hy
    have ⟨x', hx', heval⟩ := hy
    simp at heval
    have hle : principalIdeal u ≤ F.pullback σ :=
      ΩLower.principal_le_iff.mpr (by simpa using hu)
    have heval := (heval.mono_ideal hle).mono (show x' ≤ x by simpa using hx')
    by_cases hname' : (Tm E ℓ).map σ.op name = (Tm E ℓ).map σ.op label
    · exact ⟨x, hx, hname' ▸ heval⟩
    · refine (application F label X).lower σ ?_ ((application F label X).bottom σ)
      apply heval.le_of_outputAtom
      intro w hw
      rcases hsupport σ _ ⟨name, hname, rfl⟩ hw with hbottom | hlabel
      · exact hbottom
      · exact absurd hlabel hname'
  · intro Γ₂ σ y hy
    rw [ΩIdeal.val_mem, application_eq_bind₂, ΩIdeal.mem_bind₂] at hy
    have ⟨u, x, hu, hx, hy⟩ := hy
    rw [stepApplication_app] at hy
    rw [mem_rawApplication]
    exact Or.inr ⟨label, hlabel, u, x, hu, hx, hy⟩

theorem rawApplication_eventually {α : Type*} {l : Filter α}
    {F X : RawValue Γ₁} {Fs Xs : α → RawValue Γ₁} {Q : Set (Tm_ Γ₁)}
    (hF : ∀ {x}, F.mem (𝟙 Γ₁) x → ∀ᶠ a in l, (Fs a).mem (𝟙 Γ₁) x)
    (hX : ∀ {x}, X.mem (𝟙 Γ₁) x → ∀ᶠ a in l, (Xs a).mem (𝟙 Γ₁) x)
    {y : CoherentShape Γ₁} (hy : (rawApplication F Q X).mem (𝟙 Γ₁) y) :
    ∀ᶠ a in l, (rawApplication (Fs a) Q (Xs a)).mem (𝟙 Γ₁) y :=
  ΩLower.iSup_eventually (fun label => ΩLower.iSup_eventually
    fun _ => ΩLower.bind₂_eventually (stepApplicationRaw label) hF hX) hy

theorem rawApplication_iSup_le {Γ₂ : CtxCat E ℓ} {F X : Nat → RawValue Γ₂} (hF : Monotone F)
    (hX : Monotone X) (Q : Set (Tm_ Γ₂)) :
    rawApplication (⨆ n, F n) Q (⨆ n, X n) ≤ ⨆ n, rawApplication (F n) Q (X n) := by
  intro Γ₃ σ y hy
  rw [mem_rawApplication] at hy
  rcases hy with hy | ⟨label, hlabel, u, x, hu, hx, hy⟩
  · exact (ΩLower.mem_iSup ..).mpr (Or.inl hy)
  · have ⟨n₁, hu⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hu
    have ⟨n₂, hx⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hx
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨max n₁ n₂, ?_⟩
    rw [mem_rawApplication]
    exact Or.inr ⟨label, hlabel, u, x, hF (le_max_left n₁ n₂) σ u hu,
      hX (le_max_right n₁ n₂) σ x hx, hy⟩

theorem rawApplication_iSup_le_const {Γ₂ : CtxCat E ℓ} {F : Nat → RawValue Γ₂}
    (Q : Set (Tm_ Γ₂)) (X : RawValue Γ₂) :
    rawApplication (⨆ n, F n) Q X ≤ ⨆ n, rawApplication (F n) Q X := by
  intro Γ₃ σ y hy
  rw [mem_rawApplication] at hy
  rcases hy with hy | ⟨label, hlabel, u, x, hu, hx, hy⟩
  · exact (ΩLower.mem_iSup ..).mpr (Or.inl hy)
  · have ⟨n, hu⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hu
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, ?_⟩
    rw [mem_rawApplication]
    exact Or.inr ⟨label, hlabel, u, x, hu, hx, hy⟩

end Application

section Application

open CategoryTheory Presheaf

variable {Γ₁ Γ₂ : CtxCat E ℓ} {k : Nat}

noncomputable def rawApps (F : RawValue Γ₁) (names : Fin k → Tm_ Γ₁)
    (args : Fin k → RawValue Γ₁) : RawValue Γ₁ :=
  Fin.foldl k (fun G i => rawApplication G {names i} (args i)) F

@[simp] theorem rawApps_zero (F : RawValue Γ₁) (names : Fin 0 → Tm_ Γ₁)
    (args : Fin 0 → RawValue Γ₁) : rawApps F names args = F :=
  Fin.foldl_zero ..

theorem rawApps_last (F : RawValue Γ₁) (names : Fin (k + 1) → Tm_ Γ₁)
    (args : Fin (k + 1) → RawValue Γ₁) :
    rawApps F names args =
      rawApplication (rawApps F (fun i => names i.castSucc) fun i => args i.castSucc)
        {names (Fin.last k)} (args (Fin.last k)) :=
  Fin.foldl_succ_last ..

theorem rawApps_append {j : Nat} (F : RawValue Γ₁)
    (names : Fin k → Tm_ Γ₁) (names' : Fin j → Tm_ Γ₁)
    (args : Fin k → RawValue Γ₁) (args' : Fin j → RawValue Γ₁) :
    rawApps F (Fin.append names names') (Fin.append args args') =
      rawApps (rawApps F names args) names' args' := by
  simp [rawApps, Fin.foldl_add]

theorem rawApps_mono {F G : RawValue Γ₁} (hFG : F ≤ G) (names : Fin k → Tm_ Γ₁)
    {args args' : Fin k → RawValue Γ₁} (hargs : ∀ i, args i ≤ args' i) :
    rawApps F names args ≤ rawApps G names args' := by
  induction k with
  | zero => exact hFG
  | succ k ih =>
    rw [rawApps_last, rawApps_last]
    exact rawApplication_mono (ih _ fun i => hargs i.castSucc) subset_rfl (hargs (Fin.last k))

theorem pullback_rawApps (F : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) (names : Fin k → Tm_ Γ₁)
    (args : Fin k → RawValue Γ₁) :
    (rawApps F names args).pullback σ =
      rawApps (F.pullback σ) (fun i => (Tm E ℓ).map σ.op (names i))
        fun i => (args i).pullback σ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rawApps_last, rawApps_last, pullback_rawApplication, ih]
    congr 1
    exact Set.image_singleton

theorem exists_shapes_of_mem_rawApps (F : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (names : Fin k → Tm_ Γ₁) (args : Fin k → RawValue Γ₁) (y : CoherentShape Γ₂)
    (hy : (rawApps F names args).mem σ y) :
    ∃ xs : Fin k → CoherentShape Γ₂, (∀ i, (args i).mem σ (xs i)) ∧
      (rawApps (F.pullback σ) (fun i => (Tm E ℓ).map σ.op (names i))
        fun i => (principalIdeal (xs i)).val).mem (𝟙 Γ₂) y := by
  induction k generalizing y with
  | zero =>
    rw [rawApps_zero] at hy
    exact ⟨Fin.elim0, fun i => i.elim0, by rw [rawApps_zero]; simpa using hy⟩
  | succ k ih =>
    rw [rawApps_last, mem_rawApplication] at hy
    rcases hy with hy | ⟨label, rfl, u, x, hu, hx, hy⟩
    · exact ⟨fun _ => ⊥, fun i => (args i).bottom σ,
        ΩLower.lower _ (𝟙 Γ₂) hy (ΩLower.bottom _ (𝟙 Γ₂))⟩
    · have ⟨xs, hxs, hu⟩ := ih (fun i => names i.castSucc) (fun i => args i.castSucc) u hu
      refine ⟨Fin.snoc xs x, fun i => ?_, ?_⟩
      · cases i using Fin.lastCases with
        | last => rwa [Fin.snoc_last]
        | cast j => rw [Fin.snoc_castSucc]; exact hxs j
      · rw [rawApps_last, mem_rawApplication]
        refine Or.inr ⟨(Tm E ℓ).map σ.op (names (Fin.last k)), rfl, u, x, ?_, ?_, ?_⟩
        · simpa using hu
        · simp
        · simpa using hy

theorem rawApps_isDirected (F : Domain Γ₁) (names : Fin k → Tm_ Γ₁)
    (args : Fin k → Domain Γ₁) :
    (rawApps F.val names fun i => (args i).val).IsDirected := by
  induction k with
  | zero => exact F.property
  | succ k ih =>
    rw [rawApps_last]
    exact rawApplication_isDirected Set.subsingleton_singleton (ih _ _) (args _).property

theorem rawApps_eventually {α : Type*} {l : Filter α} {F : RawValue Γ₁} {Fs : α → RawValue Γ₁}
    (hF : ∀ {x}, F.mem (𝟙 Γ₁) x → ∀ᶠ a in l, (Fs a).mem (𝟙 Γ₁) x)
    (names : Fin k → Tm_ Γ₁) {args : Fin k → RawValue Γ₁}
    {argss : α → Fin k → RawValue Γ₁}
    (hargs : ∀ i {x}, (args i).mem (𝟙 Γ₁) x → ∀ᶠ a in l, (argss a i).mem (𝟙 Γ₁) x)
    {y : CoherentShape Γ₁} (hy : (rawApps F names args).mem (𝟙 Γ₁) y) :
    ∀ᶠ a in l, (rawApps (Fs a) names (argss a)).mem (𝟙 Γ₁) y := by
  induction k generalizing y with
  | zero =>
    rw [rawApps_zero] at hy
    exact Filter.Eventually.mono (hF hy) fun _ ha => by rwa [rawApps_zero]
  | succ k ih =>
    rw [rawApps_last] at hy
    exact Filter.Eventually.mono (rawApplication_eventually
      (ih (fun i => names i.castSucc) fun i => hargs i.castSucc)
      (hargs (Fin.last k)) hy) fun _ ha => by rwa [rawApps_last]

theorem rawApps_iSup_le {F : Nat → RawValue Γ₁} (hF : Monotone F)
    (names : Fin k → Tm_ Γ₁) {args : Nat → Fin k → RawValue Γ₁}
    (hargs : ∀ i, Monotone fun n => args n i) :
    rawApps (⨆ n, F n) names (fun i => ⨆ n, args n i) ≤ ⨆ n, rawApps (F n) names (args n) := by
  induction k with
  | zero =>
    intro Γ₂ σ y hy
    rw [rawApps_zero] at hy
    have ⟨n, hy⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, ?_⟩
    rwa [rawApps_zero]
  | succ k ih =>
    intro Γ₂ σ y hy
    rw [rawApps_last] at hy
    have hy₁ := rawApplication_mono
      (ih (fun i => names i.castSucc) fun i => hargs i.castSucc) subset_rfl
      (fun _ _ hz => hz) σ y hy
    have hy₂ := rawApplication_iSup_le
      (fun a b hab => rawApps_mono (hF hab) _ fun i => hargs i.castSucc hab)
      (hargs (Fin.last k)) {names (Fin.last k)} σ y hy₁
    have ⟨n, hy₂⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy₂
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, ?_⟩
    rwa [rawApps_last]

theorem rawApps_iSup_le_const {F : Nat → RawValue Γ₁} (names : Fin k → Tm_ Γ₁)
    (args : Fin k → RawValue Γ₁) :
    rawApps (⨆ n, F n) names args ≤ ⨆ n, rawApps (F n) names args := by
  induction k with
  | zero =>
    intro Γ₂ σ y hy
    rw [rawApps_zero] at hy
    have ⟨n, hy⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, ?_⟩
    rwa [rawApps_zero]
  | succ k ih =>
    intro Γ₂ σ y hy
    rw [rawApps_last] at hy
    have hy₁ := rawApplication_mono
      (ih (fun i => names i.castSucc) fun i => args i.castSucc) subset_rfl
      (fun _ _ hz => hz) σ y hy
    have hy₂ := rawApplication_iSup_le_const
      {names (Fin.last k)} (args (Fin.last k)) σ y hy₁
    have ⟨n, hy₂⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy₂
    refine (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, ?_⟩
    rwa [rawApps_last]

end Application

namespace RawFamily

open CategoryTheory Presheaf

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

def sourceQuery (Γ₁ : CtxCat E ℓ) (e : Expr ζ ℓ Γ₁.as.len) : Set (Tm_ Γ₁) :=
  {label | ∃ (t : Expr ζ ℓ Γ₁.as.len) (he : E[Γ₁.as.ctx] ⊢ₛ e : t), Tm.label Γ₁.as he = label}

theorem label_mem_sourceQuery {t e : Expr ζ ℓ Γ₁.as.len} (he : E[Γ₁.as.ctx] ⊢ₛ e : t) :
    Tm.label Γ₁.as he ∈ sourceQuery Γ₁ e :=
  ⟨t, he, rfl⟩

noncomputable def application (F X : RawFamily Γ₁) (Q : Set (Tm_ Γ₁)) : RawFamily Γ₁ where
  app _ σ := Preord.ofHom {
    toFun ρ := rawApplication (F.app _ σ ρ)
      ((Tm E ℓ).map σ '' Q) (X.app _ σ ρ)
    monotone' _ _ hρ := rawApplication_mono ((F.app _ σ).hom.monotone hρ) (Set.Subset.refl _) ((X.app _ σ).hom.monotone hρ) }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change rawApplication (F.app _ (σ₁ ≫ σ₂) (ρ.pullback σ₂.unop))
      ((Tm E ℓ).map (σ₁ ≫ σ₂) '' Q) (X.app _ (σ₁ ≫ σ₂) (ρ.pullback σ₂.unop)) =
      (rawApplication (F.app _ σ₁ ρ)
      ((Tm E ℓ).map σ₁ '' Q) (X.app _ σ₁ ρ)).pullback σ₂.unop
    symm
    refine (pullback_rawApplication (F.app _ σ₁ ρ) (X.app _ σ₁ ρ) _ σ₂.unop).trans ?_
    rw [← ΩLower.presheaf_map_eq_pullback, ← ΩLower.presheaf_map_eq_pullback,
      ← F.naturality_apply, ← X.naturality_apply]
    simp [Set.image_image]
    rfl

@[simp]
theorem application_value (F X : RawFamily Γ₁) (Q : Set (Tm_ Γ₁))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (application F X Q).app _ σ.op ρ = rawApplication (F.app _ σ.op ρ)
      ((Tm E ℓ).map σ.op '' Q) (X.app _ σ.op ρ) := rfl

noncomputable def apps {k : Nat} (F : RawFamily Γ₁) (args : Fin k → RawFamily Γ₁)
    (queries : Fin k → Set (Tm_ Γ₁)) : RawFamily Γ₁ :=
  Fin.foldl k (fun G i => application G (args i) (queries i)) F

@[simp] theorem apps_zero (F : RawFamily Γ₁) (args : Fin 0 → RawFamily Γ₁)
    (queries : Fin 0 → Set (Tm_ Γ₁)) : F.apps args queries = F :=
  Fin.foldl_zero ..

theorem apps_last {k : Nat} (F : RawFamily Γ₁) (args : Fin (k + 1) → RawFamily Γ₁)
    (queries : Fin (k + 1) → Set (Tm_ Γ₁)) :
    F.apps args queries =
      application (F.apps (fun i => args i.castSucc) fun i => queries i.castSucc)
        (args (Fin.last k)) (queries (Fin.last k)) :=
  Fin.foldl_succ_last ..

theorem apps_named_value {k : Nat} (F : RawFamily Γ₁) (args : Fin k → RawFamily Γ₁)
    (names : Fin k → Tm_ Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (F.apps args fun p => {names p}).app _ σ.op ρ =
      rawApps (F.app _ σ.op ρ) (fun p => (Tm E ℓ).map σ.op (names p))
        fun p => (args p).app _ σ.op ρ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [apps_last, rawApps_last, application_value, ih, Set.image_singleton]

theorem IsFinitary.application {F X : RawFamily Γ₁}
    (hF : F.IsFinitary) (hX : X.IsFinitary) (Q : Set (Tm_ Γ₁)) :
    (application F X Q).IsFinitary := by
  intro Γ₂ σ i ρ
  exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
    rawApplication_eventually (hF.eventually σ i ρ I) (hX.eventually σ i ρ I) hy

theorem IsFinitary.apps {k : Nat} {F : RawFamily Γ₁} {args : Fin k → RawFamily Γ₁}
    (hF : F.IsFinitary) (hargs : ∀ i, (args i).IsFinitary)
    (queries : Fin k → Set (Tm_ Γ₁)) : (F.apps args queries).IsFinitary := by
  induction k with
  | zero => rwa [apps_zero]
  | succ k ih =>
    rw [apps_last]
    exact IsFinitary.application (ih (fun j => hargs j.castSucc) fun j => queries j.castSucc)
      (hargs (Fin.last k)) (queries (Fin.last k))

end RawFamily

end Metalean.CoherentShape
