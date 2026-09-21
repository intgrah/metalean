/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Recovery
public import Metalean.Semantics.Interpretation.Inductive
public import Metalean.Semantics.Interpretation.Recursor.Section
import Mathlib.Order.Filter.Finite

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}
  {ι : IndSig} {η : Head ζ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}

noncomputable def recoveredField (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (indices : Fin (ι.nindices s) → RawValue Γ₁) :
    Fin (CtorHead.mk η s c).arity → RawValue Γ₁ :=
  Fin.append (fun f =>
    if Level.rel ((((E.get η).block.ctors s c).ordinary f).level.inst ls) then
      match ((E.get η).block.ctors s c).recoveryIndex f with
      | some i => indices i
      | none => ⊥
    else ⊥) fun _ => ⊥

def RecoveryNames (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level ℓ)
    (indices : Fin (ι.nindices s) → Tm_ Γ₁)
    (names : Fin (CtorHead.mk η s c).arity → Tm_ Γ₁) : Prop :=
  ∀ f : Fin (ι.ctors s c).nfields,
    Level.rel ((((E.get η).block.ctors s c).ordinary f).level.inst ls) = true →
    ∃ i, ((E.get η).block.ctors s c).recoveryIndex f = some i ∧
      names (Fin.castAdd (ι.ctors s c).nrecFields f) = indices i

theorem RecoveryNames.map {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {indices : Fin (ι.nindices s) → Tm_ Γ₁}
    {names : Fin (CtorHead.mk η s c).arity → Tm_ Γ₁}
    (h : RecoveryNames η s c ls indices names) (σ : Γ₂ ⟶ Γ₁) :
    RecoveryNames η s c ls (fun i => (Tm E ℓ).map σ.op (indices i))
      fun f => (Tm E ℓ).map σ.op (names f) := by
  intro f hf
  have ⟨i, hi, hn⟩ := h f hf
  exact ⟨i, hi, congrArg ((Tm E ℓ).map σ.op) hn⟩

theorem recoveredField_mono {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {indices indices' : Fin (ι.nindices s) → RawValue Γ₁}
    (h : ∀ i, indices i ≤ indices' i) (f : Fin (CtorHead.mk η s c).arity) :
    recoveredField η s c ls indices f ≤ recoveredField η s c ls indices' f := by
  cases f using Fin.addCases with
  | left f =>
    simp only [recoveredField, Fin.append_left]
    split
    · split
      · exact h _
      · exact fun _ _ h => h
    · exact fun _ _ h => h
  | right f => simp [recoveredField]

theorem pullback_recoveredField (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (indices : Fin (ι.nindices s) → RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (f : Fin (CtorHead.mk η s c).arity) :
    (recoveredField η s c ls indices f).pullback σ =
      recoveredField η s c ls (fun i => (indices i).pullback σ) f := by
  cases f using Fin.addCases with
  | left f =>
    simp only [recoveredField, Fin.append_left]
    split
    · split <;> rfl
    · rfl
  | right f => simp [recoveredField]

noncomputable def proofConstructor (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (σ₁ : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawValue Γ₂) : RawValue Γ₂ where
  mem σ₂ y := y ≤ ⊥ ∨ ∃ (c : Fin (ι.nctors s))
    (sect : CtorSection h s c (σ₂ ≫ σ₁)),
    RecoveryNames η s c ls (fun i => (Tm E ℓ).map σ₂.op (indexNames i)) sect.names ∧
      (RawValue.ctor ⟨η, s, c⟩ sect.names
        (recoveredField η s c ls fun i => (indices i).pullback σ₂)).mem (𝟙 _) y
  natural σ₂ σ₃ y := by
    rintro (hy | ⟨c, sect, hn, hy⟩)
    · exact Or.inl (Le.reindex σ₃ hy)
    · refine Or.inr ⟨c, (sect.pullback σ₃).congr (Category.assoc σ₃ σ₂ σ₁).symm, ?_, ?_⟩
      · simpa using hn.map σ₃
      · have hy' := (RawValue.ctor ⟨η, s, c⟩ sect.names
          (recoveredField η s c ls fun i => (indices i).pullback σ₂)).natural (𝟙 _) σ₃ y hy
        rw [← ΩLower.presheaf_map_mem_id, RawValue.pullback_ctor] at hy'
        simpa [pullback_recoveredField] using hy'
  bottom _ := Or.inl bot_le
  lower σ₂ hyz := by
    rintro (hz | ⟨c, sect, hn, hz⟩)
    · exact Or.inl (hyz.trans hz)
    · exact Or.inr ⟨c, sect, hn, ΩLower.lower _ _ hyz hz⟩

theorem proofConstructor_mono (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (σ₁ : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    {indices indices' : Fin (ι.nindices s) → RawValue Γ₂} (hi : ∀ i, indices i ≤ indices' i) :
    proofConstructor h s σ₁ indexNames indices ≤ proofConstructor h s σ₁ indexNames indices' := by
  rintro Γ₃ σ₂ y (hy | ⟨c, sect, hn, hy⟩)
  · exact Or.inl hy
  · exact Or.inr ⟨c, sect, hn, RawValue.ctor_mono _ _
      (recoveredField_mono fun i => ΩLower.pullback_mono (hi i) σ₂) _ _ hy⟩

theorem pullback_proofConstructor (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (σ₁ : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawValue Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) :
    (proofConstructor h s σ₁ indexNames indices).pullback σ₂ =
      proofConstructor h s (σ₂ ≫ σ₁) (fun i => (Tm E ℓ).map σ₂.op (indexNames i))
        fun i => (indices i).pullback σ₂ := by
  ext Γ₄ g y
  change (proofConstructor h s σ₁ indexNames indices).mem (g ≫ σ₂) y ↔ _
  simp only [proofConstructor]
  rw [Category.assoc]
  simp

noncomputable def recoverMajor (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (source : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawFamily Γ₂) (major : RawFamily Γ₂) : RawFamily Γ₂ :=
  if Level.rel ((E.get η).block.level.inst ls) then major else {
    app _ σ := Preord.ofHom {
      toFun ρ := proofConstructor h s (σ.unop ≫ source)
        (fun i => (Tm E ℓ).map σ (indexNames i)) fun i => (indices i).app _ σ ρ
      monotone' _ _ hρ := proofConstructor_mono h s _ _
        fun i => ((indices i).app _ σ).hom.monotone hρ }
    naturality σ₂ σ₁ := Preord.ext fun ρ => by
      change proofConstructor h s ((σ₂.unop ≫ σ₁.unop) ≫ source)
        (fun i => (Tm E ℓ).map (σ₁ ≫ σ₂) (indexNames i))
        (fun i => (indices i).app _ (σ₁ ≫ σ₂) (ρ.pullback σ₂.unop)) =
        (proofConstructor h s (σ₁.unop ≫ source)
          (fun i => (Tm E ℓ).map σ₁ (indexNames i))
          fun i => (indices i).app _ σ₁ ρ).pullback σ₂.unop
      simp only [pullback_proofConstructor, Category.assoc, Functor.map_comp_apply]
      congr 1
      funext i
      exact ((indices i).app_pullback σ₁ σ₂.unop ρ).symm }

private theorem recoveredField_eventually {α : Type*} {L : Filter α} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {indices : Fin (ι.nindices s) → RawValue Γ₁}
    {values : α → Fin (ι.nindices s) → RawValue Γ₁}
    (hv : ∀ i {x}, (indices i).mem (𝟙 Γ₁) x → ∀ᶠ a in L, (values a i).mem (𝟙 Γ₁) x)
    (f : Fin (CtorHead.mk η s c).arity) {x : CoherentShape Γ₁}
    (hx : (recoveredField η s c ls indices f).mem (𝟙 Γ₁) x) :
    ∀ᶠ a in L, (recoveredField η s c ls (values a) f).mem (𝟙 Γ₁) x := by
  cases f using Fin.addCases with
  | left f =>
    simp only [recoveredField, Fin.append_left] at hx ⊢
    split at hx
    · rename_i hrel
      cases he : ((E.get η).block.ctors s c).recoveryIndex f with
      | none =>
        simp only [hrel, he] at hx ⊢
        exact Filter.Eventually.of_forall fun _ => hx
      | some i =>
        simp only [hrel, he] at hx ⊢
        exact hv i hx
    · rename_i hrel
      simp only [hrel]
      exact Filter.Eventually.of_forall fun _ => hx
  | right f =>
    simp only [recoveredField, Fin.append_right] at hx ⊢
    exact Filter.Eventually.of_forall fun _ => hx

private theorem proofConstructor_eventually {α : Type*} {L : Filter α}
    (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts) (σ : Γ₂ ⟶ Γ₁)
    (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    {indices : Fin (ι.nindices s) → RawValue Γ₂}
    {values : α → Fin (ι.nindices s) → RawValue Γ₂}
    (hv : ∀ i {x}, (indices i).mem (𝟙 Γ₂) x → ∀ᶠ a in L, (values a i).mem (𝟙 Γ₂) x)
    {y : CoherentShape Γ₂} (hy : (proofConstructor h s σ indexNames indices).mem (𝟙 Γ₂) y) :
    ∀ᶠ a in L, (proofConstructor h s σ indexNames (values a)).mem (𝟙 Γ₂) y := by
  rcases hy with hy | ⟨c, sect, hn, fields, hf, hy⟩
  · exact Filter.Eventually.of_forall fun _ => Or.inl hy
  · simp only [ΩLower.pullback_id] at hf
    have he := Filter.eventually_all.mpr fun f => recoveredField_eventually hv f (hf f)
    refine he.mono fun a ha => Or.inr ⟨c, sect, hn, fields, ?_, hy⟩
    simpa using ha

theorem recoverMajor_isFinitary (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (source : Γ₂ ⟶ Γ₁) (indexNames : Fin (ι.nindices s) → Tm_ Γ₂)
    (indices : Fin (ι.nindices s) → RawFamily Γ₂) (major : RawFamily Γ₂)
    (hi : ∀ i, (indices i).IsFinitary) (hm : major.IsFinitary) :
    (recoverMajor h s source indexNames indices major).IsFinitary := by
  intro Γ₃ σ i ρ
  by_cases hrel : Level.rel ((E.get η).block.level.inst ls) = true
  · simpa only [recoverMajor, hrel, ↓reduceIte] using hm σ i ρ
  · simp only [recoverMajor, hrel]
    exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
      proofConstructor_eventually h s _ _ (fun j {_} hx => RawFamily.IsFinitary.eventually (hi j) σ i ρ I hx) hy

end Metalean.CoherentShape
