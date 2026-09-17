module

public import Metalean.Semantics.Interpretation.Binder.Basic
public import Metalean.Semantics.Interpretation.Family.Application
public import Metalean.Semantics.Interpretation.Recursor.Section
import Mathlib.Order.Filter.Finite

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}

noncomputable def caseArgs {k n : Nat} (hyps : Fin n → RawValue Γ₁)
    (names : Fin k → Tm_ Γ₁) (args : Fin k → RawValue Γ₁) :
    Fin (k + n) → RawValue Γ₁ :=
  Fin.append args fun f => rawApps (hyps f) names args

theorem caseArgs_mono {k n : Nat} {hyps hyps' : Fin n → RawValue Γ₁}
    (hhyps : ∀ f, hyps f ≤ hyps' f) (names : Fin k → Tm_ Γ₁)
    {args args' : Fin k → RawValue Γ₁} (hargs : ∀ i, args i ≤ args' i) (i : Fin (k + n)) :
    caseArgs hyps names args i ≤ caseArgs hyps' names args' i := by
  cases i using Fin.addCases with
  | left i =>
    simp only [caseArgs, Fin.append_left]
    exact hargs i
  | right f =>
    simp only [caseArgs, Fin.append_right]
    exact rawApps_mono (hhyps f) names hargs

theorem pullback_caseArgs {k n : Nat} (hyps : Fin n → RawValue Γ₁)
    (names : Fin k → Tm_ Γ₁) (args : Fin k → RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (fun i => (caseArgs hyps names args i).pullback σ) =
      caseArgs (fun f => (hyps f).pullback σ) (fun i => (Tm E ℓ).map σ.op (names i))
        fun i => (args i).pullback σ := by
  funext i
  cases i using Fin.addCases <;> simp [caseArgs, pullback_rawApps]

theorem caseArgs_isDirected {k n : Nat} {hyps : Fin n → RawValue Γ₁}
    (hhyps : ∀ f, (hyps f).IsDirected) (names : Fin k → Tm_ Γ₁)
    {args : Fin k → RawValue Γ₁} (hargs : ∀ i, (args i).IsDirected) (i : Fin (k + n)) :
    (caseArgs hyps names args i).IsDirected := by
  cases i using Fin.addCases with
  | left i =>
    rw [caseArgs, Fin.append_left]
    exact hargs i
  | right f =>
    rw [caseArgs, Fin.append_right]
    exact rawApps_isDirected ⟨_, hhyps f⟩ names fun i => ⟨_, hargs i⟩

variable {h : RecData Γ₁ η ls l ps ms mins}

def Observed {σ₁ : Γ₂ ⟶ Γ₁} {σ₂ : Γ₃ ⟶ Γ₂}
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂)
    (sect : CtorSection h s c (σ₂ ≫ σ₁))
    (fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃) : Prop :=
  ¬ (E.get η).block.IsStructure s c ∧ X.mem σ₂ (ctorMap ⟨η, s, c⟩ sect.names fields) ∨
    ∃ hstruct : (E.get η).block.IsStructure s c,
      sect.ProjectsFrom hstruct ((Tm E ℓ).map σ₂.op majorName) ∧
        ∀ i, (RawValue.proj ⟨η, s, c⟩ i X).mem σ₂ (fields i)

theorem Observed.mono {majorName : Tm_ Γ₂} {X Y : RawValue Γ₂} {σ₁ : Γ₂ ⟶ Γ₁}
    {σ₂ : Γ₃ ⟶ Γ₂}
    {sect : CtorSection h s c (σ₂ ≫ σ₁)}
    {fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃}
    (hXY : X ≤ Y) (hobs : Observed majorName X sect fields) :
    Observed majorName Y sect fields := by
  rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
  · exact Or.inl ⟨hns, hXY σ₂ _ hX⟩
  · exact Or.inr ⟨hstruct, hp, fun i => RawValue.proj_mono _ i hXY σ₂ _ (hf i)⟩

theorem Observed.natural {majorName : Tm_ Γ₂} {X : RawValue Γ₂} {σ₁ : Γ₂ ⟶ Γ₁}
    {σ₂ : Γ₃ ⟶ Γ₂}
    {sect : CtorSection h s c (σ₂ ≫ σ₁)}
    {fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃}
    (hobs : Observed majorName X sect fields) {Γ₄ : CtxCat E ℓ} (σ₃ : Γ₄ ⟶ Γ₃) :
    Observed majorName X ((sect.pullback σ₃).congr (Category.assoc σ₃ σ₂ σ₁).symm)
      fun i => reindex σ₃ (fields i) := by
  have hmap : (Tm E ℓ).map σ₃.op ((Tm E ℓ).map σ₂.op majorName) =
      (Tm E ℓ).map (σ₃ ≫ σ₂).op majorName :=
    ((Tm E ℓ).map_comp_apply σ₂.op σ₃.op majorName).symm
  rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
  · exact Or.inl ⟨hns, by simpa using X.natural σ₂ σ₃ _ hX⟩
  · refine Or.inr ⟨hstruct, ?_, fun i => by simpa using (RawValue.proj _ i X).natural σ₂ σ₃ _ (hf i)⟩
    have hpp := (hp.pullback σ₃).congr (Category.assoc σ₃ σ₂ σ₁).symm
    rwa [hmap] at hpp

variable (h)

noncomputable def rawRecCase
    (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂) : RawValue Γ₂ where
  mem σ₂ y := y ≤ ⊥ ∨ ∃ (c : Fin (ι.nctors s))
    (sect : CtorSection h s c (σ₂ ≫ σ₁))
    (fields : Fin (CtorHead.mk η s c).arity → CoherentShape _),
    Observed majorName X sect fields ∧
      (rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
        (Fin.append sect.names fun f => sect.ihName f)
        (caseArgs (fun f => (ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
          fun i => (principalIdeal (fields i)).val)).mem (𝟙 _) y
  natural σ₂ σ₃ y hy := by
    rcases hy with hy | ⟨c, sect, fields, hobs, hy⟩
    · exact Or.inl (le_bot_iff.mpr (le_bot_iff.mp (CoherentShape.Le.reindex σ₃ hy)))
    · refine Or.inr ⟨c, (sect.pullback σ₃).congr (Category.assoc σ₃ σ₂ σ₁).symm, fun i => reindex σ₃ (fields i),
        hobs.natural σ₃, ?_⟩
      have hy' := ΩLower.natural _ (𝟙 _) σ₃ y hy
      have hih : (fun f => ((ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).pullback σ₃) =
          fun f => (ih c f).app _ ((σ₂ ≫ σ₁).op ≫ σ₃.op) ((ρ.pullback σ₂).pullback σ₃) :=
        funext fun f => RawFamily.app_pullback ..
      rw [Category.comp_id, ← ΩLower.presheaf_map_mem_id, pullback_rawApps, RawFamily.app_pullback,
        Fin.append_comp _ _ ((Tm E ℓ).map σ₃.op), pullback_caseArgs, hih] at hy'
      simpa [Category.assoc, ΩLower.presheaf_map_principal, RawValuation.pullback_comp] using hy'
  bottom _ := Or.inl bot_le
  lower σ₂ hyz hz := by
    rcases hz with hz | ⟨c, sect, fields, hobs, hz⟩
    · exact Or.inl (hyz.trans hz)
    · exact Or.inr ⟨c, sect, fields, hobs, ΩLower.lower _ (𝟙 _) hyz hz⟩

theorem pullback_rawRecCase (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) :
    (rawRecCase h minValue ih σ₁ ρ majorName X).pullback σ₂ =
      rawRecCase h minValue ih (σ₂ ≫ σ₁) (ρ.pullback σ₂) ((Tm E ℓ).map σ₂.op majorName)
        (X.pullback σ₂) := by
  have hmap {Γ₄ : CtxCat E ℓ} (g : Γ₄ ⟶ Γ₃) :
      (Tm E ℓ).map g.op ((Tm E ℓ).map σ₂.op majorName) =
        (Tm E ℓ).map (g ≫ σ₂).op majorName :=
    ((Tm E ℓ).map_comp_apply σ₂.op g.op majorName).symm
  ext Γ₄ g y
  rw [ΩLower.presheaf_map_mem]
  constructor
  · rintro (hy | ⟨c, sect, fields, hobs, hy⟩)
    · exact Or.inl hy
    · refine Or.inr ⟨c, sect.congr (Category.assoc g σ₂ σ₁), fields, ?_, ?_⟩
      · rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
        · exact Or.inl ⟨hns, hX⟩
        · exact Or.inr ⟨hstruct, by rw [hmap]; exact hp.congr (Category.assoc g σ₂ σ₁),
            fun i => by simpa using hf i⟩
      · simpa [RawValuation.pullback_comp, Category.assoc] using hy
  · rintro (hy | ⟨c, sect, fields, hobs, hy⟩)
    · exact Or.inl hy
    · refine Or.inr ⟨c, sect.congr (Category.assoc g σ₂ σ₁).symm, fields, ?_, ?_⟩
      · rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
        · exact Or.inl ⟨hns, hX⟩
        · refine Or.inr ⟨hstruct, ?_, fun i => by simpa using hf i⟩
          have hpp := hp.congr (Category.assoc g σ₂ σ₁).symm
          rwa [hmap] at hpp
      · simpa [RawValuation.pullback_comp, Category.assoc] using hy

theorem rawRecCase_mono (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih ih' : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (hih : ∀ c f, ih c f ≤ ih' c f)
    (σ₁ : Γ₂ ⟶ Γ₁) {ρ ρ' : RawValuation Γ₂} (hρ : ρ ≤ ρ') (majorName : Tm_ Γ₂)
    {X X' : RawValue Γ₂} (hX : X ≤ X') :
    rawRecCase h minValue ih σ₁ ρ majorName X ≤ rawRecCase h minValue ih' σ₁ ρ' majorName X' := by
  rintro Γ₃ σ₂ y (hy | ⟨c, sect, fields, hobs, hy⟩)
  · exact Or.inl hy
  · have hpull : ρ.pullback σ₂ ≤ ρ'.pullback σ₂ := fun i => ΩLower.pullback_mono (hρ i) σ₂
    exact Or.inr ⟨c, sect, fields, hobs.mono hX,
      rawApps_mono (((minValue c).app _ (σ₂ ≫ σ₁).op).hom.monotone hpull) _
        (caseArgs_mono (fun f _ g a ha => ((ih' c f).app _ (σ₂ ≫ σ₁).op).hom.monotone hpull g a
          (hih c f _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) g a ha)) _ fun _ {_} _ _ hz => hz) _ _ hy⟩

theorem rawRecCase_isDirected_tail (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hdir : ∀ c f {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂),
      ((ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected)
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂)
    (hmin : ∀ (c : Fin (ι.nctors s)) {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂),
      ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected)
    {σ₂ : Γ₃ ⟶ Γ₂}
    (sect : CtorSection h s c (σ₂ ≫ σ₁))
    {fields₁ fields₂ fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃}
    (hobs : Observed majorName X sect fields)
    (hle₁ : ∀ i, fields₁ i ≤ fields i) (hle₂ : ∀ i, fields₂ i ≤ fields i)
    {a b : CoherentShape Γ₃}
    (ha : (rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
      (Fin.append sect.names fun f => sect.ihName f)
      (caseArgs (fun f => (ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
        fun i => (principalIdeal (fields₁ i)).val)).mem (𝟙 Γ₃) a)
    (hb : (rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
      (Fin.append sect.names fun f => sect.ihName f)
      (caseArgs (fun f => (ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
        fun i => (principalIdeal (fields₂ i)).val)).mem (𝟙 Γ₃) b) :
    ∃ y, (rawRecCase h minValue ih σ₁ ρ majorName X).mem σ₂ y ∧ a ≤ y ∧ b ≤ y := by
  have ha' := rawApps_mono (fun _ _ hy => hy) _
    (caseArgs_mono (fun _ {_} _ _ hz => hz) _ fun i => ΩLower.principal_mono (hle₁ i)) (𝟙 Γ₃) a ha
  have hb' := rawApps_mono (fun _ _ hy => hy) _
    (caseArgs_mono (fun _ {_} _ _ hz => hz) _ fun i => ΩLower.principal_mono (hle₂ i)) (𝟙 Γ₃) b hb
  have ⟨y, hy, hay, hby⟩ := rawApps_isDirected
    ⟨(minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂), hmin c σ₂⟩
    (Fin.append sect.names fun f => sect.ihName f)
    (fun idx => ⟨_, caseArgs_isDirected (fun f => hdir c f σ₂) sect.names
      (fun i => (principalIdeal (fields i)).property) idx⟩) (𝟙 Γ₃) ha' hb'
  exact ⟨y, Or.inr ⟨c, sect, fields, hobs, hy⟩, hay, hby⟩

theorem rawRecCase_isDirected (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hdir : ∀ c f {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂),
      ((ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected)
    (majorName : Tm_ Γ₂) {X : RawValue Γ₂} (hX : X.IsDirected)
    (hmin : ∀ (c : Fin (ι.nctors s)) {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂),
      ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected) :
    (rawRecCase h minValue ih σ₁ ρ majorName X).IsDirected := by
  intro Γ₃ σ₂ a b ha hb
  rcases ha with ha | ⟨c₁, sect₁, fields₁, hobs₁, ha⟩
  · exact ⟨b, hb, ha.trans bot_le, le_rfl⟩
  rcases hb with hb | ⟨c₂, sect₂, fields₂, hobs₂, hb⟩
  · exact ⟨a, Or.inr ⟨c₁, sect₁, fields₁, hobs₁, ha⟩, le_rfl, hb.trans bot_le⟩
  rcases hobs₁ with ⟨hns₁, hX₁⟩ | ⟨hstruct₁, hp₁, hf₁⟩
  · rcases hobs₂ with ⟨hns₂, hX₂⟩ | ⟨hstruct₂, hp₂, hf₂⟩
    · have ⟨z, hXz, hz₁, hz₂⟩ := hX σ₂ hX₁ hX₂
      obtain ⟨fields, rfl, hle₁⟩ := (ctorMap_le_inv hz₁).resolve_left fun hbot =>
        hns₁ (ctorMap_le_bot_iff.mp hbot).1
      obtain rfl : c₂ = c₁ := by
        rcases ctorMap_head_eq hz₂ with hbot | heq
        · exact absurd (ctorMap_le_bot_iff.mp hbot).1 hns₂
        · simpa using heq
      have hle₂ : ∀ i, fields₂ i ≤ fields i := ctorMap_le_field hz₂
      obtain rfl : sect₂ = sect₁ := CtorSection.eq_of_names_eq (ctorMap_names_eq hns₂ hz₂)
      exact rawRecCase_isDirected_tail h minValue σ₁ ρ hdir majorName X hmin sect₂
        (Or.inl ⟨hns₁, hXz⟩) hle₁ hle₂ ha hb
    · obtain rfl : c₁ = c₂ := hstruct₂.ctor_unique c₁
      exact absurd hstruct₂ hns₁
  · rcases hobs₂ with ⟨hns₂, hX₂⟩ | ⟨hstruct₂, hp₂, hf₂⟩
    · obtain rfl : c₂ = c₁ := hstruct₁.ctor_unique c₂
      exact absurd hstruct₁ hns₂
    · obtain rfl : c₂ = c₁ := hstruct₁.ctor_unique c₂
      obtain rfl : sect₂ = sect₁ :=
        CtorSection.eq_of_names_eq (CtorSection.names_eq_of_projectsFrom sect₂ sect₁ hp₂ hp₁)
      choose g hg hg₁ hg₂ using fun i =>
        RawValue.proj_isDirected _ i hX σ₂ (hf₁ i) (hf₂ i)
      exact rawRecCase_isDirected_tail h minValue σ₁ ρ hdir majorName X hmin sect₂
        (Or.inr ⟨hstruct₁, hp₁, hg⟩) hg₁ hg₂ ha hb

noncomputable def rawRecCaseAction
    (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    RawAction Γ₂ where
  val.app _ σ₂ := ↾fun p => rawRecCase h minValue ih (σ₂.unop ≫ σ₁) (ρ.pullback σ₂.unop) p.1 p.2
  val.naturality σ₃ σ₂ := ConcreteCategory.hom_ext _ _ fun p => by
    change rawRecCase h minValue ih ((σ₂ ≫ σ₃).unop ≫ σ₁) (ρ.pullback (σ₂ ≫ σ₃).unop)
        ((Tm E ℓ).map σ₃ p.1) (p.2.pullback σ₃.unop) =
      (rawRecCase h minValue ih (σ₂.unop ≫ σ₁) (ρ.pullback σ₂.unop) p.1 p.2).pullback σ₃.unop
    rw [pullback_rawRecCase]
    congr 1
    · rw [unop_comp, Category.assoc]
    · rw [unop_comp, RawValuation.pullback_comp]
  property _ _ _ _ _ hI := rawRecCase_mono h minValue (fun _ _ => le_rfl) _ le_rfl _ hI

noncomputable def rawRecCaseFamily
    (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁) :
    RawActionFamily Γ₁ where
  app _ σ := Preord.ofHom {
    toFun ρ := rawRecCaseAction h minValue ih σ.unop ρ
    monotone' _ _ hρ := fun _ p I =>
      rawRecCase_mono h minValue (fun _ _ => le_rfl) (p.1.unop ≫ σ.unop)
        (fun i => ΩLower.pullback_mono (hρ i) p.1.unop) p.2
        fun {_} _ _ hz => hz }
  naturality f σ := Preord.ext fun ρ => RawAction.ext fun X p I => by
    change rawRecCase h minValue ih (p.1.unop ≫ (σ ≫ f).unop)
        ((ρ.pullback f.unop).pullback p.1.unop) p.2 I =
      rawRecCase h minValue ih ((f ≫ p.1).unop ≫ σ.unop) (ρ.pullback (f ≫ p.1).unop) p.2 I
    congr 1
    · rw [unop_comp, unop_comp, Category.assoc]
    · rw [unop_comp, RawValuation.pullback_comp]

theorem rawRecCaseFamily_value (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂) (X : RawValue Γ₂) :
    ((rawRecCaseFamily h minValue ih).app _ σ.op ρ).app _ ((𝟙 Γ₂).op, label) X =
      rawRecCase h minValue ih σ ρ label X := by
  change rawRecCase h minValue ih (𝟙 Γ₂ ≫ σ) (ρ.pullback (𝟙 Γ₂)) label X = _
  rw [Category.id_comp, RawValuation.pullback_id]

theorem rawRecCaseFamily_mono (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih₁ ih₂ : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (hih : ∀ c f, ih₁ c f ≤ ih₂ c f) :
    rawRecCaseFamily h minValue ih₁ ≤ rawRecCaseFamily h minValue ih₂ :=
  fun _ σ _ _ p _ => rawRecCase_mono h minValue hih (p.1.unop ≫ σ.unop) le_rfl p.2
    fun _ _ hz => hz

theorem rawRecCaseFamily_isFinitary {minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁}
    (hmin : ∀ c, (minValue c).IsFinitary)
    {ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (hih : ∀ c f, (ih c f).IsFinitary) : (rawRecCaseFamily h minValue ih).IsFinitary := by
  intro Γ₂ σ i ρ X label
  have hval (I : RawValue Γ₂) :
      ((rawRecCaseFamily h minValue ih).app _ σ.op (ρ.replace i I)).app _ ((𝟙 Γ₂).op, label) X =
        rawRecCase h minValue ih σ (ρ.replace i I) label X :=
    rawRecCaseFamily_value h minValue ih σ (ρ.replace i I) label X
  simp only [hval]
  refine ΩLower.IsFinitary.of_eventually fun I _ hy => ?_
  rcases hy with hy | ⟨c, sect, fields, hobs, hy⟩
  · exact Filter.Eventually.of_forall fun _ => Or.inl hy
  · rw [RawValuation.pullback_id] at hy
    have hargs : ∀ idx {x},
        (caseArgs (fun f => (ih c f).app _ (𝟙 Γ₂ ≫ σ).op (ρ.replace i I)) sect.names
          (fun j => (principalIdeal (fields j)).val) idx).mem (𝟙 Γ₂) x →
        ∀ᶠ J in I.approximations,
          (caseArgs (fun f => (ih c f).app _ (𝟙 Γ₂ ≫ σ).op (ρ.replace i J)) sect.names
            (fun j => (principalIdeal (fields j)).val) idx).mem (𝟙 Γ₂) x := by
      intro idx
      cases idx using Fin.addCases with
      | left j =>
        simp only [caseArgs, Fin.append_left]
        exact fun {_} hx => Filter.Eventually.of_forall fun _ => hx
      | right j =>
        simp only [caseArgs, Fin.append_right]
        exact fun {_} hx => rawApps_eventually
          (RawFamily.IsFinitary.eventually (hih c j) (𝟙 Γ₂ ≫ σ) i ρ I) sect.names
          (fun _ {_} hz => Filter.Eventually.of_forall fun _ => hz) hx
    refine Filter.Eventually.mono
      (rawApps_eventually (RawFamily.IsFinitary.eventually (hmin c) (𝟙 Γ₂ ≫ σ) i ρ I) _ hargs hy)
      fun J hJ => Or.inr ⟨c, sect, fields, hobs, ?_⟩
    rwa [RawValuation.pullback_id]

theorem rawRecCaseFamily_isActionFinitary (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁) :
    (rawRecCaseFamily h minValue ih).IsActionFinitary := by
  intro Γ₂ σ₁ ρ Γ₃ σ₂ label
  change ΩLower.IsFinitary fun X => rawRecCase h minValue ih (σ₂ ≫ σ₁) (ρ.pullback σ₂) label X
  refine ΩLower.IsFinitary.of_eventually fun X _ hy => ?_
  rcases hy with hy | ⟨c, sect, fields, hobs, hy⟩
  · exact Filter.Eventually.of_forall fun _ => Or.inl hy
  · rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
    · exact (ΩLower.eventually_mem hX).mono fun J hJ =>
        Or.inr ⟨c, sect, fields, Or.inl ⟨hns, hJ⟩, hy⟩
    · exact (Filter.eventually_all.mpr fun i => RawValue.proj_eventually ⟨η, s, c⟩ i (hf i)).mono
        fun J hJ => Or.inr ⟨c, sect, fields, Or.inr ⟨hstruct, hp, hJ⟩, hy⟩

theorem rawRecCase_le_iSup (minValue : (c₁ : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih : (c₁ : Fin (ι.nctors s)) → Fin (ι.ctors s c₁).nrecFields → RawFamily Γ₁}
    {ihs : Nat → (c₁ : Fin (ι.nctors s)) → Fin (ι.ctors s c₁).nrecFields → RawFamily Γ₁}
    (hle : ∀ c₁ f, ih c₁ f ≤ ⨆ n, ihs n c₁ f) (hmono : ∀ c₁ f, Monotone fun n => ihs n c₁ f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂) :
    rawRecCase h minValue ih σ₁ ρ majorName X ≤
      ⨆ n, rawRecCase h minValue (ihs n) σ₁ ρ majorName X := by
  rintro Γ₃ σ₂ y (hy | ⟨c₁, sect, fields, hobs, hy⟩)
  · exact (ΩLower.mem_iSup ..).mpr (Or.inl hy)
  · have hbot : (minValue c₁).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) ≤
        ⨆ _n : Nat, (minValue c₁).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) :=
      fun _ _ hz => (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨0, hz⟩
    have hargs : ∀ idx,
        caseArgs (fun f => (ih c₁ f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
          (fun j => (principalIdeal (fields j)).val) idx ≤
        ⨆ n, caseArgs (fun f => (ihs n c₁ f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
          (fun j => (principalIdeal (fields j)).val) idx := by
      intro idx
      cases idx using Fin.addCases with
      | left j =>
        simp only [caseArgs, Fin.append_left]
        exact fun _ _ hz => (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨0, hz⟩
      | right j =>
        simp only [caseArgs, Fin.append_right]
        have hfamily : (ih c₁ j).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) ≤
            ⨆ n, (ihs n c₁ j).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) := by
          rw [← RawFamily.iSup_app]
          exact hle c₁ j _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)
        exact fun _ g z hz => rawApps_iSup_le_const sect.names _ g z
          (rawApps_mono hfamily sect.names (fun _ {_} _ _ hw => hw) g z hz)
    have hmono' : ∀ idx, Monotone fun n =>
        caseArgs (fun f => (ihs n c₁ f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) sect.names
          (fun j => (principalIdeal (fields j)).val) idx :=
      fun idx _ _ hab => caseArgs_mono (fun f => hmono c₁ f hab _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
        sect.names (fun _ {_} _ _ hz => hz) idx
    have hy₁ := rawApps_mono hbot (Fin.append sect.names fun f => sect.ihName f) hargs (𝟙 Γ₃) y hy
    have hy₂ := rawApps_iSup_le
      (fun _ _ _ _ _ _ hz => hz) (Fin.append sect.names fun f => sect.ihName f) hmono' (𝟙 Γ₃) y hy₁
    have ⟨n, hy₂⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy₂
    exact (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, Or.inr ⟨c₁, sect, fields, hobs, hy₂⟩⟩

theorem rawRecCaseFamily_le_iSup (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    {ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    {ihs : Nat → (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁}
    (hle : ∀ c f, ih c f ≤ ⨆ n, ihs n c f) (hmono : ∀ c f, Monotone fun n => ihs n c f) :
    rawRecCaseFamily h minValue ih ≤ ⨆ n, rawRecCaseFamily h minValue (ihs n) := by
  intro X σ ρ Y p I Γ₃ g y hy
  have ⟨n, hy⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp
    (rawRecCase_le_iSup h minValue hle hmono (p.1.unop ≫ σ.unop) (ρ.pullback p.1.unop) p.2 I g y hy)
  change (((⨆ n, rawRecCaseFamily h minValue (ihs n)).app X σ ρ).app Y p I).mem g y
  rw [RawActionFamily.iSup_app, RawAction.iSup_app]
  exact (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, hy⟩

theorem mem_rawRecCase_ctor (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (sect : CtorSection h s c σ₁)
    (xs : Fin (CtorHead.mk η s c).arity → RawValue Γ₂) (majorName : Tm_ Γ₂)
    (hname : ∀ hstruct : (E.get η).block.IsStructure s c, sect.ProjectsFrom hstruct majorName)
    (σ₂ : Γ₃ ⟶ Γ₂) (y : CoherentShape Γ₃) :
    (rawRecCase h minValue ih σ₁ ρ majorName (RawValue.ctor ⟨η, s, c⟩ sect.names xs)).mem σ₂ y ↔
      y ≤ ⊥ ∨ ∃ fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃,
        (∀ i, (xs i).mem σ₂ (fields i)) ∧
          (rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
            (Fin.append (sect.pullback σ₂).names fun f => (sect.pullback σ₂).ihName f)
            (caseArgs (fun f => (ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) (sect.pullback σ₂).names
              fun i => (principalIdeal (fields i)).val)).mem (𝟙 Γ₃) y := by
  constructor
  · rintro (hy | ⟨c₁, sect₁, fields, hobs, hy⟩)
    · exact Or.inl hy
    · rcases hobs with ⟨hns, hX⟩ | ⟨hstruct, hp, hf⟩
      · rw [RawValue.mem_ctor] at hX
        have ⟨xs', hxs, hle⟩ := hX
        obtain rfl : c₁ = c := by
          rcases ctorMap_head_eq hle with hbot | heq
          · exact absurd (ctorMap_le_bot_iff.mp hbot).1 hns
          · simpa using heq
        obtain rfl : sect₁ = sect.pullback σ₂ :=
          CtorSection.eq_of_names_eq (by simpa using ctorMap_names_eq hns hle)
        exact Or.inr ⟨fields, fun i => ΩLower.lower _ σ₂ (ctorMap_le_field hle i) (hxs i), hy⟩
      · obtain rfl : c₁ = c := (hstruct.ctor_unique c).symm
        obtain rfl : sect₁ = sect.pullback σ₂ := CtorSection.eq_of_names_eq
          (CtorSection.names_eq_of_projectsFrom sect₁ (sect.pullback σ₂) hp ((hname hstruct).pullback σ₂))
        exact Or.inr ⟨fields, fun i => by simpa only [RawValue.proj_ctor] using hf i, hy⟩
  · rintro (hy | ⟨fields, hfields, hy⟩)
    · exact Or.inl hy
    · refine Or.inr ⟨c, sect.pullback σ₂, fields, ?_, hy⟩
      by_cases hstruct : (E.get η).block.IsStructure s c
      · refine Or.inr ⟨hstruct, (hname hstruct).pullback σ₂, fun i => ?_⟩
        rw [RawValue.proj_ctor]
        exact hfields i
      · exact Or.inl ⟨hstruct, ⟨fields, hfields, by simp⟩⟩

theorem rawApps_case_names (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (ρ : RawValuation Γ₂)
    (sect : CtorSection h s c σ₁) (σ₂ : Γ₃ ⟶ Γ₂)
    (args : Fin ((CtorHead.mk η s c).arity + (ι.ctors s c).nrecFields) → RawValue Γ₃) :
    rawApps (((minValue c).app _ σ₁.op ρ).pullback σ₂)
        (fun idx => (Tm E ℓ).map σ₂.op
          (Fin.append sect.names (fun f => sect.ihName f) idx)) args =
      rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
        (Fin.append (fun i => (Tm E ℓ).map σ₂.op (sect.names i))
          fun f => (sect.pullback σ₂).ihName f) args := by
  rw [RawFamily.app_pullback, Fin.append_comp]
  simp

theorem rawRecCase_ctor (minValue : (c : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (c : Fin (ι.nctors s)) → Fin (ι.ctors s c).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (sect : CtorSection h s c σ₁)
    (xs : Fin (CtorHead.mk η s c).arity → RawValue Γ₂) (hxs : ∀ i, (xs i).IsDirected)
    (majorName : Tm_ Γ₂)
    (hname : ∀ hstruct : (E.get η).block.IsStructure s c, sect.ProjectsFrom hstruct majorName) :
    rawRecCase h minValue ih σ₁ ρ majorName (RawValue.ctor ⟨η, s, c⟩ sect.names xs) =
      rawApps ((minValue c).app _ σ₁.op ρ) (Fin.append sect.names fun f => sect.ihName f)
        (caseArgs (fun f => (ih c f).app _ σ₁.op ρ) sect.names xs) := by
  ext Γ₃ σ₂ y
  rw [mem_rawRecCase_ctor h minValue ih σ₁ ρ sect xs majorName hname σ₂ y, CtorSection.names_pullback]
  constructor
  · rintro (hy | ⟨fields, hfields, hy⟩)
    · exact ΩLower.lower _ σ₂ hy (ΩLower.bottom _ σ₂)
    · have hle : rawApps ((minValue c).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
          (Fin.append (fun i => (Tm E ℓ).map σ₂.op (sect.names i))
            fun f => (sect.pullback σ₂).ihName f)
          (caseArgs (fun f => (ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
            (fun i => (Tm E ℓ).map σ₂.op (sect.names i))
            fun i => (principalIdeal (fields i)).val) ≤
          (rawApps ((minValue c).app _ σ₁.op ρ) (Fin.append sect.names fun f => sect.ihName f)
            (caseArgs (fun f => (ih c f).app _ σ₁.op ρ) sect.names xs)).pullback σ₂ := by
        rw [pullback_rawApps, rawApps_case_names, pullback_caseArgs]
        exact rawApps_mono (fun _ _ hz => hz) _
          (caseArgs_mono (fun f {_} g a hz => by rw [RawFamily.app_pullback]; exact hz) _
            fun i => ΩLower.principal_le_iff.mpr (by simpa using hfields i))
      simpa using hle (𝟙 Γ₃) y hy
  · intro hy
    have ⟨zs, hzs, hy⟩ := exists_shapes_of_mem_rawApps _ σ₂ _ _ y hy
    rw [rawApps_case_names] at hy
    have hrec : ∀ f, ∃ fields : Fin (CtorHead.mk η s c).arity → CoherentShape Γ₃,
        (∀ i, (xs i).mem σ₂ (fields i)) ∧
          (rawApps ((ih c f).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂))
            (fun i => (Tm E ℓ).map σ₂.op (sect.names i))
            fun i => (principalIdeal (fields i)).val).mem (𝟙 Γ₃) (zs (Fin.natAdd _ f)) := by
      intro f
      have hf := hzs (Fin.natAdd _ f)
      simp only [caseArgs, Fin.append_right] at hf
      have ⟨fields, hmem, hf⟩ := exists_shapes_of_mem_rawApps _ σ₂ _ _ _ hf
      rw [RawFamily.app_pullback] at hf
      exact ⟨fields, hmem, hf⟩
    choose fieldsOf hfieldsOf happ using hrec
    have hmajor (i : Fin (CtorHead.mk η s c).arity) : (xs i).mem σ₂ (zs (Fin.castAdd _ i)) := by
      simpa only [caseArgs, Fin.append_left] using hzs (Fin.castAdd (ι.ctors s c).nrecFields i)
    choose b hb hble using fun i =>
      ΩLower.IsDirected.exists_upper_fin (hxs i) σ₂ (fun f => fieldsOf f i) fun f =>
        hfieldsOf f i
    choose g hg hbg hzg using fun i => hxs i σ₂ (hb i) (hmajor i)
    refine Or.inr ⟨g, hg, rawApps_mono (fun _ _ hz => hz) _ (fun idx => ?_) (𝟙 Γ₃) y hy⟩
    cases idx using Fin.addCases with
    | left i =>
      simp only [caseArgs, Fin.append_left]
      exact ΩLower.principal_mono (hzg i)
    | right f =>
      simp only [caseArgs, Fin.append_right]
      exact ΩLower.principal_le_iff.mpr (rawApps_mono (fun _ _ hz => hz) _
        (fun i => ΩLower.principal_mono ((hble i f).trans (hbg i))) (𝟙 Γ₃) _ (happ f))

end Metalean.CoherentShape
