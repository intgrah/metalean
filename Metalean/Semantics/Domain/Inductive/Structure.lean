/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Decoder.Telescope
public import Metalean.Semantics.Domain.Inductive.Projection
public import Metalean.Semantics.Syntax.Projection

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

namespace CodeAssignment

variable {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}

variable (F : CodeAssignment E ℓ)

noncomputable def indNames {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (hg : code.StructGuard c n) :
    Fin (code.ctorHead c).arity → Tm_ Γ₁ :=
  Fin.append (Tm.projOfCode hg) hg.witness.struct.no_recursive.elim

noncomputable def indBody {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors}
    {n : Tm_ Γ₁} (T : Domain Γ₁) (X : Domain Γ₁) (hg : code.StructGuard c n) :
    Domain Γ₁ :=
  ctorIdeal (code.ctorHead c) (indNames hg)
    (F.telescope T (indNames hg) fun i => projIdeal (code.ctorHead c) i X).1

variable {code : IndCode Γ₁} {c : Fin code.toIndHead.nctors} {n : Tm_ Γ₁}

theorem map_indNames (hg : code.StructGuard c n) (σ : Γ₂ ⟶ Γ₁)
    (hg' : (code.map ((Tm E ℓ).map σ.op)).StructGuard c
      ((Tm E ℓ).map σ.op n)) (i : Fin (code.ctorHead c).arity) :
    (Tm E ℓ).map σ.op (indNames hg i) = indNames hg' i := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  refine Fin.addCases (fun f => ?_) (fun f => ?_) i
  · rw [indNames, indNames, Fin.append_left, Fin.append_left]
    exact Tm.map_projOfCode hg σ f hg'
  · exact hg.witness.struct.no_recursive.elim f

theorem pullback_indBody (T X : Domain Γ₁) (hg : code.StructGuard c n) (σ : Γ₂ ⟶ Γ₁)
    (hg' : (code.map ((Tm E ℓ).map σ.op)).StructGuard c
      ((Tm E ℓ).map σ.op n)) :
    (F.indBody T X hg).pullback σ = F.indBody (T.pullback σ) (X.pullback σ) hg' := by
  rw [indBody, pullback_ctorIdeal]
  have hn := funext fun i => map_indNames hg σ hg' i
  refine congrArg₂ (ctorIdeal (code.ctorHead c)) hn ?_
  have h := congrArg (fun result :
      (Fin (code.ctorHead c).arity → Domain Γ₂) × Domain Γ₂ => result.1)
    (F.pullback_telescope T (indNames hg) (fun i => projIdeal (code.ctorHead c) i X) σ)
  simpa [hn] using h

theorem indBody_mono {T T' X X' : Domain Γ₁} (hT : T ≤ T') (hX : X ≤ X')
    (hg : code.StructGuard c n) : F.indBody T X hg ≤ F.indBody T' X' hg :=
  RawValue.ctor_mono _ _ (F.telescope_mono _ hT fun i => projIdeal_mono _ i hX).1

theorem indBody_finitary (T : Domain Γ₁) (hg : code.StructGuard c n) :
    ΩIdeal.IsFinitary fun X : Domain Γ₁ => F.indBody T X hg := by
  apply ctorIdeal_finitary _ _ _
  · exact (F.telescope_finitary (indNames hg) (fun _ => T)
      (fun i => projIdeal (code.ctorHead c) i)
      (fun X _ hy => ⟨⊥, X.bottom (𝟙 Γ₁), hy⟩) (fun i => projIdeal_finitary _ i)
      (fun _ _ _ => fun _ _ h => h) fun i _ _ h => projIdeal_mono _ i h).1
  · exact fun i _ _ h => (F.telescope_mono _ (fun _ _ h => h)
      fun j => projIdeal_mono _ j h).1 i

theorem indBody_finitary_type (X : Domain Γ₁) (hg : code.StructGuard c n) :
    ΩIdeal.IsFinitary fun T : Domain Γ₁ => F.indBody T X hg := by
  apply ctorIdeal_finitary _ _ _
  · exact (F.telescope_finitary (indNames hg) id
      (fun i _ => projIdeal (code.ctorHead c) i X)
      (fun T y hy => ⟨y, hy, (principalIdeal_mem _ _ _).mpr (by simp)⟩)
      (fun _ T _ hy => ⟨⊥, T.bottom (𝟙 Γ₁), hy⟩)
      (fun _ _ h => h) fun _ _ _ _ => fun _ _ h => h).1
  · exact fun i _ _ h => (F.telescope_mono _ h fun _ _ _ _ h => h).1 i

theorem indBody_congr {code code' : IndCode Γ₁} (ecode : code = code')
    {c : Fin code.toIndHead.nctors} {c' : Fin code'.toIndHead.nctors} (ec : c.val = c'.val)
    {n n' : Tm_ Γ₁} (en : n = n') {T T' X X' : Domain Γ₁} (eT : T = T') (eX : X = X')
    (hg : code.StructGuard c n) (hg' : code'.StructGuard c' n') :
    F.indBody T X hg = F.indBody T' X' hg' := by
  cases ecode
  cases en
  cases eT
  cases eX
  obtain rfl := Fin.ext ec
  rfl

noncomputable def indRebuild (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (n : Tm_ Γ₂) (X : Domain Γ₂) : Domain Γ₂ where
  val.mem σ₂ y := y ≤ ⊥ ∨
    (∃ (c : Fin code.toIndHead.nctors)
      (hg : (code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op)).StructGuard c
        ((Tm E ℓ).map σ₂.op n)),
      (F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (X.pullback σ₂) hg).mem (𝟙 _) y) ∨
    (∀ c : Fin code.toIndHead.nctors, ¬ (E.get code.η).block.IsStructure code.s c) ∧
      (indIdeal code.toIndHead (X.pullback σ₂)).mem (𝟙 _) y
  val.natural σ₂ σ₃ y := by
    rintro (hy | ⟨c, hg, hy⟩ | ⟨hns, hy⟩)
    · exact Or.inl (Le.reindex σ₃ hy)
    · have hcode : (code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op)).map
          ((Tm E ℓ).map σ₃.op) =
          code.map ((Tm E ℓ).map ((σ₃ ≫ σ₂) ≫ σ₁).op) := by
        rw [← IndCode.map_comp_hom, Category.assoc]
      have hn : (Tm E ℓ).map σ₃.op ((Tm E ℓ).map σ₂.op n) =
          (Tm E ℓ).map (σ₃ ≫ σ₂).op n := CodeAssignment.map_tm_comp n σ₂ σ₃
      refine Or.inr (Or.inl ⟨c, (hg.pullback σ₃).cast hcode rfl hn, ?_⟩)
      have hmem : ((F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (X.pullback σ₂)
          hg).pullback σ₃).mem (𝟙 _) (reindex σ₃ y) := by
        simpa using (F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (X.pullback σ₂)
          hg).natural (𝟙 _) σ₃ y hy
      rwa [F.pullback_indBody _ _ hg σ₃ (hg.pullback σ₃),
        F.indBody_congr hcode rfl hn
          (show ((ctorTypes c).pullback (σ₂ ≫ σ₁)).pullback σ₃ =
            (ctorTypes c).pullback ((σ₃ ≫ σ₂) ≫ σ₁) by
            rw [ΩIdeal.pullback_pullback, Category.assoc])
          (ΩIdeal.pullback_pullback X σ₂ σ₃) (hg.pullback σ₃)
          ((hg.pullback σ₃).cast hcode rfl hn)] at hmem
    · refine Or.inr (Or.inr ⟨hns, ?_⟩)
      have hmem : ((indIdeal code.toIndHead (X.pullback σ₂)).pullback σ₃).mem (𝟙 _)
          (reindex σ₃ y) := by
        simpa using (indIdeal code.toIndHead (X.pullback σ₂)).natural (𝟙 _) σ₃ y hy
      rwa [show (indIdeal code.toIndHead (X.pullback σ₂)).pullback σ₃ =
          indIdeal code.toIndHead (X.pullback (σ₃ ≫ σ₂)) from
        Subtype.val_injective (by
          rw [← ΩIdeal.pullback_pullback]
          exact RawValue.pullback_indProjection _ _ _)] at hmem
  val.bottom _ := Or.inl bot_le
  val.lower σ₂ hab := by
    rintro (hb | ⟨c, hg, hb⟩ | ⟨hns, hb⟩)
    · exact Or.inl (hab.trans hb)
    · exact Or.inr (Or.inl ⟨c, hg, (F.indBody _ _ hg).lower (𝟙 _) hab hb⟩)
    · exact Or.inr (Or.inr ⟨hns, (indIdeal code.toIndHead _).lower (𝟙 _) hab hb⟩)
  property := by
    rintro Γ₃ σ₂ a b (ha | ⟨ca, hga, ha⟩ | ⟨hnsa, ha⟩) hb
    · exact ⟨b, hb, ha.trans bot_le, le_rfl⟩
    · rcases hb with hb | ⟨cb, hgb, hb⟩ | ⟨hnsb, hb⟩
      · exact ⟨a, Or.inr (Or.inl ⟨ca, hga, ha⟩), le_rfl, hb.trans bot_le⟩
      · obtain rfl := hga.witness.struct.ctor_unique cb
        have ⟨w, hw, haw, hbw⟩ := (F.indBody _ _ hga).property (𝟙 _) ha hb
        exact ⟨w, Or.inr (Or.inl ⟨_, hga, hw⟩), haw, hbw⟩
      · exact absurd hga.witness.struct (hnsb ca)
    · rcases hb with hb | ⟨cb, hgb, hb⟩ | ⟨hnsb, hb⟩
      · exact ⟨a, Or.inr (Or.inr ⟨hnsa, ha⟩), le_rfl, hb.trans bot_le⟩
      · exact absurd hgb.witness.struct (hnsa cb)
      · have ⟨w, hw, haw, hbw⟩ := (indIdeal code.toIndHead (X.pullback σ₂)).property (𝟙 _) ha hb
        exact ⟨w, Or.inr (Or.inr ⟨hnsa, hw⟩), haw, hbw⟩

theorem pullback_indRebuild (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (n : Tm_ Γ₂) (X : Domain Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) :
    (F.indRebuild code ctorTypes σ₁ n X).pullback σ₂ =
      F.indRebuild code ctorTypes (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op n) (X.pullback σ₂) := by
  apply ΩIdeal.ext
  intro Γ₄ σ₃ y
  rw [ΩIdeal.presheaf_map_mem]
  dsimp only [indRebuild, ΩIdeal.mem]
  rw [Category.assoc, CodeAssignment.map_tm_comp, ΩIdeal.pullback_pullback]

theorem projIdeal_indBody (T X : Domain Γ₁)
    (hg : code.StructGuard c n) (i : Fin (code.ctorHead c).arity) :
    projIdeal (code.ctorHead c) i (F.indBody T X hg) =
      (F.telescope T (indNames hg) fun j => projIdeal (code.ctorHead c) j X).1 i :=
  Subtype.val_injective (RawValue.proj_ctor _ _ _ i)

theorem indBody_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent) (T X : Domain Γ₁)
    (hg : code.StructGuard c n) :
    F.indBody T (F.indBody T X hg) hg = F.indBody T X hg := by
  have hfields := funext fun i => F.projIdeal_indBody T X hg i
  conv_lhs => rw [indBody, hfields, telescope_idempotent hF]
  rfl

theorem indRebuild_eq_indBody (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (n : Tm_ Γ₂) (X : Domain Γ₂) {c : Fin code.toIndHead.nctors}
    (hg : (code.map ((Tm E ℓ).map σ₁.op)).StructGuard c n) :
    F.indRebuild code ctorTypes σ₁ n X = F.indBody ((ctorTypes c).pullback σ₁) X hg := by
  apply ΩIdeal.ext
  intro Γ₃ σ₂ y
  have hcode : (code.map ((Tm E ℓ).map σ₁.op)).map ((Tm E ℓ).map σ₂.op) =
      code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op) :=
    (IndCode.map_comp_hom σ₁ σ₂ code).symm
  have hgσ : (code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op)).StructGuard c
      ((Tm E ℓ).map σ₂.op n) := (hg.pullback σ₂).cast hcode rfl rfl
  have hbody : (F.indBody ((ctorTypes c).pullback σ₁) X hg).pullback σ₂ =
      F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (X.pullback σ₂) hgσ := by
    rw [F.pullback_indBody _ _ hg σ₂ (hg.pullback σ₂)]
    exact F.indBody_congr hcode rfl rfl (ΩIdeal.pullback_pullback (ctorTypes c) σ₁ σ₂) rfl _ _
  constructor
  · rintro (hy | ⟨c', hg', hy⟩ | ⟨hns, _⟩)
    · exact (F.indBody _ _ hg).lower σ₂ hy ((F.indBody _ _ hg).bottom σ₂)
    · obtain rfl := hg.witness.struct.ctor_unique c'
      rwa [← ΩIdeal.presheaf_map_mem_id _ σ₂, hbody]
    · exact absurd hg.witness.struct (hns c)
  · intro hy
    refine Or.inr (Or.inl ⟨c, hgσ, ?_⟩)
    rwa [← hbody, ΩIdeal.presheaf_map_mem_id]

theorem indRebuild_eq_indIdeal (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (n : Tm_ Γ₂) (X : Domain Γ₂)
    (hns : ∀ c : Fin code.toIndHead.nctors, ¬ (E.get code.η).block.IsStructure code.s c) :
    F.indRebuild code ctorTypes σ₁ n X = indIdeal code.toIndHead X := by
  apply ΩIdeal.ext
  intro Γ₃ σ₂ y
  have hfilter : (indIdeal code.toIndHead X).pullback σ₂ =
      indIdeal code.toIndHead (X.pullback σ₂) :=
    Subtype.val_injective (RawValue.pullback_indProjection _ _ _)
  constructor
  · rintro (hy | ⟨c, hg, _⟩ | ⟨_, hy⟩)
    · exact (indIdeal _ X).lower σ₂ hy ((indIdeal _ X).bottom σ₂)
    · exact absurd hg.witness.struct (hns c)
    · rwa [← ΩIdeal.presheaf_map_mem_id _ σ₂]
  · intro hy
    refine Or.inr (Or.inr ⟨hns, ?_⟩)
    rwa [← hfilter, ΩIdeal.presheaf_map_mem_id]

theorem mem_indRebuild_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (n : Tm_ Γ₂) (X : Domain Γ₂) (y : CoherentShape Γ₂) :
    (F.indRebuild code ctorTypes σ n
        (F.indRebuild code ctorTypes σ n X)).mem (𝟙 Γ₂) y ↔
      (F.indRebuild code ctorTypes σ n X).mem (𝟙 Γ₂) y := by
  by_cases hguard : ∃ c : Fin code.toIndHead.nctors,
      (code.map ((Tm E ℓ).map σ.op)).StructGuard c n
  · have ⟨c, hg⟩ := hguard
    rw [F.indRebuild_eq_indBody code ctorTypes σ n _ hg,
      F.indRebuild_eq_indBody code ctorTypes σ n X hg, indBody_idempotent hF]
  by_cases hns : ∀ c : Fin code.toIndHead.nctors,
      ¬ (E.get code.η).block.IsStructure code.s c
  · rw [F.indRebuild_eq_indIdeal code ctorTypes σ n _ hns,
      F.indRebuild_eq_indIdeal code ctorTypes σ n X hns, indIdeal_idempotent]
  have hid : code.map ((Tm E ℓ).map (𝟙 Γ₂ ≫ σ).op) =
      code.map ((Tm E ℓ).map σ.op) := by rw [Category.id_comp]
  have hnid : (Tm E ℓ).map (𝟙 Γ₂).op n = n := by simp
  have hempty : ∀ Z : Domain Γ₂,
      (F.indRebuild code ctorTypes σ n Z).mem (𝟙 Γ₂) y ↔ y ≤ ⊥ := by
    intro Z
    constructor
    · rintro (hy | ⟨c, hg, _⟩ | ⟨hns', _⟩)
      · exact hy
      · exact absurd ⟨c, hg.cast hid rfl hnid⟩ hguard
      · exact absurd hns' hns
    · exact fun hy => Or.inl hy
  rw [hempty, hempty]

noncomputable def indAction (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) : IdealAction Γ₁ where
  val.app _ p := Preord.ofHom {
    toFun := F.indRebuild code ctorTypes p.1.unop p.2
    monotone' _ _ h := by
      rintro Γ₃ σ₂ y (hy | ⟨c, hg, hy⟩ | ⟨hns, hy⟩)
      · exact Or.inl hy
      · exact Or.inr (Or.inl ⟨c, hg,
          F.indBody_mono (fun _ _ h => h) (ΩIdeal.pullback_mono h σ₂) hg (𝟙 _) y hy⟩)
      · exact Or.inr (Or.inr ⟨hns, indIdeal_mono _ (ΩIdeal.pullback_mono h σ₂) (𝟙 _) y hy⟩) }
  val.naturality σ p := Preord.ext fun X =>
    (F.pullback_indRebuild code ctorTypes p.1.unop p.2 X σ.unop).symm
  property _ p := by
    rintro X y (hy | ⟨c, hg, hy⟩ | ⟨hns, hy⟩)
    · exact ⟨⊥, X.bottom (𝟙 _), Or.inl hy⟩
    · rw [ΩIdeal.pullback_id] at hy
      have ⟨x, hx, hy⟩ := F.indBody_finitary _ hg X hy
      refine ⟨x, hx, Or.inr (Or.inl ⟨c, hg, ?_⟩)⟩
      rwa [ΩIdeal.pullback_id]
    · rw [ΩIdeal.pullback_id] at hy
      have ⟨x, hx, hy⟩ := indIdeal_finitary code.toIndHead X hy
      refine ⟨x, hx, Or.inr (Or.inr ⟨hns, ?_⟩)⟩
      rwa [ΩIdeal.pullback_id]

theorem pullback_indAction (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (F.indAction code ctorTypes).pullback σ =
      F.indAction (code.map ((Tm E ℓ).map σ.op))
        fun c => (ctorTypes c).pullback σ := by
  ext Γ₃ p X
  refine ΩIdeal.ext fun σ₃ y => ?_
  have hcode : (code.map ((Tm E ℓ).map σ.op)).map
      ((Tm E ℓ).map (σ₃ ≫ p.1.unop).op) =
      code.map ((Tm E ℓ).map (σ₃ ≫ p.1.unop ≫ σ).op) := by
    rw [← IndCode.map_comp_hom, Category.assoc]
  have hT : ∀ c : Fin code.toIndHead.nctors,
      ((ctorTypes c).pullback σ).pullback (σ₃ ≫ p.1.unop) =
        (ctorTypes c).pullback (σ₃ ≫ p.1.unop ≫ σ) := by
    intro c
    rw [ΩIdeal.pullback_pullback, Category.assoc]
  change (F.indRebuild code ctorTypes (p.1.unop ≫ σ) p.2 X).mem σ₃ y ↔
    (F.indRebuild (code.map ((Tm E ℓ).map σ.op)) (fun c => (ctorTypes c).pullback σ)
      p.1.unop p.2 X).mem σ₃ y
  refine or_congr_right (or_congr_left (exists_congr fun c => ?_))
  constructor
  · rintro ⟨hg, hy⟩
    refine ⟨hg.cast hcode.symm rfl rfl, ?_⟩
    rwa [F.indBody_congr hcode.symm rfl rfl (hT c).symm rfl hg (hg.cast hcode.symm rfl rfl)] at hy
  · rintro ⟨hg, hy⟩
    refine ⟨hg.cast hcode rfl rfl, ?_⟩
    rwa [F.indBody_congr hcode rfl rfl (hT c) rfl hg (hg.cast hcode rfl rfl)] at hy

theorem indAction_isIdempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) :
    (F.indAction code ctorTypes).IsIdempotent := by
  intro Γ₂ σ₁ n X
  apply ΩIdeal.ext
  intro Γ₃ σ₂ y
  change (F.indRebuild code ctorTypes σ₁ n (F.indRebuild code ctorTypes σ₁ n X)).mem σ₂ y ↔
    (F.indRebuild code ctorTypes σ₁ n X).mem σ₂ y
  rw [← ΩIdeal.presheaf_map_mem_id _ σ₂, ← ΩIdeal.presheaf_map_mem_id _ σ₂, F.pullback_indRebuild,
    F.pullback_indRebuild]
  exact mem_indRebuild_idempotent hF code ctorTypes (σ₂ ≫ σ₁) _ _ y

theorem indAction_mono (code : IndCode Γ₁)
    {ctorTypes ctorTypes' : Fin code.toIndHead.nctors → Domain Γ₁}
    (h : ∀ c, ctorTypes c ≤ ctorTypes' c) :
    F.indAction code ctorTypes ≤ F.indAction code ctorTypes' := by
  rintro Γ₂ p X Γ₃ σ y (hy | ⟨c, hg, hy⟩ | ⟨hns, hy⟩)
  · exact Or.inl hy
  · exact Or.inr (Or.inl ⟨c, hg,
      F.indBody_mono (ΩIdeal.pullback_mono (h c) _) (fun _ _ h => h) hg (𝟙 _) y hy⟩)
  · exact Or.inr (Or.inr ⟨hns, hy⟩)

variable {F G : CodeAssignment E ℓ} {n : Nat}

theorem indAction_eq_of_rank
    (h : ∀ {Γ₂ : CtxCat E ℓ} (a : CoherentShape Γ₂), a.1.rank < n → F.app _ a = G.app _ a)
    (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ₁)
    (hr : ∀ c, (ctorTypes c).1.rank < n) :
    F.indAction code (fun c => principalIdeal (ctorTypes c)) =
      G.indAction code fun c => principalIdeal (ctorTypes c) := by
  ext Γ₂ p X
  apply ΩIdeal.ext
  intro Γ₃ σ y
  change (F.indRebuild code _ p.1.unop p.2 X).mem σ y ↔
    (G.indRebuild code _ p.1.unop p.2 X).mem σ y
  refine or_congr_right (or_congr_left (exists_congr fun c => exists_congr fun hg => ?_))
  have heq := telescope_eq_of_rank h ((principalIdeal (ctorTypes c)).pullback (σ ≫ p.1.unop))
    (fun _ σ₂ _ hb => ⟨_, by simpa using hr c, (principalIdeal_mem _ _ _).mpr le_rfl,
      (principalIdeal_mem _ _ _).mp hb⟩)
    (indNames hg) fun i => projIdeal (code.ctorHead c) i (X.pullback σ)
  change (ctorIdeal _ _ (F.telescope _ _ _).1).mem _ y ↔
    (ctorIdeal _ _ (G.telescope _ _ _).1).mem _ y
  rw [heq]

end CodeAssignment

end Metalean.CoherentShape
