module

public import Metalean.Semantics.Basis.Rank
public import Metalean.Semantics.Basis.Universe
public import Metalean.Semantics.Domain.Decoder.Pi
public import Metalean.Semantics.Domain.Inductive.Structure
public import Metalean.Semantics.Domain.Quotient.Basic
import Metalean.Semantics.Domain.Decoder.Locality

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

def universeIdeal (r : Bool) (X : Domain Γ₁) : Domain Γ₁ where
  val.mem σ a := X.mem σ a ∧ Shape.IsCode r a.1
  val.natural σ₁ σ₂ a := fun ⟨ha, hcode⟩ => ⟨X.natural σ₁ σ₂ a ha, hcode.map _ _⟩
  val.bottom σ := ⟨X.bottom σ, .bot⟩
  val.lower σ hab := fun ⟨hb, hcode⟩ => ⟨X.lower σ hab hb, hcode.of_le hab⟩
  property := by
    intro Γ₂ σ a b ⟨ha, hacode⟩ ⟨hb, hbcode⟩
    have ⟨c, hc, hac, hbc⟩ := X.property σ ha hb
    exact ⟨cSup a b ⟨c, hac, hbc⟩, ⟨X.lower σ (cSup_le _ hac hbc) hc,
      Shape.IsCode.cSup hacode hbcode⟩, le_cSup_left _ _ _, le_cSup_right _ _ _⟩

@[simp]
theorem mem_universeIdeal_iff (r : Bool) (X : Domain Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (universeIdeal r X).mem σ y ↔ X.mem σ y ∧ Shape.IsCode r y.1 :=
  Iff.rfl

theorem universeIdeal_le (r : Bool) (X : Domain Γ₁) : universeIdeal r X ≤ X :=
  fun _ _ hy => hy.1

@[simp]
theorem universeIdeal_bottom (r : Bool) : universeIdeal r (⊥ : Domain Γ₁) = ⊥ :=
  le_antisymm (fun {_} => universeIdeal_le r _) (@bot_le (Domain Γ₁) _ _ _)

theorem universeIdeal_idempotent (r : Bool) (X : Domain Γ₁) :
    universeIdeal r (universeIdeal r X) = universeIdeal r X :=
  le_antisymm (fun {_} => universeIdeal_le r _) fun _ {_} _ hy => ⟨hy, hy.2⟩

theorem universeIdeal_principal {r : Bool} {a : CoherentShape Γ₁} (h : Shape.IsCode r a.1) :
    universeIdeal r (principalIdeal a) = principalIdeal a :=
  le_antisymm (fun {_} => universeIdeal_le r _) fun _ {σ} y hy =>
    ⟨hy, Shape.IsCode.of_le ((principalIdeal_mem a σ y).mp hy) (h.map _ _)⟩

noncomputable def universeAction (r : Bool) : IdealAction Γ₁ where
  val.app _ _ := Preord.ofHom {
    toFun := universeIdeal r
    monotone' _ _ h := fun σ z ⟨hz, hcode⟩ => ⟨h σ z hz, hcode⟩ }
  val.naturality _ _ := rfl
  property _ _ _ z hz := ⟨z, hz.1, by simp, hz.2⟩

namespace CodeAssignment

noncomputable def piStepValue (F : CodeAssignment E ℓ) (a : Shape Γ₁) (h : Shape.IsCoherent Γ₁ a) :
    IdealAction Γ₁ :=
  match a with
  | .sort r => universeAction r.rel
  | .forallE label a k names ins outs =>
    F.piAction label (principalIdeal ⟨a, h.forallE_inv.1⟩)
      (graphAction ⟨⟨k, names, ins, outs⟩, h.forallE_inv.2⟩)
  | .ind code ctorTypes =>
    if code.rel then F.indAction code fun c => principalIdeal ⟨ctorTypes c, h.ind_inv c⟩
    else IdealAction.bottom
  | .quot code => quotCodeAction code
  | _ => IdealAction.bottom

theorem piStepValue_mono (F : CodeAssignment E ℓ) {a b : Shape Γ₁} (h : a ≤ b)
    (ha : Shape.IsCoherent Γ₁ a) (hb : Shape.IsCoherent Γ₁ b) :
    F.piStepValue a ha ≤ F.piStepValue b hb := by
  cases h with
  | collapse h => cases h <;> exact IdealAction.bottom_le _
  | forallE ha' hf =>
    refine F.piAction_mono _ (principalIdeal_mono ha') fun σ label X => application_mono
      (ΩIdeal.pullback_mono (principalIdeal_mono (CoherentGraph.lamGenerator_le_iff.mpr ?_)) σ)
      (@le_rfl _ _ _)
    exact hf
  | ind hc =>
    simp only [piStepValue]
    split_ifs
    · exact F.indAction_mono _ fun c => principalIdeal_mono (hc c)
    · exact le_rfl
  | _ => exact le_rfl

theorem piStepValue_reindex (F : CodeAssignment E ℓ) (a : Shape Γ₁) (ha : Shape.IsCoherent Γ₁ a)
    (σ : Γ₂ ⟶ Γ₁) :
    (F.piStepValue a ha).pullback σ =
      F.piStepValue (a.reindexHom σ) (ha.reindex σ) := by
  cases a with
  | forallE label a k names ins outs =>
    exact (F.pullback_piAction _ _ _ σ).trans (congrArg₂ (F.piAction _)
      (ΩIdeal.presheaf_map_principal _ σ) (pullback_graphAction _ σ))
  | ind code ctorTypes =>
    by_cases hrel : code.rel
    · simp only [piStepValue, Shape.reindexHom, Shape.map, IndCode.rel_map, hrel, ↓reduceIte,
        F.pullback_indAction]
      congr 1
      funext c
      exact Presheaf.ΩIdeal.presheaf_map_principal (R := pointedOrder E ℓ)
        ⟨ctorTypes c, ha.ind_inv c⟩ σ
    · simp only [piStepValue, Shape.reindexHom, Shape.map, IndCode.rel_map, hrel]
      rfl
  | quot code =>
    change (quotCodeAction code).pullback σ = quotCodeAction (code.map _)
    unfold quotCodeAction
    dsimp only [QuotCode.map]
    cases code.level.rel <;> rfl
  | _ => rfl

noncomputable def piStep (F : CodeAssignment E ℓ) : CodeAssignment E ℓ where
  app _ := Preord.ofHom {
    toFun a := F.piStepValue a.1 a.2
    monotone' a b h := F.piStepValue_mono h a.2 b.2 }
  naturality {_ _} σ := Preord.ext fun ⟨a, ha⟩ => (F.piStepValue_reindex a ha σ.unop).symm

end CodeAssignment

theorem application_bot (label : Tm_ Γ₁) (X : Domain Γ₁) :
    application (⊥ : Domain Γ₁) label X = ⊥ := by
  apply le_antisymm
  · intro Γ₂ σ y hy
    have ⟨x, _, hy⟩ := (CoherentShape.mem_application _ _ _ _ _).mp hy
    apply (ΩIdeal.mem_bot σ y).mpr
    apply hy.le_of_outputAtom
    rintro w ⟨f, i, hf, _, _, rfl⟩
    rw [ΩIdeal.pullback_bot, ΩIdeal.val_mem, ΩIdeal.mem_bot] at hf
    exact le_bot_iff.mpr (CoherentGraph.lamGenerator_le_bot_iff.mp hf i)
  · exact @bot_le (Domain _) _ _ _

theorem IdealAction.abstraction_eq_bottom (B : IdealAction Γ₁)
    (hB : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
      (X : Domain Γ₂), B.val.app _ (σ.op, label) X = (⊥ : Domain Γ₂)) :
    B.abstraction = ⊥ := by
  apply le_antisymm
  · intro Γ₂ σ y hy
    have ⟨⟨f, hcoh⟩, hf, hy⟩ := (IdealAction.mem_abstraction _ _ _).mp hy
    have houtputs : f.IsBottom := by
      intro i
      have h := hf i
      change (B.val.app _ (σ.op, f.names i) (principalIdeal (CoherentGraph.input ⟨f, hcoh⟩ i))).mem
        (𝟙 Γ₂) (CoherentGraph.output ⟨f, hcoh⟩ i) at h
      rw [hB, ΩIdeal.mem_bot] at h
      exact le_bot_iff.mp h
    exact (ΩIdeal.mem_bot σ y).mpr (hy.trans (CoherentGraph.lamGenerator_le_bot_iff.mpr houtputs))
  · exact @bot_le (Domain _) _ _ _

def IdealAction.IsStrict (P : IdealAction Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (n : Tm_ Γ₂),
    P.val.app _ (σ.op, n) (⊥ : Domain Γ₂) = (⊥ : Domain Γ₂)

namespace CodeAssignment

theorem rawExtend_nonbottom_code (F : CodeAssignment E ℓ)
    (hF : ∀ {Γ₁ : CtxCat E ℓ}, F.app _ (⊥ : CoherentShape Γ₁) = IdealAction.bottom)
    {T I : RawValue Γ₁} {n : Tm_ Γ₁} {σ : Γ₂ ⟶ Γ₁} {y : CoherentShape Γ₂}
    (hy : (F.rawExtend T n I).mem σ y) (hne : ¬ y ≤ ⊥) :
    ∃ c, T.mem σ c ∧ ¬ c ≤ ⊥ := by
  have ⟨c, hc, x, _, hy⟩ := (mem_rawExtend _ _ _ _ _ _).mp hy
  refine ⟨c, hc, fun hbot => hne ?_⟩
  have hy' := F.eval_mono_code hbot _ (principalIdeal x) (𝟙 Γ₂) y hy
  change ((F.app _ (⊥ : CoherentShape Γ₂)).val.app _ ((𝟙 Γ₂).op, _)
    (principalIdeal x)).mem (𝟙 Γ₂) y at hy'
  rw [hF] at hy'
  exact (ΩIdeal.mem_bot _ _).mp hy'

def IsPayloadStrict (F : CodeAssignment E ℓ) : Prop :=
  ∀ ⦃Γ₁ : CtxCat E ℓ⦄ (a : CoherentShape Γ₁), IdealAction.IsStrict (F.app _ a)

theorem rawExtend_bottom_payload {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict)
    (T : RawValue Γ₁) (n : Tm_ Γ₁) : F.rawExtend T n ⊥ = ⊥ := by
  apply le_antisymm
  · intro Γ₂ σ y
    simp_rw [mem_rawExtend]
    intro ⟨c, _, x, hx, hy⟩
    have hy' := F.eval_mono_payload c _ (Y := ⊥)
      (ΩLower.principal_mono hx) (𝟙 Γ₂) y hy
    change ((F.app _ c).val.app _ ((𝟙 Γ₂).op, _) (⊥ : Domain Γ₂)).mem (𝟙 Γ₂) y at hy'
    rwa [hF c, ΩIdeal.mem_bot] at hy'
  · intro Γ₂ σ y hy
    exact (F.rawExtend T n ⊥).lower σ ((ΩLower.mem_bot _ _).mp hy) ((F.rawExtend T n ⊥).bottom σ)

theorem extend_bottom_payload {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict)
    (T : Domain Γ₁) (n : Tm_ Γ₁) :
    F.extend T n (⊥ : Domain Γ₁) = ⊥ :=
  Subtype.val_injective (F.rawExtend_bottom_payload hF T.val n)

theorem telescope_bottom {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict) {k : Nat}
    (T : Domain Γ₁) (names : Fin k → Tm_ Γ₁) :
    (F.telescope T names fun _ => (⊥ : Domain Γ₁)).1 = fun _ => (⊥ : Domain Γ₁) := by
  induction k generalizing T with
  | zero => exact funext fun i => i.elim0
  | succ k ih =>
    unfold telescope
    rw [extend_bottom_payload hF]
    funext i
    exact Fin.cases rfl (congrFun (ih _ (Fin.tail names))) i

theorem indAction_isStrict {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict)
    (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → Domain Γ₁) :
    (F.indAction code ctorTypes).IsStrict := by
  intro Γ₂ σ₁ n
  apply le_antisymm
  · rintro Γ₃ σ₂ y (hy | ⟨c, hg, hy⟩ | ⟨hns, hy⟩)
    · exact (ΩIdeal.mem_bot _ _).mpr hy
    · have hbody : F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (⊥ : Domain Γ₃) hg =
          (⊥ : Domain Γ₃) := by
        simp only [indBody, projIdeal_bottom, telescope_bottom hF]
        exact ctorIdeal_bottom _ hg.witness.struct _
      rw [ΩIdeal.pullback_bot] at hy
      change (F.indBody ((ctorTypes c).pullback (σ₂ ≫ σ₁)) (⊥ : Domain Γ₃) hg).mem
        (𝟙 Γ₃) y at hy
      rw [hbody] at hy
      exact (ΩIdeal.mem_bot _ _).mpr ((ΩIdeal.mem_bot _ _).mp hy)
    · rw [ΩIdeal.pullback_bot, indIdeal_bottom] at hy
      exact (ΩIdeal.mem_bot _ _).mpr ((ΩIdeal.mem_bot _ _).mp hy)
  · exact @bot_le (Domain _) _ _ _

theorem piAction_isStrict {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict)
    (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁) :
    (F.piAction label A B).IsStrict := by
  intro Γ₂ σ₁ n
  apply IdealAction.abstraction_eq_bottom
  intro Γ₃ σ₂ m X
  apply le_antisymm
  · intro Γ₄ σ₃ z hz
    rcases hz with hz | ⟨h, hm, hz⟩
    · exact (ΩIdeal.mem_bot σ₃ z).mpr hz
    · rw [resultBody, ΩIdeal.pullback_bot, application_bot, ΩIdeal.pullback_bot,
        extend_bottom_payload hF] at hz
      exact (ΩIdeal.mem_bot σ₃ z).mpr ((ΩIdeal.mem_bot _ _).mp hz)
  · exact @bot_le (Domain _) _ _ _

theorem piStepValue_isIdempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (a : Shape Γ₁) (ha : Shape.IsCoherent Γ₁ a) : (F.piStepValue a ha).IsIdempotent := by
  cases a with
  | sort r => exact fun _ _ _ X => universeIdeal_idempotent r.rel X
  | forallE => exact piAction_isIdempotent hF _ _ _
  | ind code ctorTypes =>
    simp only [piStepValue]
    split_ifs
    · exact indAction_isIdempotent hF _ _
    · exact fun _ _ _ _ => rfl
  | quot code =>
    change (quotCodeAction code).IsIdempotent
    unfold quotCodeAction
    cases code.level.rel
    · exact fun _ _ _ _ => rfl
    · exact fun _ _ _ X => quotIdeal_idempotent _ X
  | _ => exact fun _ _ _ _ => rfl

theorem piStepValue_isStrict {F : CodeAssignment E ℓ} (hF : F.IsPayloadStrict)
    (a : Shape Γ₁) (ha : Shape.IsCoherent Γ₁ a) : (F.piStepValue a ha).IsStrict := by
  cases a with
  | sort r => exact fun _ _ _ => universeIdeal_bottom r.rel
  | forallE => exact piAction_isStrict hF _ _ _
  | ind code ctorTypes =>
    simp only [piStepValue]
    split_ifs
    · exact indAction_isStrict hF _ _
    · exact fun _ _ _ => rfl
  | quot code =>
    change (quotCodeAction code).IsStrict
    unfold quotCodeAction
    cases code.level.rel
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => quotIdeal_bottom _
  | _ => exact fun _ _ _ => rfl

noncomputable def piStage (E : Env ζ) (ℓ : Nat) : Nat → CodeAssignment E ℓ
  | 0 => bottom E ℓ
  | n + 1 => (piStage E ℓ n).piStep

theorem piStage_isIdempotent (n : Nat) : (piStage E ℓ n).IsIdempotent := by
  induction n with
  | zero => exact bottom_isIdempotent
  | succ n ih => exact fun _ ⟨a, ha⟩ => piStepValue_isIdempotent ih a ha

theorem piStage_isPayloadStrict (n : Nat) : (piStage E ℓ n).IsPayloadStrict := by
  induction n with
  | zero => exact fun _ _ _ _ _ => rfl
  | succ n ih => exact fun _ ⟨a, ha⟩ => piStepValue_isStrict ih a ha

theorem piStepValue_eq_of_rank {F G : CodeAssignment E ℓ} {n : Nat}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (b : CoherentShape Γ₂), b.1.rank < n → F.app _ b = G.app _ b)
    (a : Shape Γ₁) (ha : Shape.IsCoherent Γ₁ a) (hr : a.rank ≤ n) :
    F.piStepValue a ha = G.piStepValue a ha := by
  cases a with
  | forallE label a k names ins outs =>
    have hr' := Nat.lt_of_succ_le hr
    exact piAction_eq_of_rank h label ⟨a, ha.forallE_inv.1⟩
      ((le_max_left _ _).trans_lt hr') ⟨⟨k, names, ins, outs⟩, ha.forallE_inv.2⟩
      ((le_max_right _ _).trans_lt hr')
  | ind code ctorTypes =>
    simp only [piStepValue]
    split_ifs
    · exact indAction_eq_of_rank h code (fun c => ⟨ctorTypes c, ha.ind_inv c⟩)
        fun c => (Shape.rank_le_sup ctorTypes c).trans_lt (Nat.lt_of_succ_le hr)
    · rfl
  | _ => rfl

theorem piStage_value_stable (n : Nat) {Γ₁ : CtxCat E ℓ} : ∀ (a : CoherentShape Γ₁) {k l : Nat},
    a.1.rank ≤ n → n < k → n < l → (piStage E ℓ k).app _ a = (piStage E ℓ l).app _ a := by
  induction n using Nat.strong_induction_on generalizing Γ₁ with
  | h n ih =>
    rintro ⟨a, hcoh⟩ (_ | k) (_ | l) ha hk hl <;> simp_all only [Nat.not_lt_zero]
    exact piStepValue_eq_of_rank
      (fun ⟨b, hcoh⟩ hb => ih b.rank hb ⟨b, hcoh⟩ le_rfl
        (hb.trans_le (Nat.le_of_lt_succ hk)) (hb.trans_le (Nat.le_of_lt_succ hl))) a hcoh ha

noncomputable def piLimit (E : Env ζ) (ℓ : Nat) : CodeAssignment E ℓ where
  app _ := Preord.ofHom {
    toFun a := (piStage E ℓ (a.1.rank + 1)).app _ a
    monotone' a b hab := by
      let m := max a.1.rank b.1.rank + 1
      change (piStage E ℓ (a.1.rank + 1)).app _ a ≤ (piStage E ℓ (b.1.rank + 1)).app _ b
      rw [piStage_value_stable _ a le_rfl (Nat.lt_succ_self _) (show a.1.rank < m by omega),
        piStage_value_stable _ b le_rfl (Nat.lt_succ_self _) (show b.1.rank < m by omega)]
      exact ((piStage E ℓ m).app _).hom.monotone hab }
  naturality {Γ₁ Γ₂} σ := Preord.ext fun ⟨a, ha⟩ => by
    change (piStage E ℓ ((a.reindexHom σ.unop).rank + 1)).app Γ₂ (reindex σ.unop ⟨a, ha⟩) =
      (IdealAction.presheaf E ℓ).map σ ((piStage E ℓ (a.rank + 1)).app Γ₁ ⟨a, ha⟩)
    rw [Shape.rank_map]
    exact (piStage E ℓ (a.rank + 1)).app_reindex ⟨a, ha⟩ σ.unop

@[simp] theorem piLimit_app (a : CoherentShape Γ₁) :
    (piLimit E ℓ).app _ a = (piStage E ℓ (a.1.rank + 1)).app _ a := rfl

theorem piLimit_isIdempotent : (piLimit E ℓ).IsIdempotent :=
  fun _ ⟨a, ha⟩ => piStage_isIdempotent (a.rank + 1) ⟨a, ha⟩

theorem piLimit_isPayloadStrict : (piLimit E ℓ).IsPayloadStrict :=
  fun _ ⟨a, ha⟩ => piStage_isPayloadStrict (a.rank + 1) ⟨a, ha⟩

theorem piLimit_value_bottom : (piLimit E ℓ).app _ (⊥ : CoherentShape Γ₁) = IdealAction.bottom := rfl

end CodeAssignment

end Metalean.CoherentShape
