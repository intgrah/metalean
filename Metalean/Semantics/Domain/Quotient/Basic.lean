module

public import Metalean.Semantics.Domain.Action

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

def quotAtom (code : QuotCode Γ₁) : CoherentShape Γ₁ := ⟨.quot code, .quot code⟩

@[simp] theorem reindex_quotAtom (σ : Γ₂ ⟶ Γ₁) (code : QuotCode Γ₁) :
    reindex σ (quotAtom code) = quotAtom (code.map ((Tm E ℓ).map σ.op)) := rfl

theorem quotAtom_le_iff {code code' : QuotCode Γ₁} : quotAtom code ≤ quotAtom code' ↔ code = code' := by
  constructor
  · intro h
    cases h with
    | collapse h => nomatch h
    | quot => rfl
  · rintro rfl
    exact le_rfl

def quotMkAtom (η : Head ζ .quot) (name : Tm_ Γ₁) (x : CoherentShape Γ₁) :
    CoherentShape Γ₁ := ⟨.quotMk η name x.val, .quotMk x.property⟩

theorem quotMkAtom_le_iff {η η' : Head ζ .quot} {name name' : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} :
    quotMkAtom η name x ≤ quotMkAtom η' name' y ↔ η = η' ∧ name = name' ∧ x ≤ y := by
  constructor
  · intro h
    cases h with
    | collapse h => nomatch h
    | quotMk h => exact ⟨rfl, rfl, h⟩
  · rintro ⟨rfl, rfl, h⟩
    exact .quotMk h

theorem quotMkAtom_upper {η : Head ζ .quot} {name : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} (h : quotMkAtom η name x ≤ y) :
    ∃ z : CoherentShape Γ₁, y = quotMkAtom η name z ∧ x ≤ z := by
  have ⟨y, hy⟩ := y
  cases h with
  | collapse h => nomatch h
  | quotMk h =>
    have .quotMk hy := hy
    exact ⟨⟨_, hy⟩, rfl, h⟩

@[simp] theorem reindex_quotMkAtom (η : Head ζ .quot) (name : Tm_ Γ₁)
    (x : CoherentShape Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    reindex σ (quotMkAtom η name x) =
      quotMkAtom η ((Tm E ℓ).map σ.op name) (reindex σ x) := rfl

def quotMap (η : Head ζ .quot) (x : CoherentShape Γ₁) : CoherentShape Γ₁ :=
  match x.val with
  | .quotMk η' _ _ => if η = η' then x else ⊥
  | _ => ⊥

theorem quotMap_le (η : Head ζ .quot) (x : CoherentShape Γ₁) : quotMap η x ≤ x := by
  cases x with | mk x hx =>
    cases x <;> simp [quotMap]
    split <;> simp

theorem quotMap_mono (η : Head ζ .quot) {x y : CoherentShape Γ₁} (h : x ≤ y) :
    quotMap η x ≤ quotMap η y := by
  have ⟨x, hx⟩ := x
  have ⟨y, hy⟩ := y
  cases h with
  | collapse h => cases h <;> exact bot_le
  | quotMk h =>
    dsimp [quotMap]
    split
    · exact .quotMk h
    · exact le_rfl
  | _ => exact le_rfl

@[simp] theorem quotMap_idempotent (η : Head ζ .quot) (x : CoherentShape Γ₁) :
    quotMap η (quotMap η x) = quotMap η x := by
  have ⟨x, hx⟩ := x
  cases x with
  | quotMk η' name value =>
    by_cases h : η = η' <;> simp [quotMap, h]
  | _ => rfl

@[simp] theorem quotMap_quotMkAtom (η : Head ζ .quot) (name : Tm_ Γ₁)
    (x : CoherentShape Γ₁) : quotMap η (quotMkAtom η name x) = quotMkAtom η name x := by
  simp [quotMap, quotMkAtom]

theorem reindex_quotMap (η : Head ζ .quot) (σ : Γ₂ ⟶ Γ₁) (x : CoherentShape Γ₁) :
    reindex σ (quotMap η x) = quotMap η (reindex σ x) := by
  have ⟨x, hx⟩ := x
  cases x with
  | quotMk η' name value =>
    change reindex σ (if η = η' then _ else ⊥) = if η = η' then _ else ⊥
    split <;> rfl
  | _ => rfl

noncomputable def quotHom (E : Env ζ) (ℓ : Nat) (η : Head ζ .quot) : order E ℓ ⟶ order E ℓ where
  app _ := Preord.ofHom ⟨quotMap η, fun _ _ h => quotMap_mono η h⟩
  naturality {_ _} σ := Preord.ext fun x => (reindex_quotMap η σ.unop x).symm

namespace RawValue

def quotMk (η : Head ζ .quot) (name : Tm_ Γ₁) (X : RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := ∃ x, X.mem σ x ∧ y ≤ quotMkAtom η ((Tm E ℓ).map σ.op name) x
  natural σ₁ σ₂ y := fun ⟨x, hx, hy⟩ =>
    ⟨reindex σ₂ x, X.natural σ₁ σ₂ x hx, by simpa using Le.reindex σ₂ hy⟩
  bottom σ := ⟨⊥, X.bottom σ, bot_le⟩
  lower σ hyz := fun ⟨x, hx, hz⟩ => ⟨x, hx, hyz.trans hz⟩

@[simp] theorem mem_quotMk (η : Head ζ .quot) (name : Tm_ Γ₁) (X : RawValue Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (quotMk η name X).mem σ y ↔
      ∃ x, X.mem σ x ∧ y ≤ quotMkAtom η ((Tm E ℓ).map σ.op name) x := Iff.rfl

theorem quotMk_mono (η : Head ζ .quot) (name : Tm_ Γ₁)
    {X Y : RawValue Γ₁} (h : X ≤ Y) : quotMk η name X ≤ quotMk η name Y :=
  fun σ _ ⟨x, hx, hy⟩ => ⟨x, h σ x hx, hy⟩

@[simp] theorem pullback_quotMk (η : Head ζ .quot) (name : Tm_ Γ₁)
    (X : RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (quotMk η name X).pullback σ₁ = quotMk η ((Tm E ℓ).map σ₁.op name) (X.pullback σ₁) := by
  ext Γ₃ σ₂ y
  simp [ΩLower.pullback]

theorem quotMk_isDirected (η : Head ζ .quot) (name : Tm_ Γ₁)
    {X : RawValue Γ₁} (hX : X.IsDirected) : (quotMk η name X).IsDirected := by
  intro Γ₂ σ a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
  have ⟨z, hz, hxz, hyz⟩ := hX σ hx hy
  exact ⟨quotMkAtom η _ z, ⟨z, hz, le_rfl⟩, ha.trans (.quotMk hxz), hb.trans (.quotMk hyz)⟩

noncomputable def quotProjection (η : Head ζ .quot) (X : RawValue Γ₁) : RawValue Γ₁ :=
  X.map (.ofNatTrans (quotHom E ℓ η))

@[simp] theorem mem_quotProjection (η : Head ζ .quot) (X : RawValue Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (X.quotProjection η).mem σ y ↔ ∃ x, X.mem σ x ∧ y ≤ quotMap η x :=
  ΩLower.mem_map (.ofNatTrans (quotHom E ℓ η)) X σ y

theorem quotProjection_le (η : Head ζ .quot) (X : RawValue Γ₁) : X.quotProjection η ≤ X := by
  intro Γ₂ σ y hy
  have ⟨x, hx, hy⟩ := (mem_quotProjection η X σ y).mp hy
  exact X.lower σ (hy.trans (quotMap_le η x)) hx

@[simp] theorem pullback_quotProjection (η : Head ζ .quot) (X : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (X.quotProjection η).pullback σ = quotProjection η (X.pullback σ) :=
  ΩLower.pullback_map (.ofNatTrans (quotHom E ℓ η)) X σ

@[simp] theorem quotProjection_idempotent (η : Head ζ .quot) (X : RawValue Γ₁) :
    (X.quotProjection η).quotProjection η = X.quotProjection η := by
  unfold quotProjection
  rw [ΩLower.map_map]
  congr 1
  ext Γ₂ σ x
  exact quotMap_idempotent η x

@[simp] theorem quotProjection_quotMk (η : Head ζ .quot) (name : Tm_ Γ₁)
    (X : RawValue Γ₁) : (quotMk η name X).quotProjection η = quotMk η name X := by
  apply le_antisymm
  · exact quotProjection_le η (quotMk η name X)
  intro Γ₂ σ y ⟨x, hx, hy⟩
  rw [mem_quotProjection]
  exact ⟨quotMkAtom η _ x, ⟨x, hx, le_rfl⟩, by simpa using hy⟩

end RawValue

noncomputable def quotIdeal (η : Head ζ .quot) (X : Domain Γ₁) : Domain Γ₁ :=
  ⟨RawValue.quotProjection η X.val, ΩLower.IsDirected.map _ X.property⟩

theorem quotIdeal_idempotent (η : Head ζ .quot) (X : Domain Γ₁) :
    quotIdeal η (quotIdeal η X) = quotIdeal η X :=
  Subtype.val_injective (RawValue.quotProjection_idempotent η X.val)

@[simp] theorem quotIdeal_bottom (η : Head ζ .quot) : quotIdeal η (⊥ : Domain Γ₁) = ⊥ :=
  le_antisymm (fun _ => RawValue.quotProjection_le η _) (@bot_le (Domain Γ₁) _ _ _)

@[simp] theorem quotIdeal_principal (η : Head ζ .quot) (x : CoherentShape Γ₁) :
    quotIdeal η (principalIdeal x) = principalIdeal (quotMap η x) :=
  Subtype.val_injective (ΩLower.map_principal (.ofNatTrans (quotHom E ℓ η)) x)

theorem quotIdeal_mono (η : Head ζ .quot) {X Y : Domain Γ₁} (h : X ≤ Y) :
    quotIdeal η X ≤ quotIdeal η Y :=
  fun σ _ ⟨x, hx, hy⟩ => ⟨x, h σ x hx, hy⟩

noncomputable def quotAction (η : Head ζ .quot) : IdealAction Γ₁ where
  val.app _ _ := Preord.ofHom ⟨quotIdeal η, fun _ _ h => quotIdeal_mono η h⟩
  val.naturality σ _ := Preord.ext fun X =>
    Subtype.val_injective (RawValue.pullback_quotProjection η X.val σ.unop).symm
  property _ _ _ _ := fun ⟨x, hx, hy⟩ => ⟨x, hx, x, (ΩLower.mem_principal_id _ _).mpr le_rfl, hy⟩

noncomputable def quotCodeAction (code : QuotCode Γ₁) : IdealAction Γ₁ :=
  match code.level.rel with
  | true => quotAction code.η
  | false => .bottom

end Metalean.CoherentShape
