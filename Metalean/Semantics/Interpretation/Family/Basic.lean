/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.CategoryTheory.Functor.FunctorHom
public import Metalean.Order.Presheaf.Finitary
public import Metalean.Semantics.Basis.Join
public import Metalean.Semantics.Domain.Constructors
public import Metalean.Semantics.Domain.Decoder.Extension
import Mathlib.Algebra.GroupWithZero.Nat

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

open CategoryTheory MonoidalCategory Opposite Presheaf

abbrev RawValuation (Γ₁ : CtxCat E ℓ) := ℕ → RawValue Γ₁

namespace RawValuation

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

noncomputable def pullback (ρ : RawValuation Γ₁) (σ : Γ₂ ⟶ Γ₁) : RawValuation Γ₂ :=
  fun i ↦ (ρ i).pullback σ

def push (ρ : RawValuation Γ₁) (I : RawValue Γ₁) : RawValuation Γ₁
  | 0 => I
  | i + 1 => ρ i

def tail (ρ : RawValuation Γ₁) : RawValuation Γ₁ := fun i ↦ ρ (i + 1)

def replace (ρ : RawValuation Γ₁) (i : ℕ) (I : RawValue Γ₁) : RawValuation Γ₁ :=
  Function.update ρ i I

@[simp]
theorem replace_same (ρ : RawValuation Γ₁) (i : ℕ) (I : RawValue Γ₁) :
    (ρ.replace i I) i = I := by
  simp [replace]

@[simp]
theorem replace_ne (ρ : RawValuation Γ₁) {i j : ℕ} (h : j ≠ i) (I : RawValue Γ₁) :
    (ρ.replace i I) j = ρ j := by
  simp [replace, h]

@[simp]
theorem tail_push (ρ : RawValuation Γ₁) (I : RawValue Γ₁) : (ρ.push I).tail = ρ := rfl

@[simp]
theorem pullback_id (ρ : RawValuation Γ₁) : ρ.pullback (𝟙 Γ₁) = ρ :=
  funext fun i => ΩLower.pullback_id (ρ i)

theorem pullback_comp (ρ : RawValuation Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) :
    (ρ.pullback σ₁).pullback σ₂ = ρ.pullback (σ₂ ≫ σ₁) :=
  funext fun i => ΩLower.pullback_pullback (ρ i) σ₁ σ₂

@[simp]
theorem pullback_push (ρ : RawValuation Γ₁) (I : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (ρ.push I).pullback σ = (ρ.pullback σ).push (I.pullback σ) := by
  funext i
  cases i <;> rfl

@[simp]
theorem pullback_tail (ρ : RawValuation Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    ρ.tail.pullback σ = (ρ.pullback σ).tail := rfl

@[simp]
theorem replace_zero_push (ρ : RawValuation Γ₁) (I J : RawValue Γ₁) :
    (ρ.push J).replace 0 I = ρ.push I := by
  ext (_ | _) <;> simp!

@[simp]
theorem push_replace (ρ : RawValuation Γ₁) (i : ℕ) (I J : RawValue Γ₁) :
    (ρ.replace i I).push J = (ρ.push J).replace (i + 1) I := by
  funext j
  cases j <;> simp! [replace, Function.update_apply]

theorem pullback_mono {ρ ρ' : RawValuation Γ₁} (h : ρ ≤ ρ') (σ : Γ₂ ⟶ Γ₁) :
    ρ.pullback σ ≤ ρ'.pullback σ :=
  fun i ↦ ΩLower.pullback_mono (h i) σ

theorem push_mono {ρ ρ' : RawValuation Γ₁} {I I' : RawValue Γ₁}
    (hρ : ρ ≤ ρ') (hI : I ≤ I') : ρ.push I ≤ ρ'.push I'
  | 0 => hI
  | i + 1 => hρ i

def pushFin (ρ : RawValuation Γ₁) : {k : Nat} → (Fin k → RawValue Γ₁) → RawValuation Γ₁
  | 0, _ => ρ
  | _ + 1, v => (ρ.pushFin fun i => v i.castSucc).push (v (Fin.last _))

@[simp] theorem pushFin_snoc (ρ : RawValuation Γ₁) {k : Nat}
    (args : Fin k → RawValue Γ₁) (I : RawValue Γ₁) :
    ρ.pushFin (Fin.snoc args I) = (ρ.pushFin args).push I := by
  simp!

theorem pushFin_append (ρ : RawValuation Γ₁) {n k : Nat}
    (args : Fin n → RawValue Γ₁) (fields : Fin k → RawValue Γ₁) :
    ρ.pushFin (Fin.append args fields) = (ρ.pushFin args).pushFin fields := by
  induction k with
  | zero => simp!
  | succ k ih =>
    rw [← Fin.snoc_init_self fields, Fin.append_snoc, pushFin_snoc, pushFin_snoc, ih]

@[simp] theorem pushFin_variable (ρ : RawValuation Γ₁) {k : Nat}
    (args : Fin k → RawValue Γ₁) (v : Var k) : (ρ.pushFin args) v.db = args v := by
  induction k with
  | zero => exact v.elim0
  | succ k ih =>
    cases v using Fin.lastCases with
    | last => simp!
    | cast v => simpa! using ih (fun i => args i.castSucc) v

theorem pushFin_mono {ρ ρ' : RawValuation Γ₁} (hρ : ρ ≤ ρ') {k : Nat} {v v' : Fin k → RawValue Γ₁}
    (hv : ∀ i, v i ≤ v' i) : ρ.pushFin v ≤ ρ'.pushFin v' := by
  induction k with
  | zero => exact hρ
  | succ k ih => exact push_mono (ih fun i => hv i.castSucc) (hv (Fin.last k))

theorem pullback_pushFin (ρ : RawValuation Γ₁) (σ : Γ₂ ⟶ Γ₁) {k : Nat} (v : Fin k → RawValue Γ₁) :
    (ρ.pushFin v).pullback σ = (ρ.pullback σ).pushFin fun i => (v i).pullback σ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pushFin, pushFin, pullback_push, ih]

theorem replace_mono {ρ ρ' : RawValuation Γ₁} {I I' : RawValue Γ₁} (i : ℕ)
    (hρ : ρ ≤ ρ') (hI : I ≤ I') : ρ.replace i I ≤ ρ'.replace i I' :=
  update_le_update_iff.mpr ⟨hI, fun j _ => hρ j⟩

@[implicit_reducible, simps! obj map_hom_coe] noncomputable def presheaf (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ Preord where
  obj Γ₂ := Preord.of (RawValuation Γ₂.unop)
  map σ₁ := Preord.ofHom {
    toFun := fun ρ => ρ.pullback σ₁.unop
    monotone' := fun _ _ h => pullback_mono h σ₁.unop }
  map_id _ := Preord.ext pullback_id
  map_comp σ₁ σ₂ := Preord.ext fun ρ => (pullback_comp ρ σ₁.unop σ₂.unop).symm

end RawValuation

abbrev RawFamily (Γ₁ : CtxCat E ℓ) : Type :=
  Functor.HomObj (RawValuation.presheaf E ℓ) (ΩLower.presheaf (pointedOrder E ℓ))
    (coyoneda.obj (op (op Γ₁)))

namespace RawFamily

noncomputable abbrev presheaf (E : Env ζ) (ℓ : Nat) := Functor.HomObj.functor (RawValuation.presheaf E ℓ) (ΩLower.presheaf (pointedOrder E ℓ))

noncomputable def pullback {Γ₁ Γ₂ : CtxCat E ℓ} (F : RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁) : RawFamily Γ₂ :=
  F.map (coyoneda.map σ.op.op)

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

@[simp] theorem app_pullback (F : RawFamily Γ₁) {Γ₂ : (CtxCat E ℓ)ᵒᵖ} {Γ₃ : CtxCat E ℓ}
    (σ₁ : op Γ₁ ⟶ Γ₂) (σ₂ : Γ₃ ⟶ Γ₂.unop) (ρ : RawValuation Γ₂.unop) :
    (F.app Γ₂ σ₁ ρ).pullback σ₂ =
      F.app (op Γ₃) (σ₁ ≫ σ₂.op) (ρ.pullback σ₂) :=
  (F.naturality_apply σ₂.op σ₁ ρ).symm

def IsFinitary (F : RawFamily Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (i : ℕ) (ρ : RawValuation Γ₂),
    ΩLower.IsFinitary fun I => F.app _ σ.op (ρ.replace i I)

theorem IsFinitary.eventually {F : RawFamily Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (i : ℕ) (ρ : RawValuation Γ₂) (I : RawValue Γ₂)
    {y : CoherentShape Γ₂} (hy : (y ∈ (F.app _ σ.op (ρ.replace i I)).app (𝟙 Γ₂))) :
    ∀ᶠ J in I.approximations, (y ∈ (F.app _ σ.op (ρ.replace i J)).app (𝟙 Γ₂)) :=
  (hF σ i ρ).eventually
    ((F.app _ σ.op).hom.monotone.comp (Function.update_mono (f := ρ) (i := i)))
    ΩLower.eventually_mem hy

@[simps! app_hom_coe] noncomputable def lookup (i : ℕ) : RawFamily Γ₁ where
  app _ _ := Preord.ofHom (Pi.evalOrderHom i)
  naturality _ _ := rfl

@[simps! app_hom_coe] noncomputable def constant (I : RawValue Γ₁) : RawFamily Γ₁ where
  app _ σ₁ := Preord.ofHom (OrderHom.const _ (I.pullback σ₁.unop))
  naturality σ₂ σ₁ := Preord.ext fun _ =>
    (ΩLower.pullback_pullback I σ₁.unop σ₂.unop).symm

theorem bottom_isFinitary : (⊥ : RawFamily Γ₁).IsFinitary :=
  fun _ _ _ _ => ΩLower.IsFinitary.const _

theorem constant_isFinitary (I : RawValue Γ₁) : (constant I).IsFinitary :=
  fun _ _ _ _ => ΩLower.IsFinitary.const _

theorem IsFinitary.pullback {F : RawFamily Γ₁} (hF : F.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) : IsFinitary ((presheaf E ℓ).map σ₁.op F) :=
  fun _ σ₂ => hF (σ₂ ≫ σ₁)

theorem lookup_isFinitary (i : ℕ) : (lookup i : RawFamily Γ₁).IsFinitary := by
  intro Γ₂ σ j ρ
  change ΩLower.IsFinitary fun I => (ρ.replace j I) i
  by_cases h : i = j
  · subst j
    simpa using ΩLower.IsFinitary.id
  · simpa [h] using ΩLower.IsFinitary.const (ρ i)

theorem iSup_eq {ι : Sort*} {F : ι → RawFamily Γ₁} (j : ι) {X : RawFamily Γ₁}
    (h : ∀ i, F i = X) : ⨆ i, F i = X :=
  le_antisymm (iSup_le fun i => (h i).le) (by rw [← h j]; exact le_iSup F j)

theorem mem_iSup_app {ι : Sort*} (F : ι → RawFamily Γ₁) {X : (CtxCat E ℓ)ᵒᵖ}
    (σ₁ : Opposite.op Γ₁ ⟶ X) (ρ : RawValuation X.unop) {Y : CtxCat E ℓ} (σ₂ : Y ⟶ X.unop)
    (y : CoherentShape Y) :
    (y ∈ ((⨆ i, F i).app X σ₁ ρ).app σ₂) ↔ y ≤ ⊥ ∨ ∃ i, (y ∈ ((F i).app X σ₁ ρ).app σ₂) := by
  rw [ΩLower.homObj_iSup_app, ΩLower.mem_iSup]

theorem IsFinitary.iSup {ι : Sort*} {F : ι → RawFamily Γ₁}
    (hF : ∀ i, (F i).IsFinitary) : (⨆ i, F i).IsFinitary := by
  intro Γ₂ σ j ρ I y hy
  rcases (mem_iSup_app F σ.op _ (𝟙 Γ₂) y).mp hy with hy | ⟨i, hy⟩
  · exact ⟨∅, by simp, (mem_iSup_app F σ.op _ (𝟙 Γ₂) y).mpr (Or.inl hy)⟩
  · have ⟨l, hl, hy⟩ := hF i σ j ρ I hy
    exact ⟨l, hl, (mem_iSup_app F σ.op _ (𝟙 Γ₂) y).mpr (Or.inr ⟨i, hy⟩)⟩

noncomputable def sort (r : Level ℓ) : RawFamily Γ₁ :=
  constant (principalIdeal (sortAtom r)).val

@[simp]
theorem sort_value (r : Level ℓ) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (sort r).app _ σ.op ρ = (principalIdeal (sortAtom r : CoherentShape Γ₂)).val :=
  ΩLower.presheaf_map_principal (R := pointedOrder E ℓ) (sortAtom r) σ

theorem sort_isFinitary (r : Level ℓ) : (sort r : RawFamily Γ₁).IsFinitary :=
  constant_isFinitary _

noncomputable def decode (D : CodeAssignment E ℓ) (n : Tm_ Γ₁) (C X : RawFamily Γ₁) :
    RawFamily Γ₁ :=
  (C.pair X).comp (D.rawExtendHom.map (coyonedaEquiv.symm n))

@[simp] theorem decode_app_hom_coe (D : CodeAssignment E ℓ) (n : Tm_ Γ₁)
    (C X : RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (decode D n C X).app _ σ.op ρ =
      D.rawExtend (C.app _ σ.op ρ) ((Tm E ℓ).map σ.op n) (X.app _ σ.op ρ) := rfl

theorem IsFinitary.decode (D : CodeAssignment E ℓ) {n : Tm_ Γ₁} {C X : RawFamily Γ₁}
    (hC : C.IsFinitary) (hX : X.IsFinitary) : (decode D n C X).IsFinitary := by
  intro Γ₂ σ i ρ
  exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
    D.rawExtend_eventually _ (hC.eventually σ i ρ I) (hX.eventually σ i ρ I) hy

end RawFamily

namespace RawValuation

def tailN (ρ : RawValuation Γ₁) : Nat → RawValuation Γ₁
  | 0 => ρ
  | k + 1 => (ρ.tailN k).tail

theorem tailN_apply (ρ : RawValuation Γ₁) (k j : Nat) : ρ.tailN k j = ρ (j + k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    change ρ.tailN k (j + 1) = _
    rw [ih]
    congr 1
    omega

@[simp] theorem tailN_tailN (ρ : RawValuation Γ₁) (k j : Nat) :
    (ρ.tailN k).tailN j = ρ.tailN (k + j) := by
  funext i
  simp [tailN_apply, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem pushFin_tailN (ρ : RawValuation Γ₁) (k : Nat) :
    (ρ.tailN k).pushFin (fun i : Var k => ρ i.db) = ρ := by
  induction k generalizing ρ with
  | zero => rfl
  | succ k ih =>
    have htail : ρ.tail.tailN k = ρ.tailN (k + 1) :=
      (tailN_tailN ρ 1 k).trans (congrArg ρ.tailN (Nat.add_comm 1 k))
    simp [pushFin, ← htail]
    change ((ρ.tail.tailN k).pushFin fun i : Var k => ρ.tail i.db).push (ρ 0) = ρ
    rw [ih]
    funext i
    cases i <;> rfl

end RawValuation

namespace RawFamily

theorem IsFinitary.head {F : RawFamily Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    ΩLower.IsFinitary fun I => F.app _ σ.op (ρ.push I) := by
  simpa using hF σ 0 (ρ.push ⊥)

theorem IsFinitary.compose_value {Γ₃ : CtxCat E ℓ} {B : RawFamily Γ₃}
    (hB : B.IsFinitary) {X : RawFamily Γ₁} (hX : X.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (σ₃ : Γ₂ ⟶ Γ₃) (i : ℕ) (ρ : RawValuation Γ₂) :
    ΩLower.IsFinitary fun I => B.app _ σ₃.op
      ((ρ.replace i I).push (X.app _ σ₁.op (ρ.replace i I))) :=
  ΩLower.IsFinitary.apply
    (fun J => by simpa using hB σ₃ (i + 1) (ρ.push J))
    (fun J => hB.head σ₃ (ρ.replace i J)) (hX σ₁ i ρ)
    (fun _ _ h J => (B.app _ σ₃.op).hom.monotone
      (RawValuation.push_mono (RawValuation.replace_mono i le_rfl h) fun _ _ hx => hx))
    (fun J _ _ h => (B.app _ σ₃.op).hom.monotone (RawValuation.push_mono le_rfl h))
    ((X.app _ σ₁.op).hom.monotone.comp (Function.update_mono (f := ρ)))

end RawFamily

noncomputable abbrev RawAction.presheaf (E : Env ζ) (ℓ : Nat) := Functor.parameterizedHom
  (ΩLower.presheaf (pointedOrder E ℓ)) (ΩLower.presheaf (pointedOrder E ℓ)) (Tm E ℓ)

abbrev RawAction (Γ₁ : CtxCat E ℓ) : Type := (RawAction.presheaf E ℓ).obj (op Γ₁)

noncomputable def RawAction.pullback {Γ₁ Γ₂ : CtxCat E ℓ} (F : RawAction Γ₁) (σ : Γ₂ ⟶ Γ₁) : RawAction Γ₂ :=
  (RawAction.presheaf E ℓ).map σ.op F

namespace RawAction

@[simp] theorem app_pullback {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} (F : RawAction Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label : Tm_ Γ₂) (I : RawValue Γ₂) :
    F.app _ (σ₁ ≫ σ₂.op, (Tm E ℓ).map σ₂.op label) (I.pullback σ₂) = ((F.app _ (σ₁, label) I).pullback σ₂) :=
  F.naturality_apply σ₂.op (σ₁, label) I

@[simp] theorem map_iSup {ι : Sort*} {X Y : (CtxCat E ℓ)ᵒᵖ} (f : X ⟶ Y)
    (F : ι → RawAction X.unop) :
    (presheaf E ℓ).map f (⨆ i, F i) = ⨆ i, (presheaf E ℓ).map f (F i) := by
  apply Functor.HomObj.ext_app
  intro Z p I
  change (⨆ i, F i).app Z (f ≫ p.1, p.2) I = (⨆ i, (presheaf E ℓ).map f (F i)).app Z p I
  rw [ΩLower.homObj_iSup_app, ΩLower.homObj_iSup_app]
  exact iSup_congr fun _ => rfl

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {G : RawAction Γ₁}

def IsFinitary (F : RawAction Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂),
    ΩLower.IsFinitary (F.app _ (σ.op, label))

def IsIdealValued (F : RawAction Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
    (I : Domain Γ₂), (F.app _ (σ.op, label) I.val).IsDirected

theorem IsFinitary.exists_principal {F : RawAction Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂) (I : Domain Γ₂)
    {y : CoherentShape Γ₂} (hy : (y ∈ (F.app _ (σ.op, label) I.val).app (𝟙 Γ₂))) :
    ∃ x, (x ∈ I.app (𝟙 Γ₂)) ∧
      (y ∈ (F.app _ (σ.op, label) (ΩLower.principal (pointedOrder E ℓ) x)).app (𝟙 Γ₂)) :=
  (hF σ label).exists_principal (F.app _ (σ.op, label)).hom.monotone I.property hy

theorem IsFinitary.pullback {F : RawAction Γ₁} (hF : F.IsFinitary) (σ₁ : Γ₂ ⟶ Γ₁) :
    IsFinitary ((presheaf E ℓ).map σ₁.op F) :=
  fun _ σ₂ => hF (σ₂ ≫ σ₁)

theorem IsIdealValued.pullback {F : RawAction Γ₁} (hF : F.IsIdealValued) (σ₁ : Γ₂ ⟶ Γ₁) :
    IsIdealValued ((presheaf E ℓ).map σ₁.op F) :=
  fun _ σ₂ => hF (σ₂ ≫ σ₁)

noncomputable def onBasis (F : RawAction Γ₁) : BasisAction Γ₁ where
  app X p := (ΩLower.principalNatTrans (pointedOrder E ℓ)).app X ≫ F.app X p
  naturality g p := Preord.ext fun x => by
    change F.app _ (p.1 ≫ g, (Tm E ℓ).map g p.2) (ΩLower.principal (pointedOrder E ℓ) (reindex g.unop x)) =
      (F.app _ p (ΩLower.principal (pointedOrder E ℓ) x)).pullback g.unop
    simpa using F.app_pullback p.1 g.unop p.2 (ΩLower.principal (pointedOrder E ℓ) x)

abbrev GraphValid (F : RawAction Γ₁) (σ : Γ₂ ⟶ Γ₁) (f : CoherentGraph Γ₂) : Prop :=
  F.onBasis.GraphValid σ f

theorem GraphValid.mono {F : RawAction Γ₁} (hFG : F ≤ G) {σ : Γ₂ ⟶ Γ₁}
    {f : CoherentGraph Γ₂} (hf : GraphValid F σ f) : GraphValid G σ f :=
  BasisAction.GraphValid.mono (fun Γ₃ p x => hFG Γ₃ p (ΩLower.principal (pointedOrder E ℓ) x)) hf

noncomputable abbrev abstraction (F : RawAction Γ₁) : RawValue Γ₁ := F.onBasis.abstraction

@[simp]
theorem pullback_abstraction (F : RawAction Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    F.abstraction.pullback σ = abstraction ((presheaf E ℓ).map σ.op F) :=
  BasisAction.pullback_abstraction F.onBasis σ

theorem abstraction_mono {F : RawAction Γ₁} (h : F ≤ G) : F.abstraction ≤ G.abstraction :=
  BasisAction.abstraction_mono fun Γ₂ p x => h Γ₂ p (ΩLower.principal (pointedOrder E ℓ) x)

noncomputable def abstractionHom (E : Env ζ) (ℓ : Nat) : presheaf E ℓ ⟶ ΩLower.presheaf (pointedOrder E ℓ) where
  app _ := Preord.ofHom { toFun := abstraction, monotone' := fun _ _ => abstraction_mono }
  naturality _ _ σ := Preord.ext fun F => (pullback_abstraction F σ.unop).symm

theorem onBasis_eq_of_eq_on_ideals {F : RawAction Γ₁}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
    (I : Domain Γ₂),
    F.app _ (σ.op, label) I.val = G.app _ (σ.op, label) I.val) : F.onBasis = G.onBasis := by
  ext _ ⟨⟨σ⟩, label⟩ x
  exact h σ label (principalIdeal x)

theorem abstraction_eq_of_eq_on_ideals {F : RawAction Γ₁}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
    (I : Domain Γ₂),
    F.app _ (σ.op, label) I.val = G.app _ (σ.op, label) I.val) : F.abstraction = G.abstraction :=
  congrArg BasisAction.abstraction (onBasis_eq_of_eq_on_ideals h)

theorem abstraction_eq_of_ideal_values (F : RawAction Γ₁) (K : IdealAction Γ₁)
    (h : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (name : Tm_ Γ₂)
      (X : Domain Γ₂),
      F.app _ (σ.op, name) X.val = (K.val.app _ (σ.op, name) X).val) :
    F.abstraction = (IdealAction.abstraction K).val :=
  congrArg BasisAction.abstraction
    (by ext _ ⟨⟨σ⟩, label⟩ x; exact h σ label (principalIdeal x))

noncomputable def toIdealAction (F : RawAction Γ₁) (hF : F.IsFinitary) (hD : F.IsIdealValued) :
    IdealAction Γ₁ where
  val.app _ := fun (σ₁, label) => Preord.ofHom {
    toFun I := (F.app _ (σ₁, label) I.val).toIdeal (hD σ₁.unop label I)
    monotone' _ _ h := (F.app _ (σ₁, label)).hom.monotone h }
  val.naturality σ₂ := fun ⟨σ₁, label⟩ => Preord.ext fun I =>
    Subtype.val_injective <| F.app_pullback σ₁ σ₂.unop label I.val
  property _ a := hF.exists_principal a.1.unop a.2

@[simp]
theorem toIdealAction_value_toLower (F : RawAction Γ₁) (hF : F.IsFinitary)
    (hD : F.IsIdealValued) (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
    (I : Domain Γ₂) :
    ((F.toIdealAction hF hD).val.app _ (σ.op, label) I).val = F.app _ (σ.op, label) I.val := rfl

theorem abstraction_isDirected (F : RawAction Γ₁) (hD : F.IsIdealValued) :
    F.abstraction.IsDirected :=
  BasisAction.abstraction_isDirected fun _ σ label x => hD σ label (principalIdeal x)

end RawAction

end Metalean.CoherentShape
