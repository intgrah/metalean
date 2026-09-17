module

public import Metalean.TypeTheory.Syntactic.Pi.Term
public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Domain.Pi
public import Metalean.Semantics.Interpretation.Binder.Basic
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Interpretation.Binder.Support

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory MonoidalCategory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

section Pi

variable {Γ₁ Γ₂ Γ₃ ΓA : CtxCat E ℓ} (D : CodeAssignment E ℓ)

noncomputable abbrev rawPi (label : Ty.Pair Γ₁) (A : RawValue Γ₁) (B : RawAction Γ₁) : RawValue Γ₁ :=
  BasisAction.pi label A B.onBasis

theorem rawPi_toIdealAction (label : Ty.Pair Γ₁)
    (A : Domain Γ₁) (B : RawAction Γ₁)
    (hB : B.IsFinitary) (hD : B.IsIdealValued) :
    rawPi label A.val B = (pi label A (B.toIdealAction hB hD)).val :=
  rfl

theorem rawPi_isDirected (label : Ty.Pair Γ₁) {A : RawValue Γ₁}
    (B : RawAction Γ₁) (hA : A.IsDirected) (hD : B.IsIdealValued) :
    (rawPi label A B).IsDirected :=
  BasisAction.pi_isDirected label A B.onBasis hA
    fun _ σ label x => hD σ label (principalIdeal x)

noncomputable def rawPiHom (E : Env ζ) (ℓ : Nat) : Functor.HomObj (ΩLower.presheaf (pointedOrder E ℓ) ⊗ (RawAction.presheaf E ℓ))
    (ΩLower.presheaf (pointedOrder E ℓ)) (Ty.pairPresheaf E ℓ) where
  app _ label := Preord.ofHom {
    toFun := fun (A, B) => rawPi label A B
    monotone' := fun _ _ ⟨hA, hB⟩ {_} σ _ ⟨a, f, ha, hf, hq⟩ =>
      ⟨a, f, hA σ a ha, RawAction.GraphValid.mono hB hf, hq⟩ }
  naturality σ label := Preord.ext fun (A, B) => (BasisAction.pullback_pi label A B.onBasis σ.unop).symm

namespace RawFamily

noncomputable def pi
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (label : Ty.Pair Γ₁)
    (C : RawFamily Γ₁) (B : RawFamily ΓA) : RawFamily Γ₁ :=
  (C.pair (RawActionFamily.normalizedBody D hA C B)).comp
    ((rawPiHom E ℓ).map (coyonedaEquiv.symm label))

@[simp]
theorem pi_value
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (label : Ty.Pair Γ₁)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (pi D hA label C B).app _ σ.op ρ =
      rawPi ((Ty.pairPresheaf E ℓ).map σ.op label) (C.app _ σ.op ρ)
        (normalizedBodyAction D hA C B σ ρ) := rfl

theorem IsFinitary.pi
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (label : Ty.Pair Γ₁)
    {C : RawFamily Γ₁} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (pi D hA label C B).IsFinitary := by
  intro Γ₂ σ i ρ
  apply ΩLower.IsFinitary.of_eventually
  intro I q hq
  have ⟨a, f, ha, hf, hq⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hq
  filter_upwards [hC.eventually σ i ρ I ha,
    RawActionFamily.IsFinitary.graph_eventually
      (RawActionFamily.IsFinitary.normalizedBody D hA hC hB) σ i ρ I f hf]
    with J ha hf
  exact (BasisAction.mem_pi _ _ _ _ _).mpr ⟨a, f, ha, hf, hq⟩

@[simp]
theorem mem_piAtom_pi_value_iff
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (label : Ty.Pair Γ₁)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label' : Ty.Pair Γ₃) :
    ((pi D hA label C B).app _ σ₁.op ρ).mem σ₂ (piAtom label') ↔
      label' = (Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label := by
  rw [pi_value, BasisAction.mem_piAtom_pi_iff, op_comp, Functor.map_comp_apply]

end RawFamily

end Pi

section Support

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

namespace CodeAssignment

theorem piAction_fixed_of_rawExtend_rawPi (label : Ty.Pair Γ₁)
    (T : Domain Γ₁) (B : RawAction Γ₁) (hB : B.IsFinitary) (hD : B.IsIdealValued)
    (n : Tm_ Γ₁) {F : Domain Γ₁}
    (hF : (piLimit E ℓ).rawExtend (rawPi label T.val B) n F.val = F.val) :
    ((piLimit E ℓ).piAction label T (B.toIdealAction hB hD)).val.app _ ((𝟙 Γ₁).op, n) F = F := by
  rw [rawPi_toIdealAction label T B hB hD, (piLimit E ℓ).rawExtend_toLower,
    piLimit_extend_pi label] at hF
  exact Subtype.val_injective hF

end CodeAssignment

namespace RawFamily

variable {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
  (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
  (label : Ty.Pair Γ₁)
  (C : RawFamily Γ₁) {B : RawFamily (CtxCat.extension Γ₁ ht)} (hB : B.IsFinitary)
  (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hC : (C.app _ σ₁.op ρ).IsDirected)
  (hD : (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ).IsIdealValued)
  (n : Tm_ Γ₂) {F : Domain Γ₂}
  (hF : (piLimit E ℓ).rawExtend ((pi (piLimit E ℓ) (CtxCat.rawComprehension ht) label C B).app _ σ₁.op ρ) n F.val = F.val)
include hB hC hD hF

theorem application_rawPi_fixed (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
    (X : Domain Γ₃)
    (hX : (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val = X.val)
    (h : Tm.type ((Tm E ℓ).map σ₂.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)).1
        ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)).2)
    (hm : Tm.type name = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)).1) :
    (piLimit E ℓ).rawExtend (sectionValue (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name X.val)
        (Tm.apply ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)).1
          ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)).2
          ((Tm E ℓ).map σ₂.op n) name h hm)
        (CoherentShape.application (F.pullback σ₂) name X).val =
      (CoherentShape.application (F.pullback σ₂) name X).val := by
  let T : Domain Γ₂ := (C.app _ σ₁.op ρ).toIdeal hC
  let U : RawAction Γ₂ := normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ
  have hU : U.IsFinitary := normalizedBodyAction_isFinitary (piLimit E ℓ) (CtxCat.rawComprehension ht) C hB σ₁ ρ
  let V : IdealAction Γ₂ := U.toIdealAction hU hD
  have hF' : ((piLimit E ℓ).piAction ((Ty.pairPresheaf E ℓ).map σ₁.op label) T V).val.app _
      ((𝟙 Γ₂).op, n) F = F :=
    piAction_fixed_of_rawExtend_rawPi ((Ty.pairPresheaf E ℓ).map σ₁.op label) T U hU hD n hF
  have hdomain : (T.pullback σ₂).val = C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂) :=
    C.app_pullback σ₁.op σ₂ ρ
  have hXideal : (piLimit E ℓ).extend (T.pullback σ₂) name X = X := by
    apply Subtype.val_injective
    rwa [← (piLimit E ℓ).rawExtend_toLower, hdomain]
  rw [piAction_app_id] at hF'
  have hresult := (piLimit E ℓ).application_eq_of_piBody_fixed ((Ty.pairPresheaf E ℓ).map σ₁.op label)
    n T V hF' σ₂ name X
  rw [hXideal, (piLimit E ℓ).resultIdeal_eq_body _ n V σ₂ name X _ h hm] at hresult
  have hcode : (V.val.app _ (σ₂.op, name) X).val =
      sectionValue (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name X.val := by
    rw [RawAction.toIdealAction_value_toLower]
    change sectionValue (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name
      ((piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val) = _
    rw [hX]
  rw [← hcode, (piLimit E ℓ).rawExtend_toLower]
  exact congrArg Subtype.val hresult.symm

theorem application_rawPi_fixed_support (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
    (X : Domain Γ₃)
    {y : CoherentShape Γ₃}
    (hy : (CoherentShape.application (F.pullback σ₂) name X).mem (𝟙 Γ₃) y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name) := by
  let T := (C.app _ σ₁.op ρ).toIdeal hC
  let U := normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ
  have hU : U.IsFinitary := normalizedBodyAction_isFinitary (piLimit E ℓ) (CtxCat.rawComprehension ht) C hB σ₁ ρ
  let V := U.toIdealAction hU hD
  have hF' : ((piLimit E ℓ).piAction ((Ty.pairPresheaf E ℓ).map σ₁.op label) T V).val.app _
      ((𝟙 Γ₂).op, n) F = F :=
    piAction_fixed_of_rawExtend_rawPi ((Ty.pairPresheaf E ℓ).map σ₁.op label) T U hU hD n hF
  rw [piAction_app_id] at hF'
  have harg := (piLimit E ℓ).application_eq_of_piBody_fixed ((Ty.pairPresheaf E ℓ).map σ₁.op label)
    n T V hF' σ₂ name X
  rw [harg] at hy
  rcases hy with hy | ⟨h, hm, hy⟩
  · exact absurd hy hne
  rw [resultBody] at hy
  have hS : V.val.app _ ((𝟙 Γ₃ ≫ σ₂).op, (Tm E ℓ).map (𝟙 Γ₃).op name)
      (((piLimit E ℓ).extend (T.pullback σ₂) name X).pullback (𝟙 Γ₃)) =
      V.val.app _ (σ₂.op, name) ((piLimit E ℓ).extend (T.pullback σ₂) name X) := by
    simp
  rw [hS] at hy
  have ⟨c, hc, hcne⟩ := (piLimit E ℓ).rawExtend_nonbottom_code piLimit_value_bottom hy hne
  exact sectionValue_support (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name _ hc hcne

theorem outputAtom_rawPi_fixed_bot_or_section (σ₂ : Γ₃ ⟶ Γ₂) {name : Tm_ Γ₃}
    {x y : CoherentShape Γ₃}
    (hy : OutputAtom (F.pullback σ₂).val name x y) :
    y ≤ ⊥ ∨ Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name) := by
  by_cases hbottom : y ≤ ⊥
  · exact Or.inl hbottom
  · exact Or.inr (application_rawPi_fixed_support ht label C hB σ₁ ρ hC hD n hF σ₂ name
      (principalIdeal x) (hy.mem_application ((principalIdeal_mem x (𝟙 Γ₃) x).mpr (by simp)))
      hbottom)

end RawFamily

end Support

section Fixedness

variable {Γ₁ Γ₂ : CtxCat E ℓ}

namespace RawFamily

variable {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}

private theorem normalizedBodyAction_value (D : CodeAssignment E ℓ)
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (C : RawFamily Γ₁) (B : RawFamily (CtxCat.extension Γ₁ ht))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂)
    (name : Tm_ Γ₃) (I : RawValue Γ₃) :
    (normalizedBodyAction D (CtxCat.rawComprehension ht) C B σ₁ ρ).app _ (σ₂.op, name) I =
      sectionValue (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name
        (D.rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name I) := rfl

theorem normalizedAbstraction_fixed (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (C : RawFamily Γ₁) (B M : RawFamily (CtxCat.extension Γ₁ ht))
    (hBF : B.IsFinitary) (hMF : M.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (label : Ty.Pair Γ₂)
    (hlabel : yonedaEquiv label.1 = (Ty E ℓ).map σ₁.op (Ty.ofTyping Γ₁.as ht))
    (n : Tm_ Γ₂) (hn : Tm.type n = Ty.piApp label.1 label.2)
    (hC : (C.app _ σ₁.op ρ).IsDirected)
    (hBI : (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ).IsIdealValued)
    (hMI : (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C M σ₁ ρ).IsIdealValued)
    (hbody : ∀ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃) (J : Domain Γ₃)
      (h : Tm.type ((Tm E ℓ).map σ₂.op n) =
        Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₂.op label).1
          ((Ty.pairPresheaf E ℓ).map σ₂.op label).2)
      (hm : Tm.type name = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₂.op label).1),
      (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name J.val = J.val →
      (piLimit E ℓ).rawExtend
          (sectionValue (CtxCat.rawComprehension ht) B (σ₂ ≫ σ₁) (ρ.pullback σ₂) name J.val)
          (Tm.apply ((Ty.pairPresheaf E ℓ).map σ₂.op label).1
            ((Ty.pairPresheaf E ℓ).map σ₂.op label).2 ((Tm E ℓ).map σ₂.op n) name h hm)
          (sectionValue (CtxCat.rawComprehension ht) M (σ₂ ≫ σ₁) (ρ.pullback σ₂) name J.val) =
        sectionValue (CtxCat.rawComprehension ht) M (σ₂ ≫ σ₁) (ρ.pullback σ₂) name J.val) :
    (piLimit E ℓ).rawExtend
        (rawPi label (C.app _ σ₁.op ρ) (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ)) n
        (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C M σ₁ ρ).abstraction =
      (normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C M σ₁ ρ).abstraction := by
  let T := (C.app _ σ₁.op ρ).toIdeal hC
  let b := normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C B σ₁ ρ
  let m := normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C M σ₁ ρ
  have hbF : b.IsFinitary := normalizedBodyAction_isFinitary (piLimit E ℓ) (CtxCat.rawComprehension ht) C hBF σ₁ ρ
  have hmF : m.IsFinitary := normalizedBodyAction_isFinitary (piLimit E ℓ) (CtxCat.rawComprehension ht) C hMF σ₁ ρ
  let V : IdealAction Γ₂ := b.toIdealAction hbF hBI
  let L := m.abstraction.toIdeal (m.abstraction_isDirected hMI)
  have hnσ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) : Tm.type ((Tm E ℓ).map σ₂.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₂.op label).1
        ((Ty.pairPresheaf E ℓ).map σ₂.op label).2 := by
    rw [Tm.type_map, hn, Ty.map_piApp]
    rfl
  have hdecode {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃) (Y : Domain Γ₃) :
      ((piLimit E ℓ).extend (T.pullback σ₂) name Y).val =
        (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name Y.val := by
    rw [← (piLimit E ℓ).rawExtend_toLower]
    exact congrArg (fun S : RawValue Γ₃ => (piLimit E ℓ).rawExtend S name Y.val)
      (C.app_pullback σ₁.op σ₂ ρ)
  have hβ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃) (Y : Domain Γ₃) :
      (CoherentShape.application (L.pullback σ₂) name Y).val = m.app _ (σ₂.op, name) Y.val := by
    rw [← rawApplication_singleton]
    change rawApplication (m.abstraction.pullback σ₂) {name} Y.val = _
    have h := RawAction.rawApplication_abstraction_eq_value (m.pullback σ₂)
      (hmF.pullback σ₂) (hMI.pullback σ₂) Y {name} name rfl
      fun _ _ hname _ _ _ => Or.inr (by simpa using hname)
    rw [RawAction.pullback, RawAction.app_map] at h
    simpa only [RawAction.pullback_abstraction, RawAction.pullback, op_id, Category.comp_id] using h
  change (piLimit E ℓ).rawExtend (rawPi label T.val b) n L.val = m.abstraction
  rw [rawPi_toIdealAction label T b hbF hBI, (piLimit E ℓ).rawExtend_toLower, piLimit_extend_pi label,
    piAction_app_id]
  symm
  apply m.abstraction_eq_of_ideal_values
  intro Γ₃ σ₂ name X
  apply Presheaf.ΩLower.ext
  intro Γ₄ σ₃ y
  set name' := (Tm E ℓ).map σ₃.op name with hname'
  set U : Domain Γ₃ := (piLimit E ℓ).extend (T.pullback σ₂) name X with hUdef
  set W : Domain Γ₃ := CoherentShape.application (L.pullback σ₂) name U with hWdef
  set J : Domain Γ₄ := (piLimit E ℓ).extend (T.pullback (σ₃ ≫ σ₂)) name' (X.pullback σ₃) with hJdef
  have hUJ : U.pullback σ₃ = J := by
    rw [hUdef, hJdef, (piLimit E ℓ).pullback_extend, Presheaf.ΩIdeal.pullback_pullback]
  have hJval : J.val =
      (piLimit E ℓ).rawExtend (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback (σ₃ ≫ σ₂))) name' (X.pullback σ₃).val := by
    rw [hJdef]
    exact hdecode (σ₃ ≫ σ₂) name' (X.pullback σ₃)
  have hJfix : (piLimit E ℓ).rawExtend (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback (σ₃ ≫ σ₂))) name' J.val = J.val := by
    rw [← hdecode (σ₃ ≫ σ₂) name' J, hJdef]
    exact congrArg Subtype.val ((piLimit E ℓ).extend_idempotent piLimit_isIdempotent _ _ _)
  have hMX : m.app _ ((σ₃ ≫ σ₂).op, name') (X.pullback σ₃).val =
      sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val := by
    rw [normalizedBodyAction_value, hJval]
  have hBvalue : (V.val.app _ ((σ₃ ≫ σ₂).op, name') J).val =
      sectionValue (CtxCat.rawComprehension ht) B ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val := by
    rw [RawAction.toIdealAction_value_toLower, normalizedBodyAction_value, hJfix]
  have hWvalue : (W.pullback σ₃).val =
      sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val := by
    rw [hWdef, pullback_application, Presheaf.ΩIdeal.pullback_pullback, hUJ, hβ,
      normalizedBodyAction_value, hJfix]
  have hrb (h : Tm.type ((Tm E ℓ).map (σ₃ ≫ σ₂).op n) =
        Ty.piApp ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂).op label).1
          ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂).op label).2)
      (hm : Tm.type name' = yonedaEquiv ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂).op label).1) :
      ((piLimit E ℓ).resultBody label n V (σ₃ ≫ σ₂) name' (U.pullback σ₃) (W.pullback σ₃) h hm).val =
        sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val := by
    rw [resultBody, ← (piLimit E ℓ).rawExtend_toLower, hUJ, hBvalue, hWvalue]
    exact hbody (σ₃ ≫ σ₂) name' J h hm hJfix
  have happ : (m.app _ (σ₂.op, name) X.val).pullback σ₃ =
      sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val := by
    rw [← hMX]
    exact (RawAction.app_pullback m σ₂.op σ₃ name X.val).symm
  have hLHS : (m.app _ (σ₂.op, name) X.val).mem σ₃ y ↔
      (sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val).mem (𝟙 Γ₄) y := by
    rw [← happ]
    exact (Presheaf.ΩLower.presheaf_map_mem_id _ σ₃ y).symm
  rw [hLHS]
  constructor
  · rintro (hy | ⟨s, hs⟩)
    · exact Or.inl hy
    · have hm : Tm.type name' =
          yonedaEquiv ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂).op label).1 := by
        have hs' := s.type_eq
        simp only [op_id, Functor.map_id_apply, Category.id_comp] at hs'
        change Tm.type name' = _ at hs'
        rw [hs', CtxCat.rawComprehension_type]
        change _ = yonedaEquiv (yoneda.map (σ₃ ≫ σ₂) ≫ label.1)
        rw [← yonedaEquiv_naturality, hlabel, ← Functor.map_comp_apply, ← op_comp]
      refine Or.inr ⟨hnσ (σ₃ ≫ σ₂), hm, ?_⟩
      change ((piLimit E ℓ).resultBody label n V (σ₃ ≫ σ₂) name' (U.pullback σ₃) (W.pullback σ₃) _ hm).val.mem
        (𝟙 Γ₄) y
      rw [hrb]
      exact Or.inr ⟨s, hs⟩
  · rintro (hy | ⟨h, hm, hy⟩)
    · exact (sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val).lower _ hy
        ((sectionValue (CtxCat.rawComprehension ht) M ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback (σ₃ ≫ σ₂)) name' J.val).bottom _)
    · change ((piLimit E ℓ).resultBody label n V (σ₃ ≫ σ₂) name' (U.pullback σ₃) (W.pullback σ₃) h hm).val.mem
        (𝟙 Γ₄) y at hy
      rwa [hrb] at hy

end RawFamily

end Fixedness

end Metalean.CoherentShape
