module

public import Metalean.Semantics.Basis.Rank
public import Metalean.Semantics.Domain.Decoder.Pi

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

theorem Evaluates.principal_upper {f : CoherentGraph Γ₁} {label : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} (hy : Evaluates (principalIdeal f.lamGenerator) label x y) :
    ∃ b : CoherentShape Γ₁, b.val.rank ≤ f.val.rank ∧
      Evaluates (principalIdeal f.lamGenerator) label x b ∧ y ≤ b := by
  induction hy with
  | entry h =>
    obtain ⟨g, i, hg, hlabel, hinput, rfl⟩ := h
    rcases CoherentGraph.lamGenerator_le_iff.mp (by simpa using hg) i with hb | ⟨j, hname, hin, hout⟩
    · exact ⟨⊥, Nat.zero_le _, .bottom, le_bot_iff.mpr hb⟩
    · exact ⟨f.output j, f.1.rank_outs_le j,
        .entry ⟨f, j, by simp, hname.trans hlabel, hin.trans hinput, rfl⟩, hout⟩
  | bottom => exact ⟨⊥, Nat.zero_le _, .bottom, le_rfl⟩
  | lower h _ ih =>
    have ⟨b, hrb, hb, hyb⟩ := ih
    exact ⟨b, hrb, hb, h.trans hyb⟩
  | join h _ _ ih ih' =>
    have ⟨a, hra, ha, hya⟩ := ih
    have ⟨b, hrb, hb, hyb⟩ := ih'
    have hab := ha.upper hb
    exact ⟨cSup a b hab, Shape.rank_cSup.trans (max_le hra hrb), .join hab ha hb,
      cSup_le h (hya.trans (le_cSup_left _ _ _)) (hyb.trans (le_cSup_right _ _ _))⟩

theorem application_rank_upper (f : CoherentGraph Γ₁) (label : Tm_ Γ₁) (X : Domain Γ₁)
    (σ : Γ₂ ⟶ Γ₁) {y : CoherentShape Γ₂}
    (hy : (application (principalIdeal f.lamGenerator) label X).mem σ y) :
    ∃ b : CoherentShape Γ₂, b.1.rank ≤ f.1.rank ∧
      (application (principalIdeal f.lamGenerator) label X).mem σ b ∧ y ≤ b := by
  have heq := pullback_application (principalIdeal f.lamGenerator) X label σ
  simp at heq
  change _ = application (principalIdeal (f.reindex σ).lamGenerator) _ _ at heq
  have hy' := (ΩIdeal.presheaf_map_mem_id
    (application (principalIdeal f.lamGenerator) label X) σ y).mpr hy
  rw [heq] at hy'
  have ⟨x, hx, hy⟩ := (mem_application _ _ _ _ _).mp hy'
  simp at hy
  have ⟨b, hrb, hb, hyb⟩ := hy.principal_upper
  rw [CoherentGraph.reindex_val, Graph.rank_map] at hrb
  refine ⟨b, hrb, (ΩIdeal.presheaf_map_mem_id _ σ _).mp ?_, hyb⟩
  rw [heq]
  exact (mem_application _ _ _ _ _).mpr ⟨x, hx, by simpa using hb⟩

def Domain.CofinalIn (T : Domain Γ₁) (P : ∀ {Γ₂ : CtxCat E ℓ}, CoherentShape Γ₂ → Prop) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (a : CoherentShape Γ₂), T.mem σ a → ∃ b, P b ∧ T.mem σ b ∧ a ≤ b

theorem CodeAssignment.extend_eq_of {F G : CodeAssignment E ℓ}
    {P : ∀ {Γ₂ : CtxCat E ℓ}, CoherentShape Γ₂ → Prop}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (b : CoherentShape Γ₂), P b → F.app _ b = G.app _ b)
    {T : Domain Γ₁} (hT : T.CofinalIn P) (cls : Tm_ Γ₁) (X : Domain Γ₁) :
    F.extend T cls X = G.extend T cls X := by
  ext Γ₂ σ y
  simp_rw [mem_extend]
  constructor <;> intro ⟨a, ha, hy⟩ <;> have ⟨b, hPb, hb, hab⟩ := hT σ a ha
  · exact ⟨b, hb, by simpa [eval, h b hPb] using F.eval_mono_code hab _ (X.pullback σ) (𝟙 Γ₂) y hy⟩
  · exact ⟨b, hb, by simpa [eval, h b hPb] using G.eval_mono_code hab _ (X.pullback σ) (𝟙 Γ₂) y hy⟩

private theorem graphAction_extend_eq {F G : CodeAssignment E ℓ} {n : Nat}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (b : CoherentShape Γ₂), b.1.rank < n → F.app _ b = G.app _ b)
    (f : CoherentGraph Γ₁) (hf : f.1.rank < n) (σ₁ : Γ₂ ⟶ Γ₁)
    (m : Tm_ Γ₂) (X : Domain Γ₂) (cls : Tm_ Γ₂) (Y : Domain Γ₂) :
    F.extend ((graphAction f).val.app _ (σ₁.op, m) X) cls Y =
      G.extend ((graphAction f).val.app _ (σ₁.op, m) X) cls Y := by
  rw [graphAction_value]
  refine CodeAssignment.extend_eq_of h (fun _ σ₂ _ hz => ?_) _ _
  have ⟨b, hrb, hb, hzb⟩ := application_rank_upper _ _ _ σ₂ hz
  rw [CoherentGraph.reindex_val, Graph.rank_map] at hrb
  exact ⟨b, hrb.trans_lt hf, hb, hzb⟩

theorem CodeAssignment.piAction_congr {F G : CodeAssignment E ℓ}
    (label : Ty.Pair Γ₁) {A : Domain Γ₁} {B : IdealAction Γ₁}
    (hA : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂) (X : Domain Γ₂),
      F.extend (A.pullback σ) m X = G.extend (A.pullback σ) m X)
    (hB : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂) (X : Domain Γ₂)
      (cls : Tm_ Γ₂) (Y : Domain Γ₂),
      F.extend (B.val.app _ (σ.op, m) X) cls Y = G.extend (B.val.app _ (σ.op, m) X) cls Y) :
    F.piAction label A B = G.piAction label A B := by
  ext Γ₂ ⟨⟨σ₁⟩, cls⟩ Y
  refine congrArg IdealAction.abstraction ?_
  ext Γ₃ ⟨⟨σ₂⟩, m⟩ X
  refine ΩIdeal.ext fun σ₃ z => ?_
  change (F.resultIdeal _ cls (B.pullback σ₁) σ₂ m (F.extend ((A.pullback σ₁).pullback σ₂) m X)
      (application (Y.pullback σ₂) m (F.extend ((A.pullback σ₁).pullback σ₂) m X))).mem σ₃ z ↔
    (G.resultIdeal _ cls (B.pullback σ₁) σ₂ m (G.extend ((A.pullback σ₁).pullback σ₂) m X)
      (application (Y.pullback σ₂) m (G.extend ((A.pullback σ₁).pullback σ₂) m X))).mem σ₃ z
  rw [ΩIdeal.pullback_pullback, hA]
  refine or_congr_right (exists_congr fun _ => exists_congr fun _ => ?_)
  rw [resultBody, resultBody, IdealAction.pullback_app, hB]

theorem CodeAssignment.piAction_eq_of_rank {F G : CodeAssignment E ℓ} {n : Nat}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (b : CoherentShape Γ₂), b.1.rank < n → F.app _ b = G.app _ b)
    (label : Ty.Pair Γ₁)
    (a : CoherentShape Γ₁) (ha : a.1.rank < n) (f : CoherentGraph Γ₁) (hf : f.1.rank < n) :
    F.piAction label (principalIdeal a) (graphAction f) =
      G.piAction label (principalIdeal a) (graphAction f) :=
  piAction_congr label
    (fun σ _ _ => by
      rw [ΩIdeal.presheaf_map_principal]
      exact extend_eq_of h (fun _ σ' _ hb => ⟨_, by simpa using ha,
        (principalIdeal_mem _ _ _).mpr le_rfl, by simpa using hb⟩) _ _)
    fun σ m X => graphAction_extend_eq h f hf σ m X

end Metalean.CoherentShape
