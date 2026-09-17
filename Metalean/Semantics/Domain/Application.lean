module

public import Metalean.Order.Presheaf.Finitary
public import Metalean.Semantics.Basis.Join

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ : CtxCat E ℓ}
variable {x' y' : CoherentShape Γ₁}

namespace CoherentShape

inductive OutputAtom (I : ΩLower (pointedOrder E ℓ) Γ₁) (label : Tm_ Γ₁)
    (x y : CoherentShape Γ₁) : Prop where
  | intro (graph : CoherentGraph Γ₁) (entry : Fin graph.val.size)
      (graph_mem : I.mem (𝟙 Γ₁) graph.lamGenerator) (label_eq : graph.val.names entry = label)
      (input_le : graph.input entry ≤ x) (output_eq : y = graph.output entry) :
      OutputAtom I label x y

namespace OutputAtom

theorem mono {I : ΩLower (pointedOrder E ℓ) Γ₁} {label : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} (h : OutputAtom I label x y) (hxx' : x ≤ x') :
    OutputAtom I label x' y :=
  let ⟨f, i, hf, hlabel, hix, hy⟩ := h
  ⟨f, i, hf, hlabel, hix.trans hxx', hy⟩

theorem mono_function {I J : ΩLower (pointedOrder E ℓ) Γ₁} (hIJ : I ≤ J)
    {label : Tm_ Γ₁} {x y : CoherentShape Γ₁} (h : OutputAtom I label x y) :
    OutputAtom J label x y :=
  let ⟨f, i, hf, hlabel, hix, hy⟩ := h
  ⟨f, i, hIJ (𝟙 Γ₁) f.lamGenerator hf, hlabel, hix, hy⟩

theorem reindex (σ : Γ₂ ⟶ Γ₁) {I : ΩLower (pointedOrder E ℓ) Γ₁} {label : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} (h : OutputAtom I label x y) :
    OutputAtom (I.pullback σ) ((Tm E ℓ).map σ.op label) (reindex σ x) (reindex σ y) := by
  have ⟨f, i, hf, hlabel, hix, hiy⟩ := h
  refine ⟨f.reindex σ, i, ?_, congrArg ((Tm E ℓ).map σ.op) hlabel,
    Le.reindex σ hix, congrArg (CoherentShape.reindex σ) hiy⟩
  change I.mem (𝟙 Γ₂ ≫ σ) (CoherentShape.reindex σ f.lamGenerator)
  simpa using I.natural (𝟙 Γ₁) σ f.lamGenerator hf

theorem compatible {I : Domain Γ₁} {label : Tm_ Γ₁} {x y : CoherentShape Γ₁}
    (hy : OutputAtom I.val label x y) (hy' : OutputAtom I.val label x y') :
    Shape.Compatible (𝟙 Γ₁) y.1 y'.1 := by
  have ⟨f, i, hf, hilabel, hix, hiy⟩ := hy
  have ⟨g, j, hg, hjlabel, hjx, hjy⟩ := hy'
  have ⟨c, _, hfc, hgc⟩ := I.property (𝟙 Γ₁) hf hg
  rw [hiy, hjy]
  have h := compatible_of_le hfc hgc (𝟙 Γ₁) i j (𝟙 Γ₁) (by rw [hilabel.trans hjlabel.symm])
    (compatible_of_le hix hjx _)
  simp at h
  exact h

end OutputAtom

inductive Evaluates (I : Domain Γ₁) (label : Tm_ Γ₁) (x : CoherentShape Γ₁) :
    CoherentShape Γ₁ → Prop where
  | entry {y} : OutputAtom I.val label x y → Evaluates I label x y
  | bottom : Evaluates I label x ⊥
  | lower {y z} : y ≤ z → Evaluates I label x z → Evaluates I label x y
  | join {y z} (h : ∃ c, y ≤ c ∧ z ≤ c) :
      Evaluates I label x y → Evaluates I label x z → Evaluates I label x (cSup y z h)

namespace Evaluates

private theorem compatible_right {I : Domain Γ₁} {label : Tm_ Γ₁} {x y d : CoherentShape Γ₁}
    (h : ∀ {z}, OutputAtom I.val label x z → Shape.Compatible (𝟙 Γ₁) z.1 d.1) :
    Evaluates I label x y →
    Shape.Compatible (𝟙 Γ₁) y.1 d.1
  | .entry hy => h hy
  | .bottom => Shape.Compatible.of_isBottom_left _ .bot
  | .lower hle hz => Shape.Compatible.anti_left hle (compatible_right h hz)
  | .join _ hy hz => Shape.cSup_compatible _ (compatible_right h hy) (compatible_right h hz)

theorem upper {I : Domain Γ₁} {label : Tm_ Γ₁} {x y z : CoherentShape Γ₁}
    (hy : Evaluates I label x y) (hz : Evaluates I label x z) : ∃ c, y ≤ c ∧ z ≤ c :=
  upper_of_compatible
    (hy.compatible_right fun ha => (hz.compatible_right fun hb => (ha.compatible hb).symm).symm)

theorem mono {I : Domain Γ₁} {label : Tm_ Γ₁} {x x' y : CoherentShape Γ₁}
    (hxx' : x ≤ x') :
    Evaluates I label x y →
    Evaluates I label x' y
  | .entry h => .entry (h.mono hxx')
  | .bottom => .bottom
  | .lower h hz => .lower h (mono hxx' hz)
  | .join h hy hz => .join h (mono hxx' hy) (mono hxx' hz)

theorem mono_ideal {I J : Domain Γ₁} (hIJ : I ≤ J) {label : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} :
    Evaluates I label x y →
    Evaluates J label x y
  | .entry h => .entry (h.mono_function hIJ)
  | .bottom => .bottom
  | .lower h hz => .lower h (mono_ideal hIJ hz)
  | .join h hy hz => .join h (mono_ideal hIJ hy) (mono_ideal hIJ hz)

theorem reindex (σ : Γ₂ ⟶ Γ₁) {I : Domain Γ₁} {label : Tm_ Γ₁} {x y : CoherentShape Γ₁} :
    Evaluates I label x y →
    Evaluates (I.pullback σ) ((Tm E ℓ).map σ.op label) (CoherentShape.reindex σ x)
      (CoherentShape.reindex σ y)
  | .entry h => .entry (h.reindex σ)
  | .bottom => .bottom
  | .lower h hz => .lower (Le.reindex σ h) (reindex σ hz)
  | .join h hy hz => by
    have ⟨c, hyc, hzc⟩ := h
    have hr : CoherentShape.reindex σ (cSup _ _ h) =
        cSup _ _ ⟨CoherentShape.reindex σ c, Le.reindex σ hyc, Le.reindex σ hzc⟩ :=
      Subtype.ext (Shape.map_cSup _ _ _ _)
    rw [hr]
    exact .join _ (reindex σ hy) (reindex σ hz)

theorem mem_of_outputAtom {I : Domain Γ₁} {label : Tm_ Γ₁} {x y : CoherentShape Γ₁}
    {L : RawValue Γ₁} (hL : L.IsDirected)
    (h : ∀ {z}, OutputAtom I.val label x z → L.mem (𝟙 Γ₁) z) :
    Evaluates I label x y →
    L.mem (𝟙 Γ₁) y
  | .entry hz => h hz
  | .bottom => L.bottom _
  | .lower hle hz => L.lower _ hle (mem_of_outputAtom hL h hz)
  | .join hc hy hz =>
    have ⟨_, hc', hyc, hzc⟩ := hL (𝟙 Γ₁) (mem_of_outputAtom hL h hy) (mem_of_outputAtom hL h hz)
    L.lower _ (cSup_le hc hyc hzc) hc'

theorem le_of_outputAtom {I : Domain Γ₁} {label : Tm_ Γ₁} {x y d : CoherentShape Γ₁}
    (hy : Evaluates I label x y) (h : ∀ {z}, OutputAtom I.val label x z → z ≤ d) : y ≤ d := by
  simpa using hy.mem_of_outputAtom (principalIdeal d).property fun hz => by simpa using h hz

theorem function_ideal_finitary {I : Domain Γ₁} {label : Tm_ Γ₁}
    {input output : CoherentShape Γ₁} (h : Evaluates I label input output) :
    ∃ f, I.mem (𝟙 Γ₁) f ∧ Evaluates (principalIdeal f) label input output := by
  induction h with
  | entry h =>
    have ⟨g, i, hg, hl, hx, hy⟩ := h
    exact ⟨_, hg, .entry ⟨g, i, by simp, hl, hx, hy⟩⟩
  | bottom => exact ⟨⊥, I.bottom _, .bottom⟩
  | lower h _ ih =>
    have ⟨a, ha, hy⟩ := ih
    exact ⟨a, ha, .lower h hy⟩
  | join h _ _ ih ih' =>
    have ⟨a, ha, hy⟩ := ih
    have ⟨b, hb, hy'⟩ := ih'
    have ⟨c, hc, hac, hbc⟩ := I.property (𝟙 Γ₁) ha hb
    exact ⟨c, hc, .join h (hy.mono_ideal (ΩLower.principal_mono hac))
      (hy'.mono_ideal (ΩLower.principal_mono hbc))⟩

end Evaluates

def application (I : Domain Γ₁) (label : Tm_ Γ₁) (X : Domain Γ₁) : Domain Γ₁ where
  val := {
    mem σ y := ∃ x, X.mem σ x ∧ Evaluates (I.pullback σ) ((Tm E ℓ).map σ.op label) x y
    natural σ₁ σ₂ y := fun ⟨x, hx, hy⟩ =>
      ⟨reindex σ₂ x, X.natural σ₁ σ₂ x hx, by simpa using hy.reindex σ₂⟩
    bottom σ := ⟨⊥, X.bottom σ, Evaluates.bottom⟩
    lower _ hyy' := fun ⟨x, hx, hy'⟩ => ⟨x, hx, hy'.lower hyy'⟩ }
  property {_} σ {_ _} := fun ⟨x, hx, hxy⟩ ⟨x', hx', hx'y'⟩ =>
    have ⟨c, hc, hxc, hx'c⟩ := X.property σ hx hx'
    have hy := hxy.mono hxc
    have hy' := hx'y'.mono hx'c
    have h := hy.upper hy'
    ⟨cSup _ _ h, ⟨c, hc, .join h hy hy'⟩, le_cSup_left _ _ h, le_cSup_right _ _ h⟩

@[simp] theorem mem_application (I : Domain Γ₂) (label : Tm_ Γ₂)
    (X : Domain Γ₂) (σ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (application I label X).mem σ y ↔ ∃ x, X.mem σ x ∧
      Evaluates (I.pullback σ) ((Tm E ℓ).map σ.op label) x y :=
  Iff.rfl

theorem OutputAtom.mem_application {F X : Domain Γ₁} {label : Tm_ Γ₁}
    {x y : CoherentShape Γ₁} (hy : OutputAtom F.val label x y) (hx : X.mem (𝟙 Γ₁) x) :
    (application F label X).mem (𝟙 Γ₁) y := by
  simp
  exact ⟨x, hx, .entry hy⟩

theorem application_mono {I J X Y : Domain Γ₁} {label : Tm_ Γ₁} (hIJ : I ≤ J)
    (hXY : X ≤ Y) : application I label X ≤ application J label Y :=
  fun σ _ ⟨x, hx, hxy⟩ => ⟨x, hXY σ x hx, hxy.mono_ideal (ΩIdeal.pullback_mono hIJ σ)⟩

theorem application_argument_finitary (F : Domain Γ₁) (label : Tm_ Γ₁) :
    ΩIdeal.IsFinitary (application F label) :=
  fun I y ⟨x, hx, heval⟩ => ⟨x, hx, x, by simp, heval⟩

theorem application_function_finitary (F : Domain Γ₁) {X : Domain Γ₁} (label : Tm_ Γ₁)
    {y : CoherentShape Γ₁} (hy : (application F label X).mem (𝟙 Γ₁) y) :
    ∃ f, F.mem (𝟙 Γ₁) f ∧ (application (principalIdeal f) label X).mem (𝟙 Γ₁) y := by
  have ⟨x, hx, heval⟩ := hy
  simp at heval
  have ⟨f, hf, heval⟩ := heval.function_ideal_finitary
  exact ⟨f, hf, x, hx, by simpa using heval⟩

end CoherentShape

end Metalean
