/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Metalean.Semantics.Basis.Order
public import Metalean.Semantics.Basis.Shape
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

open CategoryTheory Opposite TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}

def Shape.Compatible {Γ₂ : CtxCat E ℓ} (σ₁ : Γ₂ ⟶ Γ₁) : Shape Γ₁ → Shape Γ₁ → Prop
  | .bot, _ => True
  | _, .bot => True
  | .sort r, .sort r' => r = r'
  | .forallE label a _ names ins outs, .forallE label' a' _ names' ins' outs' =>
    (Ty.pairPresheaf E ℓ).map σ₁.op label = (Ty.pairPresheaf E ℓ).map σ₁.op label' ∧ Compatible σ₁ a a' ∧
      ∀ i j {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ _),
        (Tm E ℓ).map (σ₂ ≫ σ₁).op (names i) = (Tm E ℓ).map (σ₂ ≫ σ₁).op (names' j) →
        Compatible (σ₂ ≫ σ₁) (ins i) (ins' j) → Compatible (σ₂ ≫ σ₁) (outs i) (outs' j)
  | .lam _ names ins outs, .lam _ names' ins' outs' =>
    ∀ i j {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ _),
      (Tm E ℓ).map (σ₂ ≫ σ₁).op (names i) = (Tm E ℓ).map (σ₂ ≫ σ₁).op (names' j) →
      Compatible (σ₂ ≫ σ₁) (ins i) (ins' j) → Compatible (σ₂ ≫ σ₁) (outs i) (outs' j)
  | .ind code ctorTypes, .ind code' ctorTypes' =>
    code.map ((Tm E ℓ).map σ₁.op) = code'.map ((Tm E ℓ).map σ₁.op) ∧
      ∀ c c', c.val = c'.val → Compatible σ₁ (ctorTypes c) (ctorTypes' c')
  | .ctor head names fields, .ctor head' names' fields' =>
    head = head' ∧ ∀ i j, i.val = j.val →
      (Tm E ℓ).map σ₁.op (names i) = (Tm E ℓ).map σ₁.op (names' j) ∧
        Compatible σ₁ (fields i) (fields' j)
  | .struct head hstruct fields, .struct head' hstruct' fields' =>
    Basis.IsBottom (.struct head hstruct fields) ∨
      Basis.IsBottom (.struct head' hstruct' fields') ∨
      head = head' ∧ ∀ i j, i.val = j.val → Compatible σ₁ (fields i) (fields' j)
  | .quot code, .quot code' =>
    code.map ((Tm E ℓ).map σ₁.op) = code'.map ((Tm E ℓ).map σ₁.op)
  | .quotMk η name value, .quotMk η' name' value' =>
    η = η' ∧ (Tm E ℓ).map σ₁.op name = (Tm E ℓ).map σ₁.op name' ∧
      Compatible σ₁ value value'
  | a, b => Basis.IsBottom a ∨ Basis.IsBottom b

def Graph.Compatible (σ₁ : Γ₂ ⟶ Γ₁) (f g : Graph Γ₁) : Prop :=
  ∀ i j {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂),
    (Tm E ℓ).map (σ₂ ≫ σ₁).op (f.names i) = (Tm E ℓ).map (σ₂ ≫ σ₁).op (g.names j) →
    Shape.Compatible (σ₂ ≫ σ₁) (f.ins i) (g.ins j) → Shape.Compatible (σ₂ ≫ σ₁) (f.outs i) (g.outs j)

theorem Graph.Compatible.comp {σ₁ : Γ₂ ⟶ Γ₁} {f g : Graph Γ₁}
    (σ₂ : Γ₃ ⟶ Γ₂) (hfg : Graph.Compatible σ₁ f g) : Graph.Compatible (σ₂ ≫ σ₁) f g := by
  intro i j Γ₄ σ₃ hl hin
  rw [← Category.assoc] at hl hin ⊢
  exact hfg i j (σ₃ ≫ σ₂) hl hin

namespace Shape

theorem Compatible.of_isBottom_left {Γ₂ : CtxCat E ℓ} {a b : Shape Γ₁} (σ₁ : Γ₂ ⟶ Γ₁) :
    Basis.IsBottom a →
    Compatible σ₁ a b
  | .bot => by cases b <;> trivial
  | .lam h => by
    cases b with
    | bot => trivial
    | lam _ _ _ _ => exact fun i j Γ₃ σ₂ _ _ => of_isBottom_left _ (h i)
    | _ => exact .inl (.lam h)
  | .struct h => by
    cases b with
    | bot => trivial
    | _ => exact .inl (.struct h)

theorem Compatible.comm (a b : Shape Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    Compatible σ₁ a b ↔ Compatible σ₁ b a := by
  induction a generalizing b Γ₂ with
  | sort r => cases b <;> first | exact Eq.comm | exact Iff.rfl | exact Or.comm
  | forallE _ _ _ _ _ _ ih ihi iho =>
    cases b with
    | forallE _ _ _ _ _ _ =>
      exact ⟨fun ⟨hlabel, hdomain, hgraph⟩ => ⟨hlabel.symm, (ih _ σ₁).mp hdomain, fun j i _ σ₂ hl hin =>
          (iho i _ _).mp (hgraph i j σ₂ hl.symm ((ihi i _ _).mpr hin))⟩,
        fun ⟨hlabel, hdomain, hgraph⟩ => ⟨hlabel.symm, (ih _ σ₁).mpr hdomain, fun i j _ σ₂ hl hin =>
          (iho i _ _).mpr (hgraph j i σ₂ hl.symm ((ihi i _ _).mp hin))⟩⟩
    | _ => first | exact Iff.rfl | exact Or.comm
  | lam _ _ _ _ ihi iho =>
    cases b with
    | lam _ _ _ _ =>
      exact ⟨fun h j i _ σ₂ hl hin => (iho i _ _).mp (h i j σ₂ hl.symm ((ihi i _ _).mpr hin)),
        fun h i j _ σ₂ hl hin => (iho i _ _).mpr (h j i σ₂ hl.symm ((ihi i _ _).mp hin))⟩
    | _ => first | exact Iff.rfl | exact Or.comm
  | ind _ _ ih =>
    cases b with
    | ind _ _ =>
      exact ⟨fun ⟨hc, h⟩ => ⟨hc.symm, fun c c' hcc => (ih c' _ _).mp (h c' c hcc.symm)⟩,
        fun ⟨hc, h⟩ => ⟨hc.symm, fun c c' hcc => (ih c _ _).mpr (h c' c hcc.symm)⟩⟩
    | _ => first | exact Iff.rfl | exact Or.comm
  | ctor _ _ _ ih =>
    cases b with
    | ctor _ _ _ =>
      exact ⟨fun ⟨rfl, h⟩ => ⟨rfl, fun i j hij =>
          ⟨(h j i hij.symm).1.symm, (ih j _ _).mp (h j i hij.symm).2⟩⟩,
        fun ⟨rfl, h⟩ => ⟨rfl, fun i j hij =>
          ⟨(h j i hij.symm).1.symm, (ih i _ _).mpr (h j i hij.symm).2⟩⟩⟩
    | _ => first | exact Iff.rfl | exact Or.comm
  | struct _ _ _ ih =>
    cases b with
    | struct _ _ _ =>
      constructor
      · rintro (hbot | hbot' | ⟨rfl, h⟩)
        · exact .inr (.inl hbot)
        · exact .inl hbot'
        · exact .inr (.inr ⟨rfl, fun i j hij => (ih j _ _).mp (h j i hij.symm)⟩)
      · rintro (hbot' | hbot | ⟨rfl, h⟩)
        · exact .inr (.inl hbot')
        · exact .inl hbot
        · exact .inr (.inr ⟨rfl, fun i j hij => (ih i _ _).mpr (h j i hij.symm)⟩)
    | _ => first | exact Iff.rfl | exact Or.comm
  | quot _ => cases b <;> first | exact eq_comm | exact Iff.rfl | exact Or.comm
  | quotMk _ _ _ ih =>
    cases b with
    | quotMk _ _ _ =>
      exact ⟨fun ⟨hh, hn, hv⟩ => ⟨hh.symm, hn.symm, (ih _ _).mp hv⟩,
        fun ⟨hh, hn, hv⟩ => ⟨hh.symm, hn.symm, (ih _ _).mpr hv⟩⟩
    | _ => first | exact Iff.rfl | exact Or.comm
  | _ => cases b <;> exact Iff.rfl

theorem Compatible.symm {σ : Γ₂ ⟶ Γ₁} {a b : Shape Γ₁} (h : Compatible σ a b) :
    Compatible σ b a :=
  (comm a b σ).mp h

theorem Compatible.of_isBottom_right {a b : Shape Γ₁} (σ : Γ₂ ⟶ Γ₁)
    (h : Basis.IsBottom b) : Compatible σ a b :=
  (Compatible.of_isBottom_left σ h).symm

theorem Compatible.reindexHom_iff (σ₁ : Γ₂ ⟶ Γ₁) (a b : Shape Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) :
    Compatible σ₂ (a.reindexHom σ₁) (b.reindexHom σ₁) ↔ Compatible (σ₂ ≫ σ₁) a b := by
  induction a generalizing b Γ₃ with
  | ind _ _ ih =>
    cases b with
    | ind _ _ =>
      refine and_congr ?_
        (forall_congr' fun c => forall_congr' fun c' => imp_congr Iff.rfl (ih c _ _))
      simp! [reindexHom, map, IndCode.map]
    | _ => simp! [reindexHom, map, IndCode.map, QuotCode.map]
  | _ => cases b <;> simp! [reindexHom, map, IndCode.map, QuotCode.map, *]

mutual

theorem Compatible.anti_left {Γ₂ : CtxCat E ℓ} {σ₁ : Γ₂ ⟶ Γ₁} {a a' b : Shape Γ₁} :
    a ≤ a' →
    Compatible σ₁ a' b →
    Compatible σ₁ a b
  | .collapse h, _ => Compatible.of_isBottom_left σ₁ h
  | .sort _, hab => hab
  | .quot _, hab => hab
  | .ind h, hab => by
    cases b with
    | ind _ _ => exact ⟨hab.1, fun c c' hcc => anti_left (h c) (hab.2 c c' hcc)⟩
    | bot => trivial
    | _ => exact hab.imp nofun id
  | .forallE ha hf, hab => by
    cases b with
    | forallE _ _ _ _ _ _ =>
      refine ⟨hab.1, anti_left ha hab.2.1, fun i j Γ₃ σ₂ hn hin => ?_⟩
      exact anti_left_entry (hf i)
        (fun j' hn' => hab.2.2 j' j σ₂ <| congr((Tm E ℓ).map (σ₂ ≫ σ₁).op $hn').trans hn) hin
    | bot => trivial
    | _ => exact hab.imp nofun id
  | .lam hf, hab => by
    cases b with
    | lam _ _ _ _ =>
      intro i j Γ₃ σ₂ hn hin
      exact anti_left_entry (hf i)
        (fun j' hn' => hab j' j σ₂ <| congr((Tm E ℓ).map (σ₂ ≫ σ₁).op $hn').trans hn) hin
    | bot => trivial
    | _ =>
      rcases hab with hbot | hbot
      · cases hbot with
        | lam hg =>
          refine .inl (.lam fun i => ?_)
          cases hf i with
          | bottom hy => exact hy
          | mem j' _ _ hout => exact Basis.le_bot_iff.mp (hout.trans (hg j').le)
      · exact .inr hbot
  | .ctor hf, hab => by
    cases b with
    | ctor _ _ _ =>
      exact ⟨hab.1, fun i j hij => ⟨(hab.2 i j hij).1, anti_left (hf i) (hab.2 i j hij).2⟩⟩
    | bot => trivial
    | _ => exact hab.imp nofun id
  | .struct hf, hab => by
    cases b with
    | struct _ _ _ =>
      rcases hab with hbot | hbot' | ⟨hh, h⟩
      · exact .inl (Basis.IsBottom.of_le (Basis.Le.struct hf) hbot)
      · exact .inr (.inl hbot')
      · exact .inr (.inr ⟨hh, fun i j hij => anti_left (hf i) (h i j hij)⟩)
    | bot => trivial
    | _ =>
      rcases hab with hbot | hbot
      · exact .inl (Basis.IsBottom.of_le (Basis.Le.struct hf) hbot)
      · exact .inr hbot
  | .quotMk h, hab => by
    cases b with
    | quotMk _ _ _ => exact ⟨hab.1, hab.2.1, anti_left h hab.2.2⟩
    | bot => trivial
    | _ => exact hab.imp nofun id

theorem Compatible.anti_left_entry {g : Graph Γ₁} {name : Tm_ Γ₁} {x y : Shape Γ₁}
    {Γ₂ : CtxCat E ℓ} {σ₁ : Γ₂ ⟶ Γ₁} {x' y' : Shape Γ₁} :
    Basis.Entry g name x y →
    (∀ j, g.names j = name → Compatible σ₁ (g.ins j) x' → Compatible σ₁ (g.outs j) y') →
    Compatible σ₁ x x' →
    Compatible σ₁ y y'
  | .bottom hy, _, _ => Compatible.of_isBottom_left _ hy
  | .mem j hn hin hout, hg, hx => anti_left hout (hg j hn (anti_left hin hx))

end

end Shape

namespace Graph

theorem Compatible.symm {σ₁ : Γ₂ ⟶ Γ₁} {f g : Graph Γ₁} (hfg : Compatible σ₁ f g) :
    Compatible σ₁ g f :=
  fun j i _ σ₂ hl hin => (hfg i j σ₂ hl.symm hin.symm).symm

theorem Compatible.append_left {σ₁ : Γ₂ ⟶ Γ₁} {f g h : Graph Γ₁} (hf : Compatible σ₁ f h)
    (hg : Compatible σ₁ g h) : Compatible σ₁ (f.append g) h :=
  fun i j Γ₃ σ₂ => Fin.addCases
    (fun i => by simpa using hf i j σ₂)
    (fun i => by simpa using hg i j σ₂) i

theorem Compatible.append_right {σ : Γ₂ ⟶ Γ₁} {f g h : Graph Γ₁} (hf : Compatible σ h f)
    (hg : Compatible σ h g) : Compatible σ h (f.append g) :=
  (hf.symm.append_left hg.symm).symm

theorem Compatible.of_id {f g : Graph Γ₁} (hfg : Compatible (𝟙 Γ₁) f g) (σ : Γ₂ ⟶ Γ₁) :
    Compatible σ f g := by
  simpa using hfg.comp σ

theorem Compatible.reindexHom_iff (σ₁ : Γ₂ ⟶ Γ₁) (f g : Graph Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) :
    Compatible σ₂ (f.reindexHom σ₁) (g.reindexHom σ₁) ↔ Compatible (σ₂ ≫ σ₁) f g := by
  dsimp only [Compatible, reindexHom, map]
  simp [Shape.Compatible.reindexHom_iff]

theorem Compatible.reindexHom {f g : Graph Γ₁} (hfg : Compatible (𝟙 Γ₁) f g)
    (σ : Γ₂ ⟶ Γ₁) : Compatible (𝟙 Γ₂) (f.reindexHom σ) (g.reindexHom σ) := by
  rw [reindexHom_iff, Category.id_comp]
  exact hfg.of_id σ

end Graph

judgement Shape.IsCoherent (Γ₁ : CtxCat E ℓ) : Shape Γ₁ → Prop where

  ──────────────────── bot
  IsCoherent Γ₁ .bot

  ──────────────────── sort {r : Level ℓ}
  IsCoherent Γ₁ (.sort r)

  IsCoherent Γ₁ a
  Graph.Compatible (𝟙 Γ₁) ⟨k, names, ins, outs⟩ ⟨k, names, ins, outs⟩
  ∀ i, IsCoherent Γ₁ (ins i)
  ∀ i, IsCoherent Γ₁ (outs i)
  ──────────────────── forallE {label : Ty.Pair Γ₁} {a : Shape Γ₁} {k : Nat}
    {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁}
  IsCoherent Γ₁ (.forallE label a k names ins outs)

  Graph.Compatible (𝟙 Γ₁) ⟨k, names, ins, outs⟩ ⟨k, names, ins, outs⟩
  ∀ i, IsCoherent Γ₁ (ins i)
  ∀ i, IsCoherent Γ₁ (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁}
  IsCoherent Γ₁ (.lam k names ins outs)

  ∀ c, IsCoherent Γ₁ (ctorTypes c)
  ──────────────────── ind {code : IndCode Γ₁}
    {ctorTypes : Fin code.toIndHead.nctors → Shape Γ₁}
  IsCoherent Γ₁ (.ind code ctorTypes)

  ¬ head.IsStructural E
  ∀ i, IsCoherent Γ₁ (fields i)
  ──────────────────── ctor {head : CtorHead ζ} {names : Fin head.arity → Tm_ Γ₁}
    {fields : Fin head.arity → Shape Γ₁}
  IsCoherent Γ₁ (.ctor head names fields)

  ∀ i, IsCoherent Γ₁ (fields i)
  ──────────────────── struct {head : CtorHead ζ} {hstruct : head.IsStructural E}
    {fields : Fin head.arity → Shape Γ₁}
  IsCoherent Γ₁ (.struct head hstruct fields)

  ──────────────────── quot (code : QuotCode Γ₁)
  IsCoherent Γ₁ (.quot code)

  IsCoherent Γ₁ value
  ──────────────────── quotMk {η : Head ζ .quot} {name : Tm_ Γ₁} {value : Shape Γ₁}
  IsCoherent Γ₁ (.quotMk η name value)

structure Graph.IsCoherent (Γ₁ : CtxCat E ℓ) (f : Graph Γ₁) : Prop where
  directed : Graph.Compatible (𝟙 Γ₁) f f
  ins : ∀ i, Shape.IsCoherent Γ₁ (f.ins i)
  outs : ∀ i, Shape.IsCoherent Γ₁ (f.outs i)

namespace Shape.IsCoherent

theorem forallE_inv {label : Ty.Pair Γ₁} {a : Shape Γ₁} {k : Nat}
    {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁}
    (h : IsCoherent Γ₁ (.forallE label a k names ins outs)) :
    IsCoherent Γ₁ a ∧ Graph.IsCoherent Γ₁ ⟨k, names, ins, outs⟩ := by
  have .forallE ha hd hi ho := h
  exact ⟨ha, ⟨hd, hi, ho⟩⟩

theorem ind_inv {code : IndCode Γ₁} {ctorTypes : Fin code.toIndHead.nctors → Shape Γ₁}
    (h : IsCoherent Γ₁ (.ind code ctorTypes)) (c : Fin code.toIndHead.nctors) :
    IsCoherent Γ₁ (ctorTypes c) := by
  have .ind hc := h
  exact hc c

theorem reindex (σ : Γ₂ ⟶ Γ₁) {a : Shape Γ₁} (h : IsCoherent Γ₁ a) :
    IsCoherent Γ₂ (a.reindexHom σ) := by
  induction h with
  | forallE _ hd _ _ ih ihi iho => exact .forallE ih (hd.reindexHom σ) ihi iho
  | lam hd _ _ ihi iho => exact .lam (hd.reindexHom σ) ihi iho
  | ind _ ih => exact .ind ih
  | _ => constructor <;> solve_by_elim

theorem compatible_self {a : Shape Γ₁} (σ : Γ₂ ⟶ Γ₁) :
    IsCoherent Γ₁ a → Compatible σ a a
  | .bot => trivial
  | .sort | .quot _ => rfl
  | .ind h => ⟨rfl, fun c c' hcc => by
    obtain rfl := Fin.ext hcc
    exact compatible_self σ (h c)⟩
  | .forallE ha hd _ _ => ⟨rfl, compatible_self σ ha, hd.of_id σ⟩
  | .lam hd _ _ => hd.of_id σ
  | .ctor _ h => ⟨rfl, fun i j hij => by
    obtain rfl := Fin.ext hij
    exact ⟨rfl, compatible_self σ (h i)⟩⟩
  | .struct h => .inr (.inr ⟨rfl, fun i j hij => by
    obtain rfl := Fin.ext hij
    exact compatible_self σ (h i)⟩)
  | .quotMk h => ⟨rfl, rfl, compatible_self σ h⟩

end Shape.IsCoherent

namespace Graph.IsCoherent

theorem reindex (σ : Γ₂ ⟶ Γ₁) {f : Graph Γ₁} (hf : IsCoherent Γ₁ f) :
    IsCoherent Γ₂ (f.reindexHom σ) :=
  ⟨hf.directed.reindexHom σ, fun i => (hf.ins i).reindex σ, fun i => (hf.outs i).reindex σ⟩

theorem append {f g : Graph Γ₁} (hf : IsCoherent Γ₁ f) (hg : IsCoherent Γ₁ g)
    (hfg : Compatible (𝟙 Γ₁) f g) : IsCoherent Γ₁ (f.append g) where
  directed := (hf.directed.append_right hfg).append_left (hfg.symm.append_right hg.directed)
  ins := Fin.addCases (by simpa using hf.ins) (by simpa using hg.ins)
  outs := Fin.addCases (by simpa using hf.outs) (by simpa using hg.outs)

end Graph.IsCoherent

def Shape.coherent (E : Env ζ) (ℓ : Nat) : Subfunctor (Shape.presheaf E ℓ) where
  obj Γ₁ := {a | IsCoherent Γ₁.unop a}
  map σ _ ha := ha.reindex σ.unop

abbrev CoherentShape (Γ₁ : CtxCat E ℓ) := {a : Shape Γ₁ // a ∈ (Shape.coherent E ℓ).obj (op Γ₁)}

def CoherentGraph (Γ₁ : CtxCat E ℓ) := {f : Graph Γ₁ // Graph.IsCoherent Γ₁ f}

namespace CoherentShape

noncomputable abbrev presheaf (E : Env ζ) (ℓ : Nat) := (Shape.coherent E ℓ).toFunctor

noncomputable def reindex (σ : Γ₂ ⟶ Γ₁) : CoherentShape Γ₁ → CoherentShape Γ₂ :=
  (presheaf E ℓ).map σ.op

@[simp] theorem reindex_val (σ : Γ₂ ⟶ Γ₁) (a : CoherentShape Γ₁) :
    (reindex σ a).1 = a.1.reindexHom σ := rfl

@[simp] theorem reindex_id (a : CoherentShape Γ₁) : reindex (𝟙 Γ₁) a = a :=
  (presheaf E ℓ).map_id_apply (op Γ₁) a

@[simp] theorem reindex_reindex (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂)
    (a : CoherentShape Γ₁) : reindex σ₂ (reindex σ₁ a) = reindex (σ₂ ≫ σ₁) a :=
  ((presheaf E ℓ).map_comp_apply σ₁.op σ₂.op a).symm

instance : Preorder (CoherentShape Γ₁) := Subtype.preorder _

instance : OrderBot (CoherentShape Γ₁) where
  bot := ⟨⊥, .bot⟩
  bot_le a := Basis.Le.bot a.1

theorem le_def {a b : CoherentShape Γ₁} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

theorem le_bot_iff {a : CoherentShape Γ₁} : a ≤ ⊥ ↔ Basis.IsBottom a.1 := Basis.le_bot_iff

theorem Le.reindex (σ : Γ₂ ⟶ Γ₁) {a b : CoherentShape Γ₁} (h : a ≤ b) : reindex σ a ≤ reindex σ b :=
  h.map _ _

theorem compatible_of_le {a b c : CoherentShape Γ₁} (hac : a ≤ c) (hbc : b ≤ c) (σ : Γ₂ ⟶ Γ₁) :
    Shape.Compatible σ a.1 b.1 :=
  (Shape.Compatible.anti_left hbc (Shape.Compatible.anti_left hac (c.2.compatible_self σ)).symm).symm

def piAtom (label : Ty.Pair Γ₁) : CoherentShape Γ₁ :=
  ⟨.pi label .bot .nil, .forallE .bot (fun i => i.elim0) (fun i => i.elim0) fun i => i.elim0⟩

def piGenerator (label : Ty.Pair Γ₁) (a : CoherentShape Γ₁) (f : CoherentGraph Γ₁) :
    CoherentShape Γ₁ :=
  ⟨.pi label a.1 f.1, .forallE a.2 f.2.directed f.2.ins f.2.outs⟩

end CoherentShape

namespace CoherentGraph

noncomputable def reindex (σ : Γ₂ ⟶ Γ₁) (f : CoherentGraph Γ₁) : CoherentGraph Γ₂ := ⟨f.1.reindexHom σ, f.2.reindex σ⟩

@[simp] theorem reindex_val (σ : Γ₂ ⟶ Γ₁) (f : CoherentGraph Γ₁) : (f.reindex σ).1 = f.1.reindexHom σ := rfl

@[simp] theorem reindex_id (f : CoherentGraph Γ₁) : f.reindex (𝟙 Γ₁) = f :=
  Subtype.ext (Graph.reindexHom_id f.1)

@[simp] theorem reindex_reindex (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) (f : CoherentGraph Γ₁) :
    (f.reindex σ₁).reindex σ₂ = f.reindex (σ₂ ≫ σ₁) :=
  Subtype.ext (Graph.reindexHom_comp σ₁ σ₂ f.1).symm

def nil (Γ₁ : CtxCat E ℓ) : CoherentGraph Γ₁ :=
  ⟨.nil, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩

def single (label : Tm_ Γ₁) (a b : CoherentShape Γ₁) : CoherentGraph Γ₁ :=
  ⟨.single label a.1 b.1, ⟨fun _ _ _ σ _ _ => b.2.compatible_self (σ ≫ 𝟙 Γ₁), fun _ => a.2, fun _ => b.2⟩⟩

def append (f g : CoherentGraph Γ₁) (hfg : Graph.Compatible (𝟙 Γ₁) f.1 g.1) : CoherentGraph Γ₁ :=
  ⟨f.1.append g.1, f.2.append g.2 hfg⟩

def input (f : CoherentGraph Γ₁) (i : Fin f.1.size) : CoherentShape Γ₁ := ⟨f.1.ins i, f.2.ins i⟩

def output (f : CoherentGraph Γ₁) (i : Fin f.1.size) : CoherentShape Γ₁ := ⟨f.1.outs i, f.2.outs i⟩

def lamGenerator (f : CoherentGraph Γ₁) : CoherentShape Γ₁ := ⟨.abs f.1, .lam f.2.directed f.2.ins f.2.outs⟩

theorem lamGenerator_le_iff {f g : CoherentGraph Γ₁} :
    lamGenerator f ≤ lamGenerator g ↔ f.1 ≤ g.1 :=
  Basis.Le.abs_iff

theorem lamGenerator_le_bot_iff {f : CoherentGraph Γ₁} : lamGenerator f ≤ ⊥ ↔ f.1.IsBottom :=
  CoherentShape.le_bot_iff.trans Basis.IsBottom.lam_iff

end CoherentGraph

end Metalean
