/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Decide
public import Metalean.Semantics.Basis.Shape
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}
  {r : Level ℓ} {label : Ty.Pair Γ₁} {a : Shape Γ₁} {k : Nat}
  {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁} {code : IndCode Γ₁}
  {ctorTypes : Fin code.toIndHead.nctors → Shape Γ₁} {qcode : QuotCode Γ₁} {η : Head ζ .quot}
  {name : Tm_ Γ₁} {head : CtorHead ζ} {labels : Fin head.arity → Tm_ Γ₁}
  {hstruct : head.IsStructural E} {fields : Fin head.arity → Shape Γ₁}

namespace Basis

judgement IsBottom : Shape Γ₁ → Prop where

  ──────────────────── bot
  IsBottom .bot

  ∀ i, IsBottom (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁}
  IsBottom (.lam k names ins outs)

  ∀ i, IsBottom (fields i)
  ──────────────────── struct {head : CtorHead ζ} {hstruct : head.IsStructural E}
    {fields : Fin head.arity → Shape Γ₁}
  IsBottom (.struct head hstruct fields)

mutual

judgement Le : Shape Γ₁ → Shape Γ₁ → Prop where

  IsBottom a
  ──────────────────── collapse {a b : Shape Γ₁}
  Le a b

  ──────────────────── sort (r : Level ℓ)
  Le (.sort r) (.sort r)

  Le a a'
  ∀ i, Entry ⟨k', names', ins', outs'⟩ (names i) (ins i) (outs i)
  ──────────────────── forallE {label : Ty.Pair Γ₁} {a a' : Shape Γ₁} {k : Nat} {names : Fin k → Tm_ Γ₁}
    {ins outs : Fin k → Shape Γ₁} {k' : Nat} {names' : Fin k' → Tm_ Γ₁}
    {ins' outs' : Fin k' → Shape Γ₁}
  Le (.forallE label a k names ins outs) (.forallE label a' k' names' ins' outs')

  ∀ i, Entry ⟨k', names', ins', outs'⟩ (names i) (ins i) (outs i)
  ──────────────────── lam {k : Nat} {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁} {k' : Nat}
    {names' : Fin k' → Tm_ Γ₁} {ins' outs' : Fin k' → Shape Γ₁}
  Le (.lam k names ins outs) (.lam k' names' ins' outs')

  ∀ c, Le (ctorTypes c) (ctorTypes' c)
  ──────────────────── ind {code : IndCode Γ₁}
    {ctorTypes ctorTypes' : Fin code.toIndHead.nctors → Shape Γ₁}
  Le (.ind code ctorTypes) (.ind code ctorTypes')

  ∀ i, Le (fields i) (fields' i)
  ──────────────────── ctor {head : CtorHead ζ} {names : Fin head.arity → Tm_ Γ₁}
    {fields fields' : Fin head.arity → Shape Γ₁}
  Le (.ctor head names fields) (.ctor head names fields')

  ∀ i, Le (fields i) (fields' i)
  ──────────────────── struct {head : CtorHead ζ} {hstruct : head.IsStructural E}
    {fields fields' : Fin head.arity → Shape Γ₁}
  Le (.struct head hstruct fields) (.struct head hstruct fields')

  ──────────────────── quot (code : QuotCode Γ₁)
  Le (.quot code) (.quot code)

  Le value value'
  ──────────────────── quotMk {η : Head ζ .quot} {name : Tm_ Γ₁}
    {value value' : Shape Γ₁}
  Le (.quotMk η name value) (.quotMk η name value')

judgement Entry : Graph Γ₁ → (Tm_ Γ₁) → Shape Γ₁ → Shape Γ₁ → Prop where

  IsBottom y
  ──────────────────── bottom {g : Graph Γ₁} {name : Tm_ Γ₁} {x y : Shape Γ₁}
  Entry g name x y

  g.names j = name
  Le (g.ins j) x
  Le y (g.outs j)
  ──────────────────── mem {g : Graph Γ₁} {name : Tm_ Γ₁} {x y : Shape Γ₁} (j : Fin g.size)
  Entry g name x y

end

@[simp] theorem IsBottom.not_sort : ¬ IsBottom (Shape.sort r : Shape Γ₁) := nofun

@[simp] theorem IsBottom.not_forallE : ¬ IsBottom (Shape.forallE label a k names ins outs) := nofun

@[simp] theorem IsBottom.not_ind : ¬ IsBottom (Shape.ind code ctorTypes) := nofun

@[simp] theorem IsBottom.not_quot : ¬ IsBottom (Shape.quot qcode) := nofun

@[simp] theorem IsBottom.not_quotMk : ¬ IsBottom (Shape.quotMk η name a) := nofun

@[simp] theorem IsBottom.not_ctor : ¬ IsBottom (Shape.ctor head labels fields) := nofun

@[simp] theorem IsBottom.lam_iff : IsBottom (Shape.lam k names ins outs) ↔ ∀ i, IsBottom (outs i) :=
  ⟨fun | .lam h => h, .lam⟩

@[simp] theorem IsBottom.struct_iff :
    IsBottom (Shape.struct head hstruct fields) ↔ ∀ i, IsBottom (fields i) :=
  ⟨fun | .struct h => h, .struct⟩

def IsBottom.decidable : (a : Shape Γ₁) → Decidable (IsBottom a)
  | .bot => isTrue .bot
  | .lam _ _ _ outs =>
    letI : ∀ i, Decidable (IsBottom (outs i)) := fun i => IsBottom.decidable (outs i)
    decidable_of_iff _ lam_iff.symm
  | .struct _ _ fields =>
    letI : ∀ i, Decidable (IsBottom (fields i)) := fun i => IsBottom.decidable (fields i)
    decidable_of_iff _ struct_iff.symm
  | .sort _ | .forallE _ _ _ _ _ _ | .ind _ _ | .ctor _ _ _ | .quot _ | .quotMk _ _ _ => isFalse nofun

instance (a : Shape Γ₁) : Decidable (IsBottom a) := IsBottom.decidable a

instance : LE (Shape Γ₁) := ⟨Basis.Le⟩

theorem Le.bot (b : Shape Γ₁) : (.bot : Shape Γ₁) ≤ b := .collapse .bot

theorem IsBottom.le {a b : Shape Γ₁} (h : IsBottom a) : a ≤ b := .collapse h

theorem le_bot_iff {a : Shape Γ₁} : a ≤ .bot ↔ IsBottom a :=
  ⟨fun | .collapse h => h, .collapse⟩

variable (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) in
theorem IsBottom.map {a : Shape Γ₁} : IsBottom a → IsBottom (a.map arg pi)
  | .bot => .bot
  | .lam h => .lam fun i => map (h i)
  | .struct h => .struct fun i => map (h i)

theorem IsBottom.of_map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) {a : Shape Γ₁} :
    IsBottom (a.map arg pi) → IsBottom a := by
  intro h
  induction a with
  | bot => exact .bot
  | lam _ _ _ _ _ iho =>
    have .lam h := h
    exact .lam fun i => iho i (h i)
  | struct _ _ _ ih =>
    have .struct h := h
    exact .struct fun i => ih i (h i)
  | _ => nomatch h

@[simp] theorem IsBottom.map_iff (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂)
    {a : Shape Γ₁} : IsBottom (a.map arg pi) ↔ IsBottom a :=
  ⟨of_map arg pi, map arg pi⟩

end Basis

namespace Graph

def Le (f g : Graph Γ₁) : Prop := ∀ i, Basis.Entry g (f.names i) (f.ins i) (f.outs i)

instance : LE (Graph Γ₁) := ⟨Graph.Le⟩

abbrev IsBottom (g : Graph Γ₁) : Prop := ∀ i, Basis.IsBottom (g.outs i)

theorem Le.of_isBottom {f g : Graph Γ₁} (hf : f.IsBottom) : f ≤ g := fun i => .bottom (hf i)

end Graph

namespace Basis

theorem Le.forallE_inv {label label' : Ty.Pair Γ₁} {a a' : Shape Γ₁} {k k' : Nat}
    {names : Fin k → Tm_ Γ₁} {ins outs : Fin k → Shape Γ₁} {names' : Fin k' → Tm_ Γ₁}
    {ins' outs' : Fin k' → Shape Γ₁}
    (h : Shape.forallE label a k names ins outs ≤
      Shape.forallE label' a' k' names' ins' outs') :
    label = label' ∧ a ≤ a' ∧ (⟨k, names, ins, outs⟩ : Graph Γ₁) ≤ ⟨k', names', ins', outs'⟩ := by
  cases h with
  | collapse h => nomatch h
  | forallE ha hf => exact ⟨rfl, ha, hf⟩

theorem Le.abs_iff {f g : Graph Γ₁} : Shape.abs f ≤ Shape.abs g ↔ f ≤ g := by
  refine ⟨fun h => ?_, .lam⟩
  cases h with
  | collapse h => cases h with | lam h => exact Graph.Le.of_isBottom h
  | lam hf => exact hf

theorem Le.refl : ∀ a : Shape Γ₁, a ≤ a
  | .bot => bot .bot
  | .sort r => sort r
  | .forallE _ a _ _ ins outs =>
    forallE (refl a) fun i => .mem i rfl (refl (ins i)) (refl (outs i))
  | .lam _ _ ins outs => lam fun i => .mem i rfl (refl (ins i)) (refl (outs i))
  | .ind _ ctorTypes => ind fun c => refl (ctorTypes c)
  | .ctor _ _ fields => ctor fun i => refl (fields i)
  | .struct _ _ fields => struct fun i => refl (fields i)
  | .quot code => quot code
  | .quotMk _ _ value => quotMk (refl value)

theorem Le.trans {a b c : Shape Γ₁} : a ≤ b → b ≤ c → a ≤ c
  | .collapse h, _ => collapse h
  | .sort _, hbc => hbc
  | .quot _, hbc => hbc
  | .forallE _ _, .collapse h => nomatch h
  | .forallE ha hf, .forallE hb hg => forallE (ha.trans hb) fun i =>
    match hf i with
    | .bottom hy => .bottom hy
    | .mem j hn hin hout =>
      match hg j with
      | .bottom hy => .bottom (le_bot_iff.mp (hout.trans hy.le))
      | .mem l hn' hin' hout' => .mem l (hn'.trans hn) (hin'.trans hin) (hout.trans hout')
  | .lam hf, .collapse (.lam hg) => collapse (.lam fun i =>
    match hf i with
    | .bottom hy => hy
    | .mem j _ _ hout => le_bot_iff.mp (hout.trans (hg j).le))
  | .lam hf, .lam hg => lam fun i =>
    match hf i with
    | .bottom hy => .bottom hy
    | .mem j hn hin hout =>
      match hg j with
      | .bottom hy => .bottom (le_bot_iff.mp (hout.trans hy.le))
      | .mem l hn' hin' hout' => .mem l (hn'.trans hn) (hin'.trans hin) (hout.trans hout')
  | .ctor _, .collapse h => nomatch h
  | .ctor hab, .ctor hbc => ctor fun i => (hab i).trans (hbc i)
  | .struct hab, .collapse (.struct hb) =>
    collapse (.struct fun i => le_bot_iff.mp ((hab i).trans (hb i).le))
  | .struct hab, .struct hbc => struct fun i => (hab i).trans (hbc i)
  | .quotMk _, .collapse h => nomatch h
  | .quotMk hab, .quotMk hbc => quotMk (hab.trans hbc)
  | .ind _, .collapse h => nomatch h
  | .ind hab, .ind hbc => ind fun c => (hab c).trans (hbc c)

theorem IsBottom.of_le {a b : Shape Γ₁} (hab : a ≤ b) (hb : IsBottom b) : IsBottom a :=
  le_bot_iff.mp (Le.trans hab hb.le)

mutual

theorem Le.map (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂)
    {a b : Shape Γ₁} :
    a ≤ b →
    a.map arg pi ≤ b.map arg pi
  | .collapse h => .collapse (h.map arg pi)
  | .sort r => .sort r
  | .forallE ha hf => .forallE (Le.map arg pi ha) fun i => Entry.map arg pi (hf i)
  | .lam hf => .lam fun i => Entry.map arg pi (hf i)
  | .ind h => .ind fun c => Le.map arg pi (h c)
  | .ctor h => .ctor fun i => Le.map arg pi (h i)
  | .struct h => .struct fun i => Le.map arg pi (h i)
  | .quot _ => .quot _
  | .quotMk h => .quotMk (Le.map arg pi h)

theorem Entry.map (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂)
    {g : Graph Γ₁} {name : Tm_ Γ₁} {x y : Shape Γ₁} :
    Entry g name x y →
    Entry (g.map arg pi) (arg name) (x.map arg pi) (y.map arg pi)
  | .bottom h => .bottom (h.map arg pi)
  | .mem j hn hin hout => .mem j (congrArg arg hn) (Le.map arg pi hin) (Le.map arg pi hout)

end

end Basis

instance : Preorder (Shape Γ₁) where
  le := (· ≤ ·)
  le_refl := Basis.Le.refl
  le_trans _ _ _ := Basis.Le.trans

instance : OrderBot (Shape Γ₁) where
  bot := .bot
  bot_le := Basis.Le.bot

namespace Graph.Le

theorem refl (f : Graph Γ₁) : f ≤ f := fun i => .mem i rfl (Basis.Le.refl _) (Basis.Le.refl _)

theorem append_left (f g : Graph Γ₁) : f ≤ f.append g := fun i =>
  .mem (Fin.castAdd g.size i) (append_names_left f g i) (append_ins_left f g i).le
    (append_outs_left f g i).ge

theorem append_right (f g : Graph Γ₁) : g ≤ f.append g := fun i =>
  .mem (Fin.natAdd f.size i) (append_names_right f g i) (append_ins_right f g i).le
    (append_outs_right f g i).ge

theorem append {f g h : Graph Γ₁} (hf : f ≤ h) (hg : g ≤ h) : f.append g ≤ h := fun i =>
  Fin.addCases (fun i => by simpa using hf i) (fun i => by simpa using hg i) i

end Graph.Le

theorem Graph.IsBottom.append {f g : Graph Γ₁} (hf : f.IsBottom)
    (hg : g.IsBottom) : (f.append g).IsBottom := fun i =>
  Fin.addCases (fun i => by simpa using hf i) (fun i => by simpa using hg i) i

end Metalean
