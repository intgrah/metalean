/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Order.Presheaf.Ideal
public import Metalean.Semantics.Basis.Coherence

@[expose] public section

namespace Metalean

open CategoryTheory Opposite Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace Shape

def cSupBot (a b : Shape Γ) : Shape Γ := if Basis.IsBottom a then b else a

theorem cSupBot_induction {P : Shape Γ → Prop} {a b : Shape Γ} (ha : P a) (hb : P b) :
    P (cSupBot a b) := by
  unfold cSupBot
  split_ifs
  · exact hb
  · exact ha

theorem le_cSupBot {a b : Shape Γ} (h : Basis.IsBottom a ∨ Basis.IsBottom b) :
    a ≤ cSupBot a b ∧ b ≤ cSupBot a b := by
  unfold cSupBot
  split_ifs with hbot
  · exact ⟨.collapse hbot, .refl _⟩
  · exact ⟨.refl _, .collapse (h.resolve_left hbot)⟩

theorem map_cSupBot (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (piMap : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a b : Shape Γ₁) :
    (cSupBot a b).map arg piMap = cSupBot (a.map arg piMap) (b.map arg piMap) := by
  simp only [cSupBot, Basis.IsBottom.map_iff]
  split_ifs <;> rfl

def cSup : Shape Γ → Shape Γ → Shape Γ
  | .bot, b => b
  | a, .bot => a
  | .lam k names ins outs, .lam k' names' ins' outs' =>
    .abs (Graph.append ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  | .forallE label a k names ins outs, .forallE _ a' k' names' ins' outs' =>
    .pi label (cSup a a') (Graph.append ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  | .ctor head names fields, .ctor head' names' fields' =>
    if h : head = head' then .ctor head names fun i => cSup (fields i) (fields' (h ▸ i))
    else cSupBot (.ctor head names fields) (.ctor head' names' fields')
  | .struct head hstruct fields, .struct head' hstruct' fields' =>
    if h : head = head' then
      if Basis.IsBottom (.struct head hstruct fields) then .struct head' hstruct' fields'
      else .struct head hstruct fun i => cSup (fields i) (fields' (h ▸ i))
    else cSupBot (.struct head hstruct fields) (.struct head' hstruct' fields')
  | .ind code ctorTypes, .ind code' ctorTypes' =>
    if h : code.toIndHead.nctors = code'.toIndHead.nctors then
      .ind code fun c => cSup (ctorTypes c) (ctorTypes' (Fin.cast h c))
    else cSupBot (.ind code ctorTypes) (.ind code' ctorTypes')
  | .quotMk η name value, .quotMk _ _ value' => .quotMk η name (cSup value value')
  | a, b => cSupBot a b

theorem cSup_le {a b d : Shape Γ} (ha : a ≤ d) (hb : b ≤ d) :
    cSup a b ≤ d := by
  fun_induction cSup a b generalizing d
  · exact hb
  · exact ha
  · cases ha with
    | collapse ha =>
      cases hb with
      | collapse hb => exact .collapse (.lam (Graph.IsBottom.append
          (Basis.IsBottom.lam_iff.mp ha) (Basis.IsBottom.lam_iff.mp hb)))
      | lam hb => exact .lam (Graph.Le.append (.of_isBottom (Basis.IsBottom.lam_iff.mp ha)) hb)
    | lam ha =>
      cases hb with
      | collapse hb => exact .lam (Graph.Le.append ha (.of_isBottom (Basis.IsBottom.lam_iff.mp hb)))
      | lam hb => exact .lam (Graph.Le.append ha hb)
  · rename_i ih
    cases ha with
    | collapse h => nomatch h
    | forallE ha hf =>
      cases hb with
      | collapse h => nomatch h
      | forallE hb hg => exact .forallE (ih ha hb) (Graph.Le.append hf hg)
  · rename_i ih
    cases ha with
    | collapse h => nomatch h
    | ctor ha =>
      cases hb with
      | collapse h => nomatch h
      | ctor hb => exact .ctor fun i => ih i (ha i) (hb i)
  · exact cSupBot_induction (P := (· ≤ d)) ha hb
  · exact hb
  · rename_i ih
    cases ha with
    | collapse h => exact absurd h (by assumption)
    | struct ha =>
      cases hb with
      | collapse h => exact .struct fun i => ih i (ha i) ((Basis.IsBottom.struct_iff.mp h) i).le
      | struct hb => exact .struct fun i => ih i (ha i) (hb i)
  · exact cSupBot_induction (P := (· ≤ d)) ha hb
  · rename_i _ ih
    cases ha with
    | collapse h => nomatch h
    | ind ha =>
      cases hb with
      | collapse h => nomatch h
      | ind hb => exact .ind fun c => ih c (ha c) (hb c)
  · exact cSupBot_induction (P := (· ≤ d)) ha hb
  · rename_i ih
    cases ha with
    | collapse h => nomatch h
    | quotMk ha =>
      cases hb with
      | collapse h => nomatch h
      | quotMk hb => exact .quotMk (ih ha hb)
  · exact cSupBot_induction (P := (· ≤ d)) ha hb

theorem le_cSup {a b : Shape Γ} (h : Compatible (𝟙 Γ) a b) :
    a ≤ cSup a b ∧ b ≤ cSup a b := by
  fun_induction cSup a b
  · exact ⟨.bot _, .refl _⟩
  · exact ⟨.refl _, .bot _⟩
  · rename_i k names ins outs k' names' ins' outs'
    exact ⟨.lam (Graph.Le.append_left ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩),
      .lam (Graph.Le.append_right ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)⟩
  · rename_i label _ k names ins outs label' _ k' names' ins' outs' ih
    have ⟨hl, ha, _⟩ := h
    obtain rfl : label = label' := by simpa using hl
    have ⟨ha, hb⟩ := ih ha
    exact ⟨.forallE ha (Graph.Le.append_left ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩),
      .forallE hb (Graph.Le.append_right ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)⟩
  · rename_i head' names' fields' names fields ih
    have ⟨_, hc⟩ := h
    obtain rfl : names = names' := funext fun i => by simpa using (hc i i rfl).1
    exact ⟨.ctor fun i => (ih i (hc i i rfl).2).1, .ctor fun i => (ih i (hc i i rfl).2).2⟩
  · exact absurd h.1 (by assumption)
  · exact ⟨.collapse (by assumption), .refl _⟩
  · rename_i head' hstruct' fields' hstruct fields hnb ih
    rcases h with hbot | hbot | ⟨_, hc⟩
    · exact absurd hbot hnb
    · exact ⟨.struct fun i => (ih i (Compatible.of_isBottom_right _
        ((Basis.IsBottom.struct_iff.mp hbot) i))).1, .collapse hbot⟩
    · exact ⟨.struct fun i => (ih i (hc i i rfl)).1, .struct fun i => (ih i (hc i i rfl)).2⟩
  · refine le_cSupBot ?_
    rcases h with hbot | hbot | ⟨heq, _⟩
    · exact .inl hbot
    · exact .inr hbot
    · exact absurd heq (by assumption)
  · rename_i _ ih
    have ⟨hcode, hct⟩ := h
    rw [IndCode.map_hom_id, IndCode.map_hom_id] at hcode
    subst hcode
    exact ⟨.ind fun c => (ih c (hct c c rfl)).1, .ind fun c => (ih c (hct c c rfl)).2⟩
  · refine le_cSupBot ?_
    have hcode := h.1
    rw [IndCode.map_hom_id] at hcode
    exact absurd (congrArg (fun c : IndCode Γ => c.toIndHead.nctors) hcode) (by assumption)
  · rename_i η name value η' name' value' ih
    have ⟨hh, hn, hv⟩ := h
    subst η'
    obtain rfl : name = name' := by simpa using hn
    exact ⟨.quotMk (ih hv).1, .quotMk (ih hv).2⟩
  · rename_i a b hbot hbot' hlam hpi hctor hstruct hind hquotMk
    fun_cases Compatible (𝟙 Γ) a b
    · exact (hbot rfl).elim
    · exact (hbot' rfl).elim
    · cases h
      exact ⟨.refl _, .refl _⟩
    · exact (hpi _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
    · exact (hlam _ _ _ _ _ _ _ _ rfl rfl).elim
    · exact (hind _ _ _ _ rfl rfl).elim
    · exact (hctor _ _ _ _ _ _ rfl rfl).elim
    · exact (hstruct _ _ _ _ _ _ rfl rfl).elim
    · change QuotCode.map _ _ = QuotCode.map _ _ at h
      rw [QuotCode.map_hom_id, QuotCode.map_hom_id] at h
      subst h
      exact ⟨.refl _, .refl _⟩
    · exact (hquotMk _ _ _ _ _ _ rfl rfl).elim
    · simp only [Compatible] at h
      exact le_cSupBot h

theorem cSup_isCoherent {a b : Shape Γ} (h : Compatible (𝟙 Γ) a b)
    (ha : IsCoherent Γ a) (hb : IsCoherent Γ b) : IsCoherent Γ (cSup a b) := by
  fun_induction cSup a b
  · exact hb
  · exact ha
  · cases ha with | lam hd hi ho =>
      cases hb with | lam hd' hi' ho' =>
        have hc := Graph.IsCoherent.append ⟨hd, hi, ho⟩ ⟨hd', hi', ho'⟩ h
        exact .lam hc.directed hc.ins hc.outs
  · rename_i ih
    have ⟨_, hab, hfg⟩ := h
    cases ha with | forallE ha hd hi ho =>
      cases hb with | forallE hb hd' hi' ho' =>
        have hc := Graph.IsCoherent.append ⟨hd, hi, ho⟩ ⟨hd', hi', ho'⟩ hfg
        exact .forallE (ih hab ha hb) hc.directed hc.ins hc.outs
  · rename_i ih
    have ⟨_, hc⟩ := h
    cases ha with | ctor hns ha =>
      cases hb with | ctor _ hb => exact .ctor hns fun i => ih i (hc i i rfl).2 (ha i) (hb i)
  · exact cSupBot_induction ha hb
  · exact hb
  · rename_i ih
    have .struct ha := ha
    have .struct hb := hb
    rcases h with hbot | hbot | ⟨_, hc⟩
    · exact absurd hbot (by assumption)
    · exact .struct fun i => ih i (Compatible.of_isBottom_right _
        ((Basis.IsBottom.struct_iff.mp hbot) i)) (ha i) (hb i)
    · exact .struct fun i => ih i (hc i i rfl) (ha i) (hb i)
  · exact cSupBot_induction ha hb
  · rename_i _ ih
    have ⟨hcode, hct⟩ := h
    rw [IndCode.map_hom_id] at hcode
    subst hcode
    cases ha with | ind ha =>
      cases hb with | ind hb => exact .ind fun c => ih c (hct c c rfl) (ha c) (hb c)
  · exact cSupBot_induction ha hb
  · rename_i ih
    cases ha with | quotMk ha =>
      cases hb with | quotMk hb => exact .quotMk (ih h.2.2 ha hb)
  · exact cSupBot_induction ha hb

theorem map_cSup (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (piMap : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a b : Shape Γ₁) : (cSup a b).map arg piMap = cSup (a.map arg piMap) (b.map arg piMap) := by
  induction a generalizing b with
  | ctor head names fields ih =>
    cases b with
    | ctor head' names' fields' =>
      by_cases h : head = head'
      · subst h
        simp only [cSup, map]
        split_ifs <;> simp_all [map]
      · simp [cSup, map, h, map_cSupBot]
    | _ => simp [cSup, map, map_cSupBot]
  | struct head hstruct fields ih =>
    cases b with
    | struct head' hstruct' fields' =>
      by_cases h : head = head'
      · subst h
        simp only [cSup, map]
        split_ifs <;> simp_all [map]
      · simp [cSup, map, h, map_cSupBot]
    | _ => simp [cSup, map, map_cSupBot]
  | ind code ctorTypes ih =>
    cases b with
    | ind code' ctorTypes' =>
      by_cases h : code.toIndHead.nctors = code'.toIndHead.nctors
      · simp only [cSup, map, dite_eq_left h]
        exact congrArg _ (funext fun c => ih c _)
      · simp [cSup, map, dite_eq_right h, map_cSupBot]
    | _ => simp [cSup, map, map_cSupBot]
  | quotMk _ _ _ ih => cases b <;> simp [cSup, map, ih, map_cSupBot]
  | _ =>
    cases b <;> simp_all only [cSup, map, map_cSupBot]
    all_goals congr 1 <;> funext i <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [Graph.append]

theorem cSup_compatible {a b d : Shape Γ₁} (σ : Γ₂ ⟶ Γ₁)
    (ha : Compatible σ a d) (hb : Compatible σ b d) : Compatible σ (cSup a b) d := by
  fun_induction cSup a b generalizing d
  · exact hb
  · exact ha
  · cases d with
    | lam _ _ _ _ => exact Graph.Compatible.append_left (h := ⟨_, _, _, _⟩) ha hb
    | bot => trivial
    | _ =>
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact .inl (.lam (Graph.IsBottom.append (Basis.IsBottom.lam_iff.mp ha)
            (Basis.IsBottom.lam_iff.mp hb)))
        · exact .inr hb
      · exact .inr ha
  · rename_i ih
    cases d with
    | forallE _ _ _ _ _ _ =>
      have ⟨hl, ha, hf⟩ := ha
      have ⟨_, hb, hg⟩ := hb
      exact ⟨hl, ih ha hb, Graph.Compatible.append_left (h := ⟨_, _, _, _⟩) hf hg⟩
    | bot => trivial
    | _ => exact ha.imp (fun h => nomatch h) id
  · rename_i ih
    cases d with
    | ctor _ _ _ =>
      exact ⟨ha.1, fun i j hij => ⟨(ha.2 i j hij).1, ih i (ha.2 i j hij).2 (hb.2 i j hij).2⟩⟩
    | bot => trivial
    | _ => exact ha.imp (fun h => nomatch h) id
  · exact cSupBot_induction (P := (Compatible σ · d)) ha hb
  · exact hb
  · rename_i hnb ih
    cases d with
    | struct _ _ _ =>
      rcases ha with hba | hd | ⟨hh, ha⟩
      · exact absurd hba hnb
      · exact .inr (.inl hd)
      · rcases hb with hbb | hd | ⟨_, hb⟩
        · exact .inr (.inr ⟨hh, fun i j hij =>
            ih i (ha i j hij) (Compatible.of_isBottom_left _
              ((Basis.IsBottom.struct_iff.mp hbb) i))⟩)
        · exact .inr (.inl hd)
        · exact .inr (.inr ⟨hh, fun i j hij => ih i (ha i j hij) (hb i j hij)⟩)
    | bot => trivial
    | _ => exact .inr (ha.resolve_left hnb)
  · exact cSupBot_induction (P := (Compatible σ · d)) ha hb
  · rename_i _ ih
    cases d with
    | ind _ _ =>
      exact ⟨ha.1, fun c c' hcc => ih c (ha.2 c c' hcc) (hb.2 _ c' hcc)⟩
    | bot => trivial
    | _ => exact ha.imp (fun h => nomatch h) id
  · exact cSupBot_induction (P := (Compatible σ · d)) ha hb
  · rename_i ih
    cases d with
    | quotMk _ _ _ => exact ⟨ha.1, ha.2.1, ih ha.2.2 hb.2.2⟩
    | bot => trivial
    | _ => exact ha.imp (fun h => nomatch h) id
  · exact cSupBot_induction (P := (Compatible σ · d)) ha hb

end Shape

namespace CoherentShape

theorem compatible_of_upper {a b : CoherentShape Γ} (h : ∃ c, a ≤ c ∧ b ≤ c) :
    Shape.Compatible (𝟙 Γ) a.1 b.1 :=
  have ⟨_, hac, hbc⟩ := h
  compatible_of_le hac hbc _

theorem upper_of_compatible {a b : CoherentShape Γ} (h : Shape.Compatible (𝟙 Γ) a.1 b.1) :
    ∃ c, a ≤ c ∧ b ≤ c :=
  ⟨⟨_, Shape.cSup_isCoherent h a.2 b.2⟩, Shape.le_cSup h⟩

instance : CondSemilatticeSup (CoherentShape Γ) where
  cSup a b h := ⟨Shape.cSup a.1 b.1, Shape.cSup_isCoherent (compatible_of_upper h) a.2 b.2⟩
  le_cSup_left _ _ h := (Shape.le_cSup (compatible_of_upper h)).1
  le_cSup_right _ _ h := (Shape.le_cSup (compatible_of_upper h)).2
  cSup_le _ := Shape.cSup_le

@[implicit_reducible] noncomputable def pointedOrder (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ CondSemilatSup where
  obj Γ₁ := CondSemilatSup.of (CoherentShape Γ₁.unop)
  map σ := CondSemilatSup.ofHom {
    toFun := reindex σ.unop
    monotone' _ _ h := Le.reindex σ.unop h
    map_bot' := rfl
    map_cSup' a b _ _ hda hdb := by
      change Shape.map _ _ (Shape.cSup a.1 b.1) ≤ _
      rw [Shape.map_cSup]
      exact Shape.cSup_le hda hdb }
  map_id _ := CondSemilatSup.ext reindex_id
  map_comp σ₁ σ₂ := CondSemilatSup.ext fun a => (reindex_reindex σ₁.unop σ₂.unop a).symm

@[simp] theorem pointedOrder_map {Γ₁ Γ₂ : (CtxCat E ℓ)ᵒᵖ} (σ : Γ₁ ⟶ Γ₂)
    (a : CoherentShape Γ₁.unop) : (pointedOrder E ℓ).map σ a = reindex σ.unop a := rfl

noncomputable abbrev order (E : Env ζ) (ℓ : Nat) := pointedOrder E ℓ ⋙ forget₂ CondSemilatSup Preord

abbrev RawValue (Γ₁ : CtxCat E ℓ) := ΩLower (pointedOrder E ℓ) Γ₁

abbrev Domain (Γ₁ : CtxCat E ℓ) := ΩIdeal (pointedOrder E ℓ) Γ₁

noncomputable abbrev principalIdeal (a : CoherentShape Γ) : Domain Γ :=
  ΩIdeal.principal (pointedOrder E ℓ) a

@[simp]
theorem principalIdeal_mem (a : CoherentShape Γ₁) (σ : Γ₂ ⟶ Γ₁) (b : CoherentShape Γ₂) :
    (principalIdeal a).mem σ b ↔ b ≤ reindex σ a :=
  ΩIdeal.mem_principal (R := pointedOrder E ℓ) a σ b

theorem principalIdeal_mono {a b : CoherentShape Γ} (h : a ≤ b) :
    principalIdeal a ≤ principalIdeal b :=
  ΩLower.principal_mono h

end CoherentShape

end Metalean
