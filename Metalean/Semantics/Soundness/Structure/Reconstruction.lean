/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Decoder
import Metalean.Semantics.Domain.Inductive.Decoder
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {maj : Expr ζ ℓ Γ₁.as.len}

theorem RawTyped.structural_value_bot
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
    (hrel : Level.rel ((E.get η).block.level.inst ls) = false)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ = ⊥ := by
  have ht := hs.indTypeStrong hps
  have htype := HasFixedness.ind (IndTyping.ofTyping hB ht) hB ht σ ρ hρ
  rw [rawInterpret_sort] at htype
  conv_lhs at htype => arg 2; rw [show (E.get η).block.level.inst ls = .zero by simpa using hrel]
  exact (pmaj.fixed pmaj.typed σ ρ hρ).symm.trans
    (piLimit_rawExtend_prop _ htype _ _)

theorem HasEquality.structure_eta_of_projections
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (pfn : ∀ d : Fin (ι.nctors s), RawInterpretationProperties (CtxCat.nil E ℓ)
      (((E.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E.get η).block.paramType ls ps p))
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
    (hproj : ∀ (f : Fin (ι.ctors s c).nfields) {Γ₂ : CtxCat E ℓ}
      (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂), SourceAdmissible σ ρ →
        (rawInterpret (piLimit E ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ.op ρ =
          RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
            ((rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ)) :
    HasEquality Γ₁ (hs.rebuildTerm η ls ps maj) maj := by
  let hctor : CtorTyping Γ₁ η s c ls ps (fun f => hs.projTerm η ls ps f maj) hs.recursive := {
    ordinary f := by
      simpa [Inductive.IsStructure.projType_eq] using
        hs.projTerm_hasTypeStrong hB f Γ₁.as.wf (fun p => (pps p).typed) pmaj.typed
    recursive := hs.no_recursive.elim }
  intro Γ₂ σ ρ hρ
  change (rawInterpret (piLimit E ℓ) Γ₁ (.ctor η s c ls ps
    (fun f => hs.projTerm η ls ps f maj) hs.recursive)).app _ σ.op ρ = _
  cases hrel : Level.rel ((E.get η).block.level.inst ls) with
  | false =>
    rw [rawInterpret_ctor_prop _ hrel,
      pmaj.structural_value_bot hs hB (fun p => (pps p).typed) hrel σ ρ hρ]
    rfl
  | true =>
    rw [rawInterpret_ctor_typed _ hctor hrel, RawFamily.ctor_value]
    have heq : (fun i => (rawInterpret (piLimit E ℓ) Γ₁
        (Fin.append (fun f => hs.projTerm η ls ps f maj) hs.recursive i)).app _ σ.op ρ) =
        fun i => RawValue.proj ⟨η, s, c⟩ i
          ((rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ) := by
      funext i
      cases i using Fin.addCases with
      | left f => simpa using hproj f σ ρ hρ
      | right f => exact hs.no_recursive.elim f
    rw [heq]
    let hi := IndTyping.ofTyping hB (hs.indTypeStrong fun p => (pps p).typed)
    let hg : hi.code.StructGuard c (Tm.label Γ₁.as pmaj.typed) := ⟨{
      params := ps
      struct := hs
      block := hB
      typed := hi.param
      params_eq := fun _ => rfl
      guard := rfl }⟩
    have hfix := pmaj.fixed pmaj.typed σ ρ hρ
    rw [rawInterpret_ind_typed _ hi hB] at hfix
    exact ctor_proj_of_structural_fixed (hi.code.map ((Tm E ℓ).map σ.op))
      ((IndCode.rel_map _ _).trans (hi.code_rel.trans hrel)) (hg.pullback σ)
      (ctorFieldTypes (fun d => (pfn d).ideal) (fun p => Tm.label Γ₁.as (hi.param p))
        σ ρ fun p => (pps p).term.ideal σ ρ hρ) (hρ.eval pmaj.term.ideal) hfix _

theorem RawTyped.structural_field_telescope
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (hrel : Level.rel ((E.get η).block.level.inst ls) = true)
    (pfn : ∀ d : Fin (ι.nctors s), HasIdeality (CtxCat.nil E ℓ)
      (((E.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pps : ∀ p, HasIdeality Γ₁ (ps p))
    (pmaj : RawTyped Γ₁ maj (.ind η s ls ps hs.indices))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    ((piLimit E ℓ).telescope
      (ctorFieldTypes pfn (fun p => Tm.label Γ₁.as (hps p)) σ ρ (fun p => pps p σ ρ hρ) c)
      (fun f => (Tm E ℓ).map σ.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.typed)))
      fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.term.ideal)).1 =
      fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.term.ideal) := by
  have ht := hs.indTypeStrong hps
  have hi : IndTyping Γ₁ η s ls ps hs.indices := IndTyping.ofTyping hB ht
  let w : hi.code.StructWitness c (Tm.label Γ₁.as pmaj.typed) := {
    params := ps
    struct := hs
    block := hB
    typed := hi.param
    params_eq := fun _ => rfl
    guard := rfl }
  let hg : hi.code.StructGuard c (Tm.label Γ₁.as pmaj.typed) := ⟨w⟩
  let types := ctorFieldTypes pfn (fun p => Tm.label Γ₁.as (hi.param p)) σ ρ fun p => pps p σ ρ hρ
  have hfix := pmaj.fixed pmaj.typed σ ρ hρ
  rw [rawInterpret_ind_typed _ hi hB] at hfix
  have hd := telescope_of_structural_fixed (hi.code.map ((Tm E ℓ).map σ.op))
    ((IndCode.rel_map _ _).trans (hi.code_rel.trans hrel)) (hg.pullback σ)
    types (hρ.eval pmaj.term.ideal) hfix
  have hnames : indNames (hg.pullback σ) = Fin.append
      (fun f => (Tm E ℓ).map σ.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.typed)))
      hs.no_recursive.elim := by
    funext i
    rw [← map_indNames hg σ (hg.pullback σ) i]
    cases i using Fin.addCases with
    | left f =>
      change Fin (ι.ctors s c).nfields at f
      simp only [indNames, IndTyping.code, Fin.append_left]
      exact congrArg ((Tm E ℓ).map σ.op) (Tm.projOfCode_eq_proj hg w f)
    | right f => exact hs.no_recursive.elim f
  have hargs : (fun i => projIdeal (hi.code.ctorHead c) i (hρ.eval pmaj.term.ideal)) =
      Fin.append (fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.term.ideal))
        hs.no_recursive.elim := by
    rw [← Fin.append_castAdd_natAdd (f := fun i => projIdeal (hi.code.ctorHead c) i (hρ.eval pmaj.term.ideal))]
    congr 1
    exact funext hs.no_recursive.elim
  rw [hnames, hargs] at hd
  have hdrop {k : Nat} (names : Fin k → Tm_ Γ₂) (args : Fin k → Domain Γ₂) :
      ∀ (ns : Fin (ι.ctors s c).nrecFields → Tm_ Γ₂)
        (xs : Fin (ι.ctors s c).nrecFields → Domain Γ₂),
        ((piLimit E ℓ).telescope (types c) (Fin.append names ns) (Fin.append args xs)).1 =
          Fin.append args xs → ((piLimit E ℓ).telescope (types c) names args).1 = args := by
    rw [Fin.eq_zero_of_isEmpty hs.no_recursive]
    intro ns xs heq
    simpa using heq
  exact hdrop _ _ _ _ hd

end Metalean.CoherentShape
