/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Admissible
import Metalean.Semantics.Domain.Inductive.Decoder
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ Γ₂ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {maj : Expr ζ ℓ Γ₁.as.len}

theorem RawJudgment.structural_value_bot
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (hrel : Level.rel ((E.get η).block.level.inst ls) = false)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ = ⊥ := by
  have ht := hs.indTypeStrong hps
  have htype := HasFixedness.ind (IndTyping.ofTyping hB ht) hB ht σ ρ hρ
  rw [rawInterpret_sort] at htype
  conv_lhs at htype => arg 2; rw [show (E.get η).block.level.inst ls = .zero by simpa using hrel]
  exact (pmaj.fixed pmaj.syntactic.left σ ρ hρ).symm.trans
    (piLimit_rawExtend_prop _ htype _ _)

theorem RawJudgment.structural_reconstruct
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (pfn : ∀ d : Fin (ι.nctors s), RawInterpretationProperties (CtxCat.nil E ℓ)
      (((E.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ)
    (names : Fin (CtorHead.mk η s c).arity → Tm_ Γ₂) :
    RawValue.ctor ⟨η, s, c⟩ names
      (fun i => RawValue.proj ⟨η, s, c⟩ i ((rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ)) =
      (rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ := by
  have ht := hs.indTypeStrong fun p => (pps p).syntactic.left
  have hT : IndTyping Γ₁ η s ls ps hs.indices := IndTyping.ofTyping hB ht
  cases hrel : Level.rel ((E.get η).block.level.inst ls)
  · rw [pmaj.structural_value_bot hs hB (fun p => (pps p).syntactic.left) hrel σ ρ hρ]
    simpa using RawValue.ctor_bot (CtorHead.mk η s c) hs names
  · let hg : hT.code.StructGuard c (Tm.label Γ₁.as pmaj.syntactic.left) := ⟨{
      params := ps
      struct := hs
      block := hB
      typed := hT.param
      params_eq := fun _ => rfl
      guard := rfl }⟩
    let types := ctorFieldTypes (fun d => (pfn d).ideal) (fun p => Tm.label Γ₁.as (hT.param p))
      σ ρ fun p => (pps p).left.ideal σ ρ hρ
    have hfix := pmaj.fixed pmaj.syntactic.left σ ρ hρ
    rw [rawInterpret_ind_typed _ hT hB] at hfix
    exact ctor_proj_of_structural_fixed (hT.code.map ((Tm E ℓ).map σ.op))
      ((IndCode.rel_map _ _).trans (hT.code_rel.trans hrel)) (hg.pullback σ)
      types (hρ.eval pmaj.left.ideal) hfix names

theorem HasEquality.structure_eta_of_projections
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (pfn : ∀ d : Fin (ι.nctors s), RawInterpretationProperties (CtxCat.nil E ℓ)
      (((E.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E.get η).block.paramType ls ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (hproj : ∀ (f : Fin (ι.ctors s c).nfields) {Γ₂ : CtxCat E ℓ}
      (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂), SourceAdmissible σ ρ →
        (rawInterpret (piLimit E ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ.op ρ =
          RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
            ((rawInterpret (piLimit E ℓ) Γ₁ maj).app _ σ.op ρ)) :
    HasEquality Γ₁ (hs.rebuildTerm η ls ps maj) maj := by
  have ht := hs.indTypeStrong fun p => (pps p).syntactic.left
  let hctor : CtorTyping Γ₁ η s c ls ps (fun f => hs.projTerm η ls ps f maj) hs.recursive := {
    ordinary f := by
      simpa [Inductive.IsStructure.projType_eq] using
        hs.projTerm_hasTypeStrong hB f Γ₁.as.wf (fun p => (pps p).syntactic.left) pmaj.syntactic.left
    recursive := hs.no_recursive.elim }
  intro Γ₂ σ ρ hρ
  change (rawInterpret (piLimit E ℓ) Γ₁ (.ctor η s c ls ps
    (fun f => hs.projTerm η ls ps f maj) hs.recursive)).app _ σ.op ρ = _
  cases hrel : Level.rel ((E.get η).block.level.inst ls) with
  | false =>
    rw [rawInterpret_ctor_prop _ hrel,
      pmaj.structural_value_bot hs hB (fun p => (pps p).syntactic.left) hrel σ ρ hρ]
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
    exact pmaj.structural_reconstruct hs hB pfn pps σ ρ hρ _

theorem RawJudgment.structural_field_telescope
    (hs : (E.get η).block.IsStructure s c) (hB : (E.get η).block.WFStrong E)
    (hrel : Level.rel ((E.get η).block.level.inst ls) = true)
    (pfn : ∀ d : Fin (ι.nctors s), HasIdeality (CtxCat.nil E ℓ)
      (((E.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pps : ∀ p, HasIdeality Γ₁ (ps p))
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ)
    (T : Domain Γ₂)
    (hT : T.val = (RawFamily.closedApps
      (rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) (((E.get η).block.ctorTypeFn s c).instL fun p => ls p))
      (fun p => Tm.label Γ₁.as (hps p))
      fun p => rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ.op ρ) :
    ((piLimit E ℓ).telescope T
      (fun f => (Tm E ℓ).map σ.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.syntactic.left)))
      fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.left.ideal)).1 =
      fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.left.ideal) := by
  have ht := hs.indTypeStrong hps
  have hi : IndTyping Γ₁ η s ls ps hs.indices := IndTyping.ofTyping hB ht
  let w : hi.code.StructWitness c (Tm.label Γ₁.as pmaj.syntactic.left) := {
    params := ps
    struct := hs
    block := hB
    typed := hi.param
    params_eq := fun _ => rfl
    guard := rfl }
  let hg : hi.code.StructGuard c (Tm.label Γ₁.as pmaj.syntactic.left) := ⟨w⟩
  let types := ctorFieldTypes pfn (fun p => Tm.label Γ₁.as (hi.param p)) σ ρ fun p => pps p σ ρ hρ
  have hfix := pmaj.fixed pmaj.syntactic.left σ ρ hρ
  rw [rawInterpret_ind_typed _ hi hB] at hfix
  have hd := telescope_of_structural_fixed (hi.code.map ((Tm E ℓ).map σ.op))
    ((IndCode.rel_map _ _).trans (hi.code_rel.trans hrel)) (hg.pullback σ)
    types (hρ.eval pmaj.left.ideal) hfix
  have htypes : types c = T := Subtype.val_injective hT.symm
  have hnames : indNames (hg.pullback σ) = Fin.append
      (fun f => (Tm E ℓ).map σ.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.syntactic.left)))
      hs.no_recursive.elim := by
    funext i
    rw [← map_indNames hg σ (hg.pullback σ) i]
    cases i using Fin.addCases with
    | left f =>
      change Fin (ι.ctors s c).nfields at f
      simpa [indNames, IndTyping.code, Fin.append_left] using congrArg ((Tm E ℓ).map σ.op)
        ((Tm.projOfCode_eq_proj hg w f).trans
          (Tm.proj_label hs hB ls ps hi.param pmaj.syntactic.left f))
    | right f => exact hs.no_recursive.elim f
  have hargs : (fun i => projIdeal (hi.code.ctorHead c) i (hρ.eval pmaj.left.ideal)) =
      Fin.append (fun f => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ f) (hρ.eval pmaj.left.ideal))
        hs.no_recursive.elim := by
    funext i
    cases i using Fin.addCases with
    | left f =>
      exact (Fin.append_left
        (fun f => projIdeal (CtorHead.mk η s c) (Fin.castAdd _ f) (hρ.eval pmaj.left.ideal))
        hs.no_recursive.elim f).symm
    | right f => exact hs.no_recursive.elim f
  rw [htypes, hnames, hargs] at hd
  have hdrop {k : Nat} (names : Fin k → Tm_ Γ₂) (args : Fin k → Domain Γ₂) :
      ∀ (ns : Fin (ι.ctors s c).nrecFields → Tm_ Γ₂)
        (xs : Fin (ι.ctors s c).nrecFields → Domain Γ₂),
        ((piLimit E ℓ).telescope T (Fin.append names ns) (Fin.append args xs)).1 =
          Fin.append args xs → ((piLimit E ℓ).telescope T names args).1 = args := by
    rw [Fin.eq_zero_of_isEmpty hs.no_recursive]
    intro ns xs heq
    simpa using heq
  exact hdrop _ _ _ _ hd

end Metalean.CoherentShape
