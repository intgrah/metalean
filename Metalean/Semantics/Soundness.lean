/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Judgment
public import Metalean.Semantics.Soundness.Rules.Core
public import Metalean.Semantics.Soundness.Rules.Constant
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Rules.Quotient
public import Metalean.Semantics.Soundness.Structure.Eta
import Metalean.Typing.Env
import Metalean.Typing.InstLevel
import Metalean.Typing.Map
import Metalean.Typing.Substitution
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Soundness.Recursor.Iota
import Mathlib.CategoryTheory.Whiskering

@[expose] public section

namespace Metalean

open CategoryTheory CoherentShape CodeAssignment Presheaf

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {ℓ n : Nat} {Δ : Ctx ζ₂ ℓ 0 n}

theorem EnvWF.rawSound (hE : EnvWF E₂) (pre : E₁.as ⟶ E₂.as) :
    RawSound E₂ ℓ pre := by
  induction hk : ζ₁.length using Nat.strong_induction_on generalizing ζ₁ with
  | _ k ih =>
  have hlookup {ι : IndSig} (η : Head ζ₁ (.inductive ι)) :=
    (Env.lookup _ ≫ Functor.whiskerLeft Env.forget (Entry.blockNatTrans _)).naturality_apply pre η
  dsimp at hlookup
  have hctors {ι : IndSig} (η : Head ζ₁ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
      (E₂.get (η.map pre.sigs)).block.ctors s c = ((E₁.get η).block.ctors s c).map pre.sigs := by
    rw [hlookup η]
    rfl
  have hblock {ι : IndSig} (η : Head ζ₁ (.inductive ι)) :
      ∃ (ζ₃ : Sigs) (E₃ : Env ζ₃) (incl : E₃.as ⟶ E₂.as) (I : Inductive ζ₃ ι),
        RawSound E₂ ℓ incl ∧ InductiveWF E₃ I ∧ (E₂.get (η.map pre.sigs)).block = I.map incl.sigs :=
    have ⟨_, _, incl, I, hlen, hI, hb⟩ := (hE.comap pre).block_spec pre η
    ⟨_, _, incl ≫ pre, I, ih _ (hlen.trans_eq hk) _ rfl, hI, hb⟩
  have hdef {m : Nat} (η : Head ζ₁ (.const .def m)) (ls : Fin m → Level ℓ) :
      RawJudgment (CtxCat.nil E₂ ℓ) ((E₂.get (η.map pre.sigs)).defValue.instL ls)
        ((E₂.get (η.map pre.sigs)).defValue.instL ls)
        ((E₂.get (η.map pre.sigs)).constType.instL ls) := by
    have ⟨_, _, incl, _, _, hlen, he, hη⟩ := (hE.comap pre).def_spec pre η
    have p := ih _ (hlen.trans_eq hk) (incl ≫ pre) rfl (he.instLevel ls) .nil .nil
    simp only [Expr.map_instL] at p
    rw [hη]
    exact p
  intro n Δ e₁ e₂ t d hΔ hR
  induction d with
  | var =>
    rw [← Ctx.get_map]
    exact RawJudgment.var hR _
  | symm _ ih₁ => exact (ih₁ hΔ hR).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hΔ hR).trans (ih₂ hΔ hR)
  | sortDF => exact RawJudgment.sort _ _
  | @constDF _ _ kind _ η ls _ _ ihtype =>
    have pT := ihtype hΔ hR
    simp only [Expr.map_wkClosed, Expr.map_instL,
      ← dsimp% (Entry.constTypeNatTrans _ _).naturality_apply,
      ← dsimp% (Env.lookup _).naturality_apply pre] at pT ⊢
    cases kind with
    | «def» => exact (RawJudgment.delta _ (hdef η ls) pT).leftRefl
    | «axiom» => exact RawJudgment.const_bot _ (fun _ => rawInterpret_const_axiom _ _ _) pT
    | «opaque» => exact RawJudgment.const_bot _ (fun _ => rawInterpret_const_opaque _ _ _) pT
  | @indDF _ _ ι η s ls ps₁ ps₂ is₁ is₂ _ _ ihps ihis =>
    have ⟨_, _, _, _, hsound, hI, hb⟩ := hblock η
    have pps := fun p => ihps p hΔ hR
    have pis := fun i => ihis i hΔ hR
    simp only [Inductive.paramType_map, Inductive.indexType_map, ← hlookup η] at pps pis
    rw [show (E₁.get η).block.level = (E₂.get (η.map pre.sigs)).block.level by
      simp [hlookup η, Inductive.map]]
    exact RawJudgment.indDF (hE.entryWF _).block
      (fun c => hsound.ctorTypeFnProperties _ hI hb s c _) pps pis
  | @ctorDF _ _ ι η s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂ fieldLevels recFieldLevels
      _ _ _ hfieldTypes hrecFieldTypes _ ihps ihfields ihrecFields _ _ ihtype =>
    have ⟨_, _, _, _, hsound, hI, hb⟩ := hblock η
    have pps := fun p => ihps p hΔ hR
    have pf := fun f =>
      show RawJudgment ⟨_, hΔ⟩ _ _
          ((((E₁.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f).map pre.sigs) from
        ihfields f hΔ hR
    have pr := fun f =>
      show RawJudgment ⟨_, hΔ⟩ _ _
          ((((E₁.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f).map pre.sigs) from
        ihrecFields f hΔ hR
    have hft := fun f => (hfieldTypes f).map pre
    have hrft := fun f => (hrecFieldTypes f).map pre
    have pT := ihtype hΔ hR
    simp only [Expr.map, Inductive.paramType_map, Ctor.ordinaryFieldExpr_map,
      Ctor.recursiveFieldExpr_map, Ctor.targetIndex_map, ← hctors, ← hlookup η]
      at pps pf pr hft hrft pT ⊢
    rw [show (E₁.get η).block.level = (E₂.get (η.map pre.sigs)).block.level by
      simp [hlookup η, Inductive.map]] at pT
    exact RawJudgment.ctorDF hsound hI hb (hE.entryWF _).block pps pf pr hft hrft pT
  | @recrDF _ _ ι η s ls l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂ hallowed hps hms hmins
      his hmaj hresult ihps ihms ihmins ihis ihmaj ihresult =>
    have ptype := ihresult hΔ hR
    have hrec := (Defeq.recrDF hallowed hps hms hmins his hmaj hresult).map pre
    simp only [Inductive.motiveResult_map] at ptype hrec ⊢
    have ⟨_, _, _, _, hsound, hI, hb⟩ := hblock η
    have pps := fun p => ihps p hΔ hR
    have pms := fun s => ihms s hΔ hR
    have pmins := fun s c => ihmins s c hΔ hR
    have pis := fun i => ihis i hΔ hR
    have pmaj := ihmaj hΔ hR
    simp only [Inductive.paramType_map, Inductive.indexType_map, Inductive.motiveType_map,
      Inductive.caseFnType_map, ← hlookup η] at pps pms pmins pis pmaj
    have hB := (hE.entryWF (η.map pre.sigs)).block
    have ha : (E₂.get (η.map pre.sigs)).block.RecAllowed l := by simpa [hlookup η] using hallowed
    exact RawJudgment.recrDF hsound hI hb
      (RecTyping.left hB ha (fun p => (pps p).syntactic) (fun s => (pms s).syntactic)
        (fun s c => (pmins s c).syntactic) (fun i => (pis i).syntactic) pmaj.syntactic)
      (RecTyping.right hB ha hΔ (fun p => (pps p).syntactic) (fun s => (pms s).syntactic)
        (fun s c => (pmins s c).syntactic) (fun i => (pis i).syntactic) pmaj.syntactic)
      hrec (Inductive.forall_recrSubst (motive := fun _ e₁ e₂ t => RawJudgment _ e₁ e₂ t) pps pms pmins pis pmaj) ptype
  | appDF _ _ _ _ _ iht iht' ihf ihe ihres =>
    have pt := iht hΔ hR
    have pRes := ihres hΔ hR
    simp only [Expr.map_inst] at pRes ⊢
    exact RawJudgment.appDF pt (iht' _ (hR.extension hΔ pt.left)) (ihf hΔ hR)
      (ihe hΔ hR) pRes
  | lamDF _ _ _ _ _ iht iht' _ ihe ihe' =>
    have pt := iht hΔ hR
    exact RawJudgment.lamDF pt (iht' _ (hR.extension hΔ pt.left))
      (ihe _ (hR.extension hΔ pt.left)) (ihe' _ (hR.extension hΔ pt.right))
  | forallEDF _ _ _ iht iht' iht'' =>
    have pt := iht hΔ hR
    exact RawJudgment.forallEDF pt (iht' _ (hR.extension hΔ pt.left))
      (iht'' _ (hR.extension hΔ pt.right))
  | defeqDF _ _ ihtt₁ ihe => exact RawJudgment.convert (ihtt₁ hΔ hR) (ihe hΔ hR)
  | beta _ _ _ _ _ _ iht iht' ihe' ihe ihte ihee =>
    have pt := iht hΔ hR
    have pTE := ihte hΔ hR
    have pEE := ihee hΔ hR
    simp only [Expr.map_inst] at pTE pEE ⊢
    exact RawJudgment.beta pt (iht' _ (hR.extension hΔ pt.left))
      (ihe' _ (hR.extension hΔ pt.left)) (ihe hΔ hR) pTE pEE
  | zeta _ _ _ _ iht ihv _ ihbody =>
    have pb := ihbody hΔ hR
    simp only [Expr.map_inst] at pb ⊢
    exact RawJudgment.zeta (iht hΔ hR) (ihv hΔ hR) pb
  | eta _ _ _ _ _ iht iht' ihtw ihew ihe =>
    have pt := iht hΔ hR
    have hR' := hR.extension hΔ pt.left
    have pTW := ihtw (hΔ.snoc ⟨_, pt.syntactic⟩) hR'
    have pEW := ihew (hΔ.snoc ⟨_, pt.syntactic⟩) hR'
    simp only [Expr.map, Expr.map_wk, Expr.map_wkFrom] at pTW pEW ⊢
    exact RawJudgment.eta pt (iht' _ hR') pTW pEW (ihe hΔ hR)
  | @etaStruct _ _ ι η s c ls ps is maj h _ _ _ ihps ihmaj ihrebuild =>
    have ⟨_, _, _, _, hsound, hI, hb⟩ := hblock η
    have pmaj := ihmaj hΔ hR
    have prebuild := ihrebuild hΔ hR
    have pps := fun p => ihps p hΔ hR
    have hs : (E₂.get (η.map pre.sigs)).block.IsStructure s c := hlookup η ▸ h.map pre.sigs
    have hidx : (fun i => (is i).map pre.sigs) = (hs.indices : Fin (ι.nindices s) → Expr ζ₂ ℓ _) :=
      funext h.no_indices.elim
    simp only [Expr.map] at pmaj prebuild ⊢
    rw [hidx] at pmaj prebuild ⊢
    simp only [Inductive.paramType_map, ← hlookup η] at pps
    have he := RawJudgment.etaStruct hsound hI hb hs (hE.entryWF _).block hR
      (fun p => (pps p).toRawTyped) pmaj.toRawTyped
    simpa [← hlookup η] using he (by simpa [← hlookup η] using prebuild.toRawTyped)
  | proofIrrel _ _ _ ihp ih₁ ih₂ =>
    have pP := ihp hΔ hR
    exact RawJudgment.proofIrrel pP (ih₁ hΔ hR) (ih₂ hΔ hR)
  | @iota _ _ ι η s c ls u ps ms mins fds recFds hallowed hps hms hmins hfields hrecFields
      htype hlhs hrhs ihps ihms ihmins ihfields ihrecFields ihtype ihlhs ihrhs =>
    have ptype := ihtype hΔ hR
    have plhs := ihlhs hΔ hR
    have prhs := ihrhs hΔ hR
    have hIota :=
      (Defeq.iota hallowed hps hms hmins hfields hrecFields htype hlhs hrhs).map pre
    by_cases hu : u = .zero
    · subst hu
      exact RawJudgment.of_typings hIota plhs prhs
        (HasEquality.proofIrrel ptype.syntactic.left plhs.syntactic.left prhs.syntactic.left
          ptype.fixed plhs.fixed prhs.fixed)
    have ⟨_, _, _, _, hsound, hI, hb⟩ := hblock η
    have pps := fun p => ihps p hΔ hR
    have pms := fun s => ihms s hΔ hR
    have pmins := fun s c => ihmins s c hΔ hR
    have pf := fun f =>
      show RawJudgment ⟨_, hΔ⟩ _ _
        ((((E₁.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f).map pre.sigs) from
        ihfields f hΔ hR
    have prf := fun f =>
      show RawJudgment ⟨_, hΔ⟩ _ _
        ((((E₁.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f).map pre.sigs) from
        ihrecFields f hΔ hR
    simp only [Inductive.paramType_map, Ctor.ordinaryFieldExpr_map, Ctor.recursiveFieldExpr_map,
      Inductive.motiveType_map, Inductive.caseFnType_map, ← hctors, ← hlookup η]
      at pps pf prf pms pmins
    have h : RecData (⟨_, hΔ⟩ : CtxCat E₂ ℓ) (η.map pre.sigs) ls u
        (fun p => (ps p).map pre.sigs) (fun s => (ms s).map pre.sigs)
        (fun s c => (mins s c).map pre.sigs) :=
      { block := (hE.entryWF _).block, allowed := by simpa [hlookup η] using hallowed,
        param := fun p => (pps p).syntactic, motive := fun s => (pms s).syntactic,
        case := fun s c => (pmins s c).syntactic }
    simp only [Inductive.iotaLhs_map, Inductive.iotaRhs_map, Inductive.iotaType_map,
      ← hlookup η] at hIota plhs prhs ⊢
    exact RawJudgment.of_typings hIota plhs prhs (RawSound.iota hsound hI hb h (by simp [hu]) hR
      ⟨fun f => (fds f).map pre.sigs, fun f => (recFds f).map pre.sigs,
        fun f => (pf f).syntactic, fun f => (prf f).syntactic⟩
      (fun p => (pps p).toRawTyped) (fun t => (pms t).toRawTyped) (fun t c => (pmins t c).toRawTyped)
      (fun f => (pf f).toRawTyped) (fun f => (prf f).toRawTyped) hIota prhs.toRawTyped)
  | quotDF _ _ ihα ihr =>
    have pr := ihr hΔ hR
    simp only [Quot.relType_map] at pr
    exact RawJudgment.quotDF (ihα hΔ hR) pr
  | quotMkDF _ _ _ ihα ihr iha =>
    have pr := ihr hΔ hR
    simp only [Quot.relType_map] at pr
    exact RawJudgment.quotMkDF (ihα hΔ hR) pr (iha hΔ hR)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    have pr := ihr hΔ hR
    have pf := ihf hΔ hR
    have ph := ihh hΔ hR
    simp only [Expr.map, Expr.map_wk, Quot.relType_map, Quot.compatType_map,
      ← dsimp% Entry.eqHeadNatTrans.naturality_apply,
      ← dsimp% (Env.lookup _).naturality_apply pre] at pr pf ph
    exact RawJudgment.quotLiftDF (ihα hΔ hR) pr (ihβ hΔ hR) pf ph (iha hΔ hR)
  | quotIndDF _ _ _ _ _ _ ihα ihr ihβ ihf iha ihresult =>
    have pr := ihr hΔ hR
    have pβ := ihβ hΔ hR
    have pf := ihf hΔ hR
    simp only [Quot.relType_map, Quot.minorType_map] at pr pβ pf
    exact RawJudgment.quotIndDF (ihα hΔ hR) pr pβ pf (iha hΔ hR) (ihresult hΔ hR)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha _ ihrhs =>
    have pr := ihr hΔ hR
    have pf := ihf hΔ hR
    have ph := ihh hΔ hR
    simp only [Expr.map, Expr.map_wk, Quot.relType_map, Quot.compatType_map,
      ← dsimp% Entry.eqHeadNatTrans.naturality_apply,
      ← dsimp% (Env.lookup _).naturality_apply pre] at pr pf ph
    exact RawJudgment.quotIota (ihα hΔ hR) pr (ihβ hΔ hR) pf ph (iha hΔ hR)
      (ihrhs hΔ hR)
  | @delta _ _ _ η ls _ _ _ ihtype _ =>
    have pT := ihtype hΔ hR
    simp only [Expr.map_wkClosed, Expr.map_instL,
      ← dsimp% (Entry.constTypeNatTrans _ _).naturality_apply,
      ← dsimp% (Entry.defValueNatTrans _).naturality_apply,
      ← dsimp% (Env.lookup _).naturality_apply pre] at pT ⊢
    exact RawJudgment.delta _ (hdef η ls) pT

theorem Defeq.rawSoundness (hE : EnvWF E₂) {e₁ e₂ t : Expr ζ₂ ℓ n}
    (hΔ : E₂[Δ] ⊢ ok) (d : E₂[Δ] ⊢ e₁ ≡ e₂ : t) :
    RawJudgment ⟨Δ, hΔ⟩ e₁ e₂ t := by
  convert RawSound.properties (hE.rawSound .refl) hΔ d using 1 <;>
    simp! [dsimp% [CategoryStruct.id] (Expr.functor ℓ n).map_id_apply ζ₂,
      dsimp% [CategoryStruct.id] (Ctx.functor ℓ 0 n).map_id_apply ζ₂]

theorem CtxWF.bottom_admissible (hE : EnvWF E₂) (hΔ : E₂[Δ] ⊢ ok) {Γ : CtxCat E₂ ℓ}
    (σ : Γ ⟶ (⟨Δ, hΔ⟩ : CtxCat E₂ ℓ)) : SourceAdmissible σ fun _ ↦ ⊥ := by
  induction hΔ with
  | nil => exact .nil σ _
  | @snoc _ Δ t hΔ ht ih =>
    have ⟨u, ht⟩ := ht
    have htail := ih (σ ≫ CtxCat.rawProjection ⟨Δ, hΔ⟩ ht)
    exact SourceAdmissible.cons ht σ (fun _ ↦ ⊥) htail ((ht.rawSoundness hE hΔ).left.ideal _ _ htail)
      ΩLower.isDirected_bot (rawExtend_bottom_payload piLimit_isPayloadStrict _ _)

end Metalean
