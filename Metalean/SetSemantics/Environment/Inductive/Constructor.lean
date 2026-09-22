/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Interpretation
import Metalean.Typing.Inductive
import Metalean.Typing.InstLevel
import Metalean.Syntax.Substitution

/-! # Semantic models for constructors -/

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {nfields arity bound bound₁ level : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  {s s₁ : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ₁ ι s csig}
  {recFd : RecField ζ₁ ι nfields arity s₁}
  {Γ : Ctx ζ₁ 0 0 (ι.nparams + nfields)} {base : StrongTeleModel E₁ ε₁ zeroNs Γ}
  {params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params)}

structure BlockTeleModels (E : Env ζ₁) (ls : Fin ι.nlevels → Level 0)
    (ε : Atom ζ₁ 0 → ZFSet.{u}) (I : Inductive ζ₁ ι) : Type (u + 1) where
  params : StrongTeleModel E ε zeroNs (Ctx.instL ls I.params)
  indicesBound (s : Fin ι.nsorts) : Nat
  indices (s : Fin ι.nsorts) :
    StrongTeleExtension E ε zeroNs params (Ctx.instL ls (I.indices s)) (indicesBound s)

theorem InductiveWF.teleModels (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁) (hB : InductiveWF E₁ I) :
    Nonempty (BlockTeleModels E₁ ls ε₁ I) := by
  have ⟨paramsModel⟩ :=
    (hB.params.instLevel ls fun _ => trivial).model hdecl hrule hE
  have his (s) := Classical.choice
    ((hB.indices s).instLevel ls (fun _ => trivial)
      |>.modelExtension hdecl hrule hE paramsModel)
  exact ⟨paramsModel, fun s => (his s).fst, fun s => (his s).snd⟩

structure StrongRecursiveFieldSource (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0)
    (base : StrongTeleModel E ε zeroNs Γ)
    (bound : Nat) (recFd : RecField ζ₁ ι nfields arity s₁) : Type (u + 1) where
  extension : StrongTeleExtension E ε zeroNs base (recFd.tele.instL ls) bound
  mem (γ : Slots (ι.nparams + nfields + arity))
    (hγ : γ ∈ Reachable (Reachable Set.univ base.sem) extension.sem)
    (index : Fin (ι.nindices s₁)) :
    ε[γ]⟦(recFd.indices index).instL ls⟧ ∈
      ε[γ]⟦I.indexType ls s₁ (fun param => .var ⟨param.val, by omega⟩)
        (fun i => (recFd.indices i).instL ls) index⟧

namespace StrongRecursiveFieldSource

noncomputable def code (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd) :
    CtorRecCode (ι.nparams + nfields) arity where
  tele := source.extension.sem
  index γ := sortKey s₁.val (encode (ε₁[γ]⟦recFd.indices · |>.instL ls⟧))

@[simp] theorem code_index (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (γ : Slots (ι.nparams + nfields + arity)) :
    (code recFd source).index γ =
      sortKey s₁.val (encode (ε₁[γ]⟦recFd.indices · |>.instL ls⟧)) :=
  rfl

theorem denotesDepMapEnv
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    {block : Dom (ι.nparams + nfields)}
    {sortValue : Slots ι.nparams → Slots (ι.nindices s₁) → ZFSet}
    {reach : Set (Slots (ι.nparams + nfields))}
    (hreaches : reach ⊆ Reachable Set.univ base.sem)
    (hF : ∀ vps vis, ε₂ (.ind η s₁ ls vps vis) = sortValue vps vis)
    (happly : ∀ γ ∈ Reachable reach (code recFd source).tele,
      sortValue (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
        (ε₁[γ]⟦recFd.indices · |>.instL ls⟧) =
        propSet level (fibreOp
          (block fun current : Fin (ι.nparams + nfields) =>
            γ (current.castLE (code recFd source).tele.le))
          ((code recFd source).index γ)))
    (γ : Slots (ι.nparams + nfields)) (hγ : γ ∈ reach) :
    ε₂[γ]⟦(recFd.map pre.sigs).instantiatedType η ls
        (fun param => .var (param.castLE (Nat.le_add_right _ _))) Subst.id⟧ =
      typedRecFieldSetDep (code recFd source).tele (code recFd source).index block level γ := by
  simp only [RecField.map, RecField.instantiatedType, RecField.instantiatedTelescope_id]
  apply Realizes.denotes_pi hγ
  · intro final hfinal
    have his (index : Fin (ι.nindices s₁)) :=
      Expr.denote_map (ν := zeroNs) pre.sigs hatoms final ((recFd.indices index).instL ls)
    simp only [Expr.map_instL] at his
    simp! only [RecField.instantiatedIndices_id, Expr.denote_wkN]
    rw [funext his, hF]
    exact happly final hfinal
  · exact Realizes.mapInst (source.extension.realizes.monoReach hreaches) pre hatoms

theorem ihType_denotes
    (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    {n : Nat} {σ : Subst ζ₂ 0 (ι.nparams + nfields) n}
    {ms : Fin ι.nsorts → Expr ζ₂ 0 n}
    {motive : ZFSet} {e : Expr ζ₂ 0 n}
    {domain : Dom (ι.nparams + nfields + arity)}
    (γ : Slots n) (δ : Slots (ι.nparams + nfields))
    (hδ : δ ∈ Reachable Set.univ base.sem)
    (hσ : (ε₂[γ]⟦σ ·⟧) = δ)
    (hvalue : ε₂[γ]⟦e⟧ ∈ (code recFd source).tele.pi domain δ)
    (hleaf : ∀ final,
      (∀ v : Fin (ι.nparams + nfields), final (v.castAdd arity) = δ v) →
      ∀ value, value ∈ domain final →
      [zf|$(ε₂[γ]⟦ms s₁⟧) $((ε₁[final]⟦recFd.indices · |>.instL ls⟧))... value] =
        fibreOp motive (pair (code recFd source |>.index final) value)) :
    ε₂[γ]⟦(recFd.map pre.sigs).ihType ls ms σ e⟧ =
      ihType (code recFd source).tele (code recFd source).index motive δ ε₂[γ]⟦e⟧ := by
  let project : Slots n → Slots (ι.nparams + nfields) := fun _ => δ
  have hden := (Realizes.mapInst source.extension.realizes pre hatoms).pull σ project
    (reach₁ := {γ}) (fun _ _ => hδ)
    (fun current hcurrent v => by subst current; exact congrFun hσ v)
    |>.denotes_motivePiAt
    (vis := fun final => (ε₁[Slots.pull project final]⟦recFd.indices · |>.instL ls⟧))
    (Set.mem_singleton γ) (by rwa [SemTele.pi_pull])
    (fun _ hfinal v => congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal)) v)
    (fun final hfinal index => by
      have hsource := Expr.denote_map (ν := zeroNs) pre.sigs hatoms (Slots.pull project final)
        ((recFd.indices index).instL ls)
      rw [Expr.map_instL] at hsource
      rwa [Expr.denote_subst, Expr.denote_substLiftN,
        show (fun v => final (v.castAdd arity)) = γ from
          Set.eq_of_mem_singleton (Reachable.base hfinal), hσ])
    fun final hfinal value hvalue =>
      hleaf (Slots.pull project final) (fun v => by simp [project]) value hvalue
  rwa [SemTele.piAt_pull (leaf := fun final value =>
    fibreOp motive (pair ((code recFd source).index final) value))] at hden

end StrongRecursiveFieldSource

theorem RecFieldWF.recursiveSourceOf
    (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁)
    {Δ : Ctx ζ₁ ι.nlevels ι.nparams (ι.nparams + nfields)}
    (hfield : RecFieldWF E₁ I (I.params ++ Δ) recFd)
    (params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params))
    (extension : StrongTeleExtension E₁ ε₁ zeroNs params (Ctx.instL ls Δ) bound₁)
    (fieldExtension : StrongTeleExtension E₁ ε₁ zeroNs (params.append extension)
      (recFd.tele.instL ls) bound) :
    Nonempty (StrongRecursiveFieldSource E₁ ε₁ I ls (params.append extension) bound recFd) := by
  have his (index : Fin (ι.nindices s₁)) := hfield.recursiveIndex (ls := ls) index
  rw [Ctx.instL_append] at his
  exact ⟨fieldExtension, fun γ hγ index =>
    (soundness hdecl hrule hE (his index) γ (fieldExtension.semCtx γ hγ)).mem⟩

structure StrongCtorSource (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0) (ctor : Ctor ζ₁ ι s csig)
    (params : StrongTeleModel E ε zeroNs (Ctx.instL ls I.params))
    (bound : Nat) : Type (u + 1) where
  ordinary : StrongTeleExtension E ε zeroNs params (Ctx.instL ls ctor.ordinaryTele) bound
  recursive (f : Fin csig.nrecFields) :
    StrongRecursiveFieldSource E ε I ls (params.append ordinary) bound (ctor.recursive f)

theorem CtorWF.sourceAt (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params))
    (hblock : (I.level.inst ls).eval zeroNs = bound + 1) :
    Nonempty (StrongCtorSource E₁ ε₁ I ls ctor params bound) := by
  have hnz : I.level.eval (Level.eval zeroNs ∘ ls) ≠ 0 := by
    rw [← Level.eval_inst]
    omega
  have ⟨fields⟩ := ((hctor.ordinaryTeleAux _ le_rfl).instLevel
    (Q := fun l => l.eval zeroNs ≤ bound + 1) ls fun hl => by
      rw [Level.eval_inst, ← hblock, Level.eval_inst]
      exact Level.eval_le_of_imax_le hl hnz).modelExtensionAt hdecl hrule hE (fun hl => hl) params
  refine ⟨⟨fields, fun f => Classical.choice ?_⟩⟩
  have htele := (hctor.recursive f).teleAt (ls := ls) hblock
  rw [Ctx.instL_append] at htele
  have ⟨fieldExtension⟩ :=
    htele.modelExtensionAt hdecl hrule hE (fun hl => hl) (params.append fields)
  exact (hctor.recursive f).recursiveSourceOf hdecl hrule hE params fields fieldExtension

theorem CtorWF.source (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params)) :
    Nonempty (Σ bound, StrongCtorSource E₁ ε₁ I ls ctor params bound) := by
  have ⟨fieldBound, fields⟩ := ((hctor.ordinaryTeleAux _ le_rfl).instLevel
    (Q := fun _ => True) ls fun _ => trivial).modelExtension hdecl hrule hE params
  have hsources (f : Fin csig.nrecFields) :
      Nonempty (Σ bound₂, StrongTeleExtension E₁ ε₁ zeroNs (params.append fields)
        (Ctx.instL ls ((ctor.recursive f).tele)) bound₂) := by
    have htele := (hctor.recursive f).tele.instLevel (Q := fun _ => True) ls fun _ => trivial
    rw [Ctx.instL_append] at htele
    exact htele.modelExtension hdecl hrule hE (params.append fields)
  let recFieldBound (f : Fin csig.nrecFields) : Nat := (Classical.choice (hsources f)).1
  let bound := max fieldBound (Finset.univ.sup recFieldBound)
  have hrecField (f : Fin csig.nrecFields) : recFieldBound f ≤ bound :=
    (Finset.le_sup (f := recFieldBound) (Finset.mem_univ f)).trans (Nat.le_max_right _ _)
  exact ⟨bound, fields.mono (Nat.le_max_left _ _), fun f => Classical.choice <|
    (hctor.recursive f).recursiveSourceOf hdecl hrule hE params _
      ((Classical.choice (hsources f)).2.mono (hrecField f))⟩

private theorem indexValuesReachable {m : Nat} (hm : ι.nparams ≤ m)
    {paramsSem : SemTele 0 ι.nparams}
    {indicesSem : SemTele ι.nparams (ι.nparams + ι.nindices s)}
    (his : Realizes ε₁ zeroNs
      (Reachable Set.univ paramsSem)
      (Ctx.instL ls (I.indices s)) indicesSem)
    (is : Fin (ι.nindices s) → Expr ζ₁ 0 m) (γ : Slots m)
    (hps : (fun param => γ (param.castLE hm)) ∈ Reachable Set.univ paramsSem)
    (interp : ∀ index, ε₁[γ] ⊨ is index ≡ is index :
      I.indexType ls s (fun param => .var (param.castLE hm)) is index) :
    Fin.append (fun param : Fin ι.nparams => γ (param.castLE hm)) (ε₁[γ]⟦is ·⟧) ∈
      Reachable (Reachable Set.univ paramsSem) indicesSem := by
  let := Subst.category ζ₁ 0
  let vps : Slots ι.nparams := fun param => γ (param.castLE hm)
  let σ : Subst ζ₁ 0 (ι.nparams + ι.nindices s) m :=
    Fin.append (fun param => .var (param.castLE hm)) is
  let γ₁ : Slots (ι.nparams + ι.nindices s) := Fin.append vps (ε₁[γ]⟦is ·⟧)
  apply his.reachable_subst (Γ := I.params.instL ls) (γ := γ) σ γ₁
  · simpa [γ₁] using hps
  · intro v
    cases v using Fin.addCases with
    | left param => simp [σ, γ₁, vps, Expr.denote]
    | right index => simp [σ, γ₁]
  · intro v hv
    cases v using Fin.addCases with
    | left param =>
      exact ((Nat.not_le_of_gt param.isLt) (by simpa using hv)).elim
    | right index =>
      simp only [γ₁, Fin.append_right]
      rw [show Ctx.instL ls (I.indices s) = I.indexTele ls s fun param => .var param from
        ((Ctx.substFunctor _).map_id_apply _ _).symm,
        I.indexTele_get, Inductive.indexType_subst,
        show (fun param : Fin ι.nparams => Expr.subst σ ((Expr.var param).wkN (ι.nindices s))) =
          fun param => (Expr.var (param.castLE hm) : Expr ζ₁ 0 m) from
            funext fun param => by simp [σ, Expr.subst],
        show (fun i : Fin (ι.nindices s) =>
            Expr.subst σ (.var (Fin.natAdd ι.nparams i))) = is from
          funext fun i => by simp [Expr.subst, σ]]
      exact (interp index).mem

theorem StrongRecursiveFieldSource.valuesReachable (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (paramsSem : SemTele 0 ι.nparams)
    (indicesSem : SemTele ι.nparams (ι.nparams + ι.nindices s₁))
    (his : Realizes ε₁ zeroNs (Reachable Set.univ paramsSem)
      ((I.indices s₁).instL ls) indicesSem)
    {reach : Set (Slots (ι.nparams + nfields))}
    (hreaches : reach ⊆ Reachable Set.univ base.sem)
    (hps : Set.MapsTo (fun γ param => γ (param.castLE (Nat.le_add_right _ _)))
      reach (Reachable Set.univ paramsSem))
    (γ : Slots (ι.nparams + nfields + arity))
    (hγ : γ ∈ Reachable reach (StrongRecursiveFieldSource.code recFd source).tele) :
    Fin.append (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
        (ε₁[γ]⟦recFd.indices · |>.instL ls⟧) ∈
      Reachable (Reachable Set.univ paramsSem) indicesSem :=
  indexValuesReachable (by omega) his (fun index => Expr.instL ls (recFd.indices index)) γ
    (hps (Reachable.base hγ))
    fun index => ⟨rfl, source.mem γ (Reachable.mono hγ hreaches) index⟩

namespace StrongCtorSource

noncomputable def recursiveCodes (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (f : Fin csig.nrecFields) : CtorRecCode.Packed (ι.nparams + csig.nfields) :=
  ⟨csig.recursiveArity f, StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)⟩

structure Target (source : StrongCtorSource E₁ ε₁ I ls ctor params bound) : Type (u + 1) where
  values (γ : Slots (ι.nparams + csig.nfields)) : Fin (ι.nindices s) → ZFSet
  interp : ∀ γ ∈ Reachable Set.univ (params.append source.ordinary).sem,
    (i : Fin (ι.nindices s)) →
    ε₁[γ] ⊨ Expr.instL ls (ctor.targetIndices i) ≡ Expr.instL ls (ctor.targetIndices i) :
      I.indexType ls s (fun param => .var ⟨param.val, by omega⟩)
        (fun i => (ctor.targetIndices i).instL ls) i
  denotes : ∀ γ ∈ Reachable Set.univ (params.append source.ordinary).sem,
    (i : Fin (ι.nindices s)) →
    ε₁[γ]⟦(ctor.targetIndices i).instL ls⟧ = values γ i
  bounded : ∃ level, ∀ γ index, values γ index ∈ U_ level

noncomputable def targetIndex {source : StrongCtorSource E₁ ε₁ I ls ctor params bound}
    (model : Target source) : Dom (ι.nparams + csig.nfields) :=
  fun γ => sortKey s.val (encode (model.values γ))

theorem Target.valuesReachable {source : StrongCtorSource E₁ ε₁ I ls ctor params bound}
    (model : Target source)
    (indicesSem : SemTele ι.nparams (ι.nparams + ι.nindices s))
    (his : Realizes ε₁ zeroNs (Reachable Set.univ params.sem)
      ((I.indices s).instL ls) indicesSem)
    (fieldSlots : Slots (ι.nparams + csig.nfields))
    (hfields : fieldSlots ∈ Reachable Set.univ (params.append source.ordinary).sem) :
    Fin.append (fun param : Fin ι.nparams => fieldSlots (param.castLE (Nat.le_add_right _ _)))
        (model.values fieldSlots) ∈
      Reachable (Reachable Set.univ params.sem) indicesSem :=
  (funext (model.denotes fieldSlots hfields)) ▸ indexValuesReachable (Nat.le_add_right _ _) his
    (fun index => Expr.instL ls (ctor.targetIndices index))
    fieldSlots (Reachable.base (Reachable.of_append hfields)) (model.interp fieldSlots hfields)

noncomputable def code (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (targetIndex : Dom (ι.nparams + csig.nfields)) : CtorCode ι.nparams :=
  CtorCode.prependOrdinary source.ordinary.sem
    (CtorCode.prependRecursive csig.nrecFields source.recursiveCodes (.target targetIndex))

theorem codeDomsIn (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (targetIndex : Dom (ι.nparams + csig.nfields)) :
    (source.code targetIndex).DomsIn bound :=
  CtorCode.DomsIn.prependOrdinary source.ordinary.bounded
    (CtorCode.DomsIn.prependRecursive
      (fun f => (source.recursive f).extension.bounded)
      (CtorCode.DomsIn.target))

theorem code_targetIndex_mem_type (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (model : Target source) (hlevel : Classical.choose model.bounded ≤ level)
    (γ : Slots ι.nparams) (vargs : ZFSet) :
    (source.code (targetIndex model)).targetIndex γ vargs ∈ U_ level := by
  rw [code, SemTele.targetIndex_prependOrdinary, CtorCode.targetIndex_prependRecursive]
  exact sortKey_mem_type (encode_fin_mem_type fun index =>
    type_mono hlevel (Classical.choose_spec model.bounded _ index))

theorem recursivePhaseAux
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    {block : Dom (ι.nparams + csig.nfields)}
    {reach : Set (Slots (ι.nparams + csig.nfields))}
    (hreaches : reach ⊆ Reachable Set.univ (params.append source.ordinary).sem)
    (sortValues : (s₁ : Fin ι.nsorts) → Slots ι.nparams → Slots (ι.nindices s₁) → ZFSet)
    (hsortValues : ∀ s₁ vps vis, ε₂ (.ind η s₁ ls vps vis) = sortValues s₁ vps vis)
    (happlyRecursive : ∀ f : Fin csig.nrecFields,
      ∀ γ ∈ Reachable reach
          (StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).tele,
      sortValues (csig.recursiveTarget f)
        (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
        (ε₁[γ]⟦(ctor.recursive f).indices · |>.instL ls⟧) =
        propSet level (fibreOp
          (block fun current : Fin (ι.nparams + csig.nfields) =>
            γ (current.castLE (StrongRecursiveFieldSource.code (ctor.recursive f)
              (source.recursive f)).tele.le))
          ((StrongRecursiveFieldSource.code (ctor.recursive f)
            (source.recursive f)).index γ)))
    (count : Nat) (hcount : count ≤ csig.nrecFields) :
    ∃ reachEnd : Set (Slots (ι.nparams + csig.nfields + count)),
      RecursivePhaseRealizes ε₂ zeroNs block level id reach
        (fun f => source.recursiveCodes (f.castLE hcount))
        (fun γ f => γ (f.castAdd count)) reachEnd
        ((ctor.map pre.sigs).recursiveFieldTeleAux η ls
          (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
            Expr ζ₂ 0 (ι.nparams + csig.nfields)))
          (Expr.boundVars ι.nparams csig.nfields 0) count hcount) ∧
      Set.MapsTo (fun γ f => γ (f.castAdd count)) reachEnd reach := by
  induction count with
  | zero =>
    refine ⟨reach, ?_, fun _ h => h⟩
    convert RecursivePhaseRealizes.nil using 1 <;> rfl
  | succ count ih =>
    have ⟨reachEnd, hphase, hreach⟩ := ih (by omega)
    let f : Fin csig.nrecFields := ⟨count, by omega⟩
    let code := StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)
    have hphase₁ := hphase.snoc ⟨csig.recursiveArity f, code⟩
      (t := (((ctor.map pre.sigs).recursive f).instantiatedType η ls
        (fun param => .var (param.castLE (Nat.le_add_right _ _))) Subst.id).wkN count)
      fun γ hγ => by
        have h := StrongRecursiveFieldSource.denotesDepMapEnv
          pre hatoms (ctor.recursive f) (source.recursive f) hreaches
          (hsortValues (csig.recursiveTarget f)) (happlyRecursive f)
          _ (hreach hγ)
        simpa [Ctor.map, -RecField.instantiatedType_wkN] using h
    refine ⟨{γ | Fin.init γ ∈ reachEnd ∧
        γ (Fin.last (ι.nparams + csig.nfields + count)) ∈
          typedRecFieldSetDep code.tele code.index block level
            fun f => Fin.init γ (f.castAdd count)},
      ?_, fun _ hγ => hreach hγ.1⟩
    convert hphase₁ using 1
    · exact (Fin.snoc_init_self
        fun f : Fin (count + 1) => source.recursiveCodes (f.castLE hcount)).symm
    · rfl
    · simp [Ctor.recursiveFieldTeleAux]
      rfl

theorem realizes
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (model : Target source)
    {block : ZFSet}
    (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ params.sem)
    (sortValues : (s₁ : Fin ι.nsorts) → Slots ι.nparams → Slots (ι.nindices s₁) → ZFSet)
    (hsortValues : ∀ s₁ vps vis, ε₂ (.ind η s₁ ls vps vis) = sortValues s₁ vps vis)
    (happlyTarget : ∀ γ ∈ Reachable {vps} source.ordinary.sem,
      sortValues s (fun param : Fin ι.nparams => γ (param.castLE (by omega))) (model.values γ) =
        propSet level (fibreOp block (targetIndex model γ)))
    (happlyRecursive : ∀ f : Fin csig.nrecFields,
      ∀ γ ∈ Reachable (Reachable {vps} source.ordinary.sem)
          (StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).tele,
      sortValues (csig.recursiveTarget f)
        (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
        (ε₁[γ]⟦(ctor.recursive f).indices · |>.instL ls⟧) =
        propSet level (fibreOp block
          ((StrongRecursiveFieldSource.code (ctor.recursive f)
            (source.recursive f)).index γ))) :
    CtorCode.Interprets ε₂ zeroNs block level (fun γ => γ) {vps}
      (let ps : Fin ι.nparams → Expr ζ₂ 0 ι.nparams := fun param => .var param
       Ctx.pi
         (.ind η s ls (csig.fieldParams ps)
           fun index => (ctor.map pre.sigs).targetIndex ls
             (csig.fieldParams ps) csig.fieldOrdinary index)
         ((ctor.map pre.sigs).fieldTele η ls ps))
      (source.code (targetIndex model)) := by
  let := Subst.category ζ₂ 0
  have hreaches : Reachable {vps} source.ordinary.sem ⊆
      Reachable Set.univ (params.append source.ordinary).sem := fun _ hγ =>
    Reachable.append (Reachable.mono hγ (Set.singleton_subset_iff.mpr hps))
  have htarget (γ : Slots (ι.nparams + csig.nfields))
      (hγ : γ ∈ Reachable {vps} source.ordinary.sem) :
      ε₂[γ]⟦.ind η s ls
          (fun param => .var
            (param.castLE (Nat.le_add_right _ _)))
          (fun index => Expr.instL ls
            ((ctor.map pre.sigs).targetIndices index))⟧ = propSet level (fibreOp block
          (targetIndex model γ)) := by
    simp only [Expr.denote]
    rw [funext fun index : Fin (ι.nindices s) => show
        ε₂[γ]⟦((ctor.map pre.sigs).targetIndices index).instL ls⟧ = model.values γ index by
      simpa [Ctor.map] using
        (Expr.denote_map pre.sigs hatoms γ _).trans (model.denotes γ (hreaches hγ) index),
      hsortValues]
    exact happlyTarget γ hγ
  have ⟨reachEnd, hphase, hreach⟩ :=
    recursivePhaseAux (block := fun _ => block) (level := level)
      pre hatoms source hreaches sortValues hsortValues
      (by simpa using happlyRecursive) csig.nrecFields le_rfl
  have hfields := CtorCode.Interprets.prependOrdinary (block := block) (level := level)
    (Δ := Ctx.instL ls (ctor.map pre.sigs).ordinaryTele)
    (congrArg (Ctx.instL ls) (Ctor.ordinaryTeleAux_map pre.sigs ctor _ _) ▸
      Realizes.mapInst (source.ordinary.realizes.monoReach
        (Set.singleton_subset_iff.mpr hps)) pre hatoms)
    (hphase.prepend (rest := .target (targetIndex model))
      (.target fun γ hγ => (Expr.denote_wkN γ _).trans (htarget _ (hreach hγ))))
  rw [(ctor.map pre.sigs).targetType_fields η ls] at hfields
  simpa [Fin.castAdd, Ctor.fieldTele, Ctx.pi, Tele.foldr_append, code,
    show Ctx.instL ls (ctor.map pre.sigs).ordinaryTele = (ctor.map pre.sigs).ordinaryFieldTele η ls fun param => .var param from ((Ctx.substFunctor _).map_id_apply _ _).symm] using hfields

end StrongCtorSource

open scoped Classical in
theorem CtorWF.targetModel (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (indices : StrongTeleExtension E₁ ε₁ zeroNs params (Ctx.instL ls (I.indices s)) bound₁)
    (source : StrongCtorSource E₁ ε₁ I ls ctor params bound) :
    Nonempty (StrongCtorSource.Target source) := by
  let sourceModel := params.append source.ordinary
  have htarget (index : Fin (ι.nindices s)) :=
    (hctor.targetIndices index).instLevel ls
  rw [Ctx.instL_append] at htarget
  have interp (γ : Slots (ι.nparams + csig.nfields))
      (hγ : γ ∈ Reachable Set.univ sourceModel.sem)
      (index : Fin (ι.nindices s)) :
      ε₁[γ] ⊨ Expr.instL ls (ctor.targetIndices index) ≡
        Expr.instL ls (ctor.targetIndices index) :
        I.indexType ls s
          (fun param => .var ⟨param.val, by omega⟩)
          (fun i => Expr.instL ls (ctor.targetIndices i)) index := by
    simpa! using
      soundness hdecl hrule hE (htarget index) γ (sourceModel.semCtx γ hγ)
  let vis (γ : Slots (ι.nparams + csig.nfields))
      (index : Fin (ι.nindices s)) : ZFSet :=
    if γ ∈ Reachable Set.univ sourceModel.sem then
      ε₁[γ]⟦(ctor.targetIndices index).instL ls⟧
    else ∅
  have hdenotes γ (hγ : γ ∈ Reachable Set.univ sourceModel.sem) index :
      ε₁[γ]⟦(ctor.targetIndices index).instL ls⟧ = vis γ index := by
    simp [vis, hγ]
  refine ⟨vis, interp, hdenotes, bound₁, fun γ index => ?_⟩
  by_cases hγ : γ ∈ Reachable Set.univ sourceModel.sem
  · have hreach := indexValuesReachable (Nat.le_add_right _ _) indices.realizes
      (fun index => Expr.instL ls (ctor.targetIndices index)) γ
      (Reachable.base (Reachable.of_append hγ)) (interp γ hγ)
    simp only [hdenotes γ hγ] at hreach
    simpa using Reachable.mem_type_of_domsIn hreach indices.bounded (Fin.natAdd ι.nparams index)
      (by simp)
  · simpa [vis, hγ] using empty_mem_type

structure StrongCtorModel (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0) (ctor : Ctor ζ₁ ι s csig)
    (params : StrongTeleModel E ε zeroNs (Ctx.instL ls I.params)) : Type (u + 1) where
  bound : Nat
  source : StrongCtorSource E ε I ls ctor params bound
  target : StrongCtorSource.Target source
  localDoms (level : Nat) :
    (I.level.inst ls).eval zeroNs = level + 1 →
    (source.code (StrongCtorSource.targetIndex target)).DomsIn level

theorem CtorWF.model (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params))
    (indices : StrongTeleExtension E₁ ε₁ zeroNs params (Ctx.instL ls (I.indices s)) bound₁) :
    Nonempty (StrongCtorModel E₁ ε₁ I ls ctor params) := by
  cases hlevel : (I.level.inst ls).eval zeroNs with
  | zero =>
    have ⟨bound, source⟩ := hctor.source hdecl hrule hE params
    have ⟨targetModel⟩ := hctor.targetModel hdecl hrule hE indices source
    exact ⟨_, source, targetModel, fun _ _ => by omega⟩
  | succ level =>
    have ⟨source⟩ : Nonempty (StrongCtorSource E₁ ε₁ I ls ctor params level) :=
      hctor.sourceAt hdecl hrule hE params (by simpa using hlevel)
    have ⟨targetModel⟩ := hctor.targetModel hdecl hrule hE indices source
    refine ⟨_, source, targetModel, fun level₁ hlevel₁ => ?_⟩
    obtain rfl : level₁ = level := by omega
    exact source.codeDomsIn _

end Metalean
