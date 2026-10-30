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
  {Γ : Ctx ζ₁ 0 0 (ι.nparams + nfields)} {base : StrongTeleModel E₁ ε₁ ![] Γ}
  {params : StrongTeleModel E₁ ε₁ ![] I.params{ls}}

structure BlockTeleModels (E : Env ζ₁) (ls : Fin ι.nlevels → Level 0)
    (ε : Atom ζ₁ 0 → ZFSet.{u}) (I : Inductive ζ₁ ι) : Type (u + 1) where
  params : StrongTeleModel E ε ![] I.params{ls}
  indicesBound (s : Fin ι.nsorts) : Nat
  indices (s : Fin ι.nsorts) :
    StrongTeleExtension E ε ![] params (I.indices s){ls} (indicesBound s)

theorem InductiveWF.teleModels (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hB : InductiveWF E₁ I) :
    Nonempty (BlockTeleModels E₁ ls ε₁ I) := by
  have ⟨paramsModel⟩ :=
    (hB.params.instLevel ls fun _ => trivial).model hdecl hrule hE
  have his (s) := Classical.choice
    ((hB.indices s).instLevel ls (fun _ => trivial)
      |>.modelExtension hdecl hrule hE paramsModel)
  exact ⟨paramsModel, fun s => (his s).fst, fun s => (his s).snd⟩

structure StrongRecursiveFieldSource (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0)
    (base : StrongTeleModel E ε ![] Γ)
    (bound : Nat) (recFd : RecField ζ₁ ι nfields arity s₁) : Type (u + 1) where
  extension : StrongTeleExtension E ε ![] base recFd.tele{ls} bound
  mem (γ : Slots (ι.nparams + nfields + arity))
    (hγ : γ ∈ Reachable (Reachable Set.univ base.sem) extension.sem)
    (index : Fin (ι.nindices s₁)) :
    ε[γ]⟦(recFd.indices index){ls}⟧ ∈
      ε[γ]⟦I.indexType ls s₁ (fun param => .var ⟨param.val, by omega⟩)
        recFd.indices{ls} index⟧

namespace StrongRecursiveFieldSource

noncomputable abbrev code (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd) :
    CtorRecCode (ι.nparams + nfields) where
  arity := arity
  tele := source.extension.sem
  index γ := sortKey s₁.val (encode (ε₁[γ]⟦recFd.indices{ls} ·⟧))

@[simp] theorem code_index (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (γ : Slots (ι.nparams + nfields + arity)) :
    (code recFd source).index γ =
      sortKey s₁.val (encode (ε₁[γ]⟦recFd.indices{ls} ·⟧)) :=
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
        (ε₁[γ]⟦recFd.indices{ls} ·⟧) =
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
      Expr.denote_map (ν := ![]) pre.sigs hatoms final (recFd.indices index){ls}
    simp only [Expr.map_instL] at his
    simp! only [RecField.instantiatedIndices_id, InstLevel.inst_apply, Expr.denote_wkN]
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
      [zf|$(ε₂[γ]⟦ms s₁⟧) $((ε₁[final]⟦recFd.indices{ls} ·⟧))... value] =
        fibreOp motive (pair (code recFd source |>.index final) value)) :
    ε₂[γ]⟦(recFd.map pre.sigs).ihType ls ms σ e⟧ =
      ihType (code recFd source).tele (code recFd source).index motive δ ε₂[γ]⟦e⟧ := by
  have hden := (Realizes.mapInst source.extension.realizes pre hatoms).denotes_fold_subst
    Expr.forallE Aczel.pi (fun _ _ _ => rfl) (fun _ _ _ h => Aczel.pi_congr h)
    σ γ δ hδ hσ
    (e := Inductive.motiveResult ((ms s₁).wkN arity)
      ((recFd.map pre.sigs).instantiatedIndices ls σ) (e.applyBound arity))
    (leaf := fun final => fibreOp motive (pair ((code recFd source).index final)
      [zf|$(ε₂[γ]⟦e⟧) $(fun f => final (Fin.natAdd (ι.nparams + nfields) f))...]))
    (fun values hvalues => by
      have his (index : Fin (ι.nindices s₁)) :
          ε₂[Fin.append γ values]⟦(recFd.map pre.sigs).instantiatedIndices ls σ index⟧ =
            ε₁[Fin.append δ values]⟦(recFd.indices index){ls}⟧ := by
        rw [RecField.instantiatedIndices, Expr.denote_substLiftN_append, hσ]
        simp only [RecField.map]
        rw [← Expr.map_instL]
        exact Expr.denote_map pre.sigs hatoms _ _
      simpa [Inductive.motiveResult, Expr.denote, his, -Expr.denote_instL] using
        hleaf (Fin.append δ values) (fun _ => by simp) _
          (Reachable.apps_mem_of_base hvalues (fun _ => by simp) hvalue))
  simp only [ihType, SemTele.piAt, SemTele.foldAt, SemTele.app_eq_apps]
  exact hden

end StrongRecursiveFieldSource

theorem RecFieldWF.recursiveSourceOf
    (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁)
    {Δ : Ctx ζ₁ ι.nlevels ι.nparams (ι.nparams + nfields)}
    (hfield : RecFieldWF E₁ I (I.params ++ Δ) recFd)
    (params : StrongTeleModel E₁ ε₁ ![] I.params{ls})
    (extension : StrongTeleExtension E₁ ε₁ ![] params Δ{ls} bound₁)
    (fieldExtension : StrongTeleExtension E₁ ε₁ ![] (params.append extension)
      recFd.tele{ls} bound) :
    Nonempty (StrongRecursiveFieldSource E₁ ε₁ I ls (params.append extension) bound recFd) := by
  have his (index : Fin (ι.nindices s₁)) := hfield.recursiveIndex (ls := ls) index
  rw [Ctx.instL_append] at his
  exact ⟨fieldExtension, fun γ hγ index =>
    (soundness hdecl hrule hE (his index) γ (fieldExtension.semCtx γ hγ)).mem⟩

structure StrongCtorSource (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0) (ctor : Ctor ζ₁ ι s csig)
    (params : StrongTeleModel E ε ![] I.params{ls})
    (bound : Nat) : Type (u + 1) where
  ordinary : StrongTeleExtension E ε ![] params ctor.ordinaryTele{ls} bound
  recursive (f : Fin csig.nrecFields) :
    StrongRecursiveFieldSource E ε I ls (params.append ordinary) bound (ctor.recursive f)

theorem CtorWF.sourceAt (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ ![] I.params{ls})
    (hblock : I.level{ls}.eval ![] = bound + 1) :
    Nonempty (StrongCtorSource E₁ ε₁ I ls ctor params bound) := by
  have hnz : I.level.eval (Level.eval ![] ∘ ls) ≠ 0 := by
    rw [← Level.eval_inst]
    omega
  have ⟨fields⟩ := ((hctor.ordinaryTeleAux _ le_rfl).instLevel
    (Q := fun l => l.eval ![] ≤ bound + 1) ls fun hl => by
      rw [Level.eval_inst, ← hblock, Level.eval_inst]
      exact Level.eval_le_of_imax_le hl hnz).modelExtensionAt hdecl hrule hE (fun hl => hl) params
  refine ⟨⟨fields, fun f => Classical.choice ?_⟩⟩
  have htele := (hctor.recursive f).teleAt (ls := ls) hblock
  rw [Ctx.instL_append] at htele
  have ⟨fieldExtension⟩ :=
    htele.modelExtensionAt hdecl hrule hE (fun hl => hl) (params.append fields)
  exact (hctor.recursive f).recursiveSourceOf hdecl hrule hE params fields fieldExtension

theorem CtorWF.source (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ ![] I.params{ls}) :
    Nonempty (Σ bound, StrongCtorSource E₁ ε₁ I ls ctor params bound) := by
  have ⟨fieldBound, fields⟩ := ((hctor.ordinaryTeleAux _ le_rfl).instLevel
    (Q := fun _ => True) ls fun _ => trivial).modelExtension hdecl hrule hE params
  have hsources (f : Fin csig.nrecFields) :
      Nonempty (Σ bound₂, StrongTeleExtension E₁ ε₁ ![] (params.append fields)
        (ctor.recursive f).tele{ls} bound₂) := by
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
    (his : Realizes ε₁ ![]
      (Reachable Set.univ paramsSem)
      (I.indices s){ls} indicesSem)
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
  apply his.reachable_subst (Γ := I.params{ls}) (γ := γ) σ γ₁
  · simpa [γ₁] using hps
  · intro v
    cases v using Fin.addCases with
    | left param => simp! [σ, γ₁, vps]
    | right index => simp [σ, γ₁]
  · intro v hv
    cases v using Fin.addCases with
    | left param =>
      exact ((Nat.not_le_of_gt param.isLt) (by simpa using hv)).elim
    | right index =>
      simp only [γ₁, Fin.append_right]
      rw [show (I.indices s){ls} = I.indexTele ls s fun param => .var param from
        ((Ctx.substFunctor _).map_id_apply _ _).symm,
        I.indexTele_get, Inductive.indexType_subst,
        show (fun param : Fin ι.nparams => Expr.subst σ ((Expr.var param).wkN (ι.nindices s))) =
          fun param => (Expr.var (param.castLE hm) : Expr ζ₁ 0 m) from
            funext fun param => by simp [σ],
        show (fun i : Fin (ι.nindices s) =>
            Expr.subst σ (.var (Fin.natAdd ι.nparams i))) = is from
          funext fun i => by simp [σ]]
      exact (interp index).mem

theorem StrongRecursiveFieldSource.valuesReachable (recFd : RecField ζ₁ ι nfields arity s₁)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (paramsSem : SemTele 0 ι.nparams)
    (indicesSem : SemTele ι.nparams (ι.nparams + ι.nindices s₁))
    (his : Realizes ε₁ ![] (Reachable Set.univ paramsSem)
      (I.indices s₁){ls} indicesSem)
    {reach : Set (Slots (ι.nparams + nfields))}
    (hreaches : reach ⊆ Reachable Set.univ base.sem)
    (hps : Set.MapsTo (fun γ param => γ (param.castLE (Nat.le_add_right _ _)))
      reach (Reachable Set.univ paramsSem))
    (γ : Slots (ι.nparams + nfields + arity))
    (hγ : γ ∈ Reachable reach (StrongRecursiveFieldSource.code recFd source).tele) :
    Fin.append (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
        (ε₁[γ]⟦recFd.indices{ls} ·⟧) ∈
      Reachable (Reachable Set.univ paramsSem) indicesSem :=
  indexValuesReachable (by omega) his recFd.indices{ls} γ
    (hps (Reachable.base hγ))
    fun index => ⟨rfl, source.mem γ (Reachable.mono hγ hreaches) index⟩

namespace StrongCtorSource

open scoped Classical in
noncomputable def targetValues (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (γ : Slots (ι.nparams + csig.nfields)) (i : Fin (ι.nindices s)) : ZFSet :=
  if γ ∈ Reachable Set.univ (params.append source.ordinary).sem then
    ε₁[γ]⟦(ctor.targetIndices i){ls}⟧ else ∅

theorem targetValues_denotes (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (γ : Slots (ι.nparams + csig.nfields))
    (hγ : γ ∈ Reachable Set.univ (params.append source.ordinary).sem) (i : Fin (ι.nindices s)) :
    ε₁[γ]⟦(ctor.targetIndices i){ls}⟧ = source.targetValues γ i := by
  simp [targetValues, hγ]

noncomputable def targetIndex (source : StrongCtorSource E₁ ε₁ I ls ctor params bound) :
    Dom (ι.nparams + csig.nfields) :=
  fun γ => sortKey s.val (encode (source.targetValues γ))

noncomputable abbrev code (source : StrongCtorSource E₁ ε₁ I ls ctor params bound) :
    CtorCode ι.nparams :=
  ⟨csig.nfields, csig.nrecFields, source.ordinary.sem,
    fun f => StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f), source.targetIndex⟩

theorem codeDomsIn (source : StrongCtorSource E₁ ε₁ I ls ctor params bound) :
    source.code.DomsIn bound :=
  ⟨source.ordinary.bounded, fun f => (source.recursive f).extension.bounded⟩

theorem code_targetIndex_mem_type (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (hvalues : ∀ γ i, source.targetValues γ i ∈ U_ level)
    (γ : Slots ι.nparams) (vargs : ZFSet) :
    source.code.targetIndex γ vargs ∈ U_ level :=
  sortKey_mem_type (encode_fin_mem_type (hvalues _))

noncomputable def recursiveSem
    (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    (block : Dom (ι.nparams + csig.nfields)) (level : Nat) :
    SemTele (ι.nparams + csig.nfields) (ι.nparams + csig.nfields + csig.nrecFields) :=
  SemTele.ofDoms fun f γ =>
    typedRecFieldSet (source.code.recursive f).tele (source.code.recursive f).index (block γ)
      level γ

theorem recursiveSem_realizes
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
    {block : Dom (ι.nparams + csig.nfields)} {level : Nat}
    {reach : Set (Slots (ι.nparams + csig.nfields))}
    (hreaches : reach ⊆ Reachable Set.univ (params.append source.ordinary).sem)
    (sortValues : (s : Fin ι.nsorts) → Slots ι.nparams → Slots (ι.nindices s) → ZFSet)
    (hsortValues : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = sortValues s vps vis)
    (happlyRecursive : ∀ f : Fin csig.nrecFields,
      ∀ γ ∈ Reachable reach
        (StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).tele,
      sortValues (csig.recursiveTarget f)
          (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
          (ε₁[γ]⟦(ctor.recursive f).indices{ls} ·⟧) =
        propSet level (fibreOp
          (block fun current : Fin (ι.nparams + csig.nfields) =>
            γ (current.castLE (StrongRecursiveFieldSource.code (ctor.recursive f)
              (source.recursive f)).tele.le))
          ((StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).index γ))) :
    Realizes ε₂ ![] reach
      ((ctor.map pre.sigs).recursiveFieldTele η ls
        (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
          Expr ζ₂ 0 (ι.nparams + csig.nfields)))
        (Expr.boundVars ι.nparams csig.nfields 0))
      (source.recursiveSem block level) :=
  Realizes.ofTypes fun f γ hγ => by
    have hden := StrongRecursiveFieldSource.denotesDepMapEnv pre hatoms (ctor.recursive f)
      (source.recursive f) hreaches (hsortValues (csig.recursiveTarget f)) (happlyRecursive f) γ hγ
    simp at hden ⊢
    exact hden

end StrongCtorSource

structure StrongCtorModel (E : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0) (ctor : Ctor ζ₁ ι s csig)
    (params : StrongTeleModel E ε ![] I.params{ls}) : Type (u + 1) where
  bound : Nat
  source : StrongCtorSource E ε I ls ctor params bound
  targetInterp : ∀ γ ∈ Reachable Set.univ (params.append source.ordinary).sem,
    ∀ i, ε[γ] ⊨ (ctor.targetIndices i){ls} ≡ (ctor.targetIndices i){ls} :
      I.indexType ls s (fun param => .var ⟨param.val, by omega⟩) ctor.targetIndices{ls} i
  targetBounded : ∃ level, ∀ γ i, source.targetValues γ i ∈ U_ level
  localDoms : ∀ level,
    I.level{ls}.eval ![] = level + 1 → source.code.DomsIn level

open scoped Classical in
theorem CtorWF.model (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hctor : CtorWF E₁ I ctor)
    (params : StrongTeleModel E₁ ε₁ ![] I.params{ls})
    (indices : StrongTeleExtension E₁ ε₁ ![] params (I.indices s){ls} bound₁) :
    Nonempty (StrongCtorModel E₁ ε₁ I ls ctor params) := by
  have make {bound : Nat} (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
      (hlocal : ∀ level, I.level{ls}.eval ![] = level + 1 → source.code.DomsIn level) :
      Nonempty (StrongCtorModel E₁ ε₁ I ls ctor params) := by
    have htarget (i : Fin (ι.nindices s)) := (hctor.targetIndices i).instLevel ls
    rw [Ctx.instL_append] at htarget
    have interp (γ : Slots (ι.nparams + csig.nfields))
        (hγ : γ ∈ Reachable Set.univ (params.append source.ordinary).sem) (i : Fin (ι.nindices s)) :
        ε₁[γ] ⊨ (ctor.targetIndices i){ls} ≡ (ctor.targetIndices i){ls} :
          I.indexType ls s (fun param => .var ⟨param.val, by omega⟩) ctor.targetIndices{ls} i := by
      simpa! using soundness hdecl hrule hE (htarget i) γ
        ((params.append source.ordinary).semCtx γ hγ)
    refine ⟨bound, source, interp, ⟨bound₁, fun γ i => ?_⟩, hlocal⟩
    by_cases hγ : γ ∈ Reachable Set.univ (params.append source.ordinary).sem
    · have hreach := indexValuesReachable (Nat.le_add_right _ _) indices.realizes
        ctor.targetIndices{ls} γ (Reachable.base (Reachable.of_append hγ)) (interp γ hγ)
      simpa [StrongCtorSource.targetValues, hγ] using
        Reachable.mem_type_of_domsIn hreach indices.bounded (Fin.natAdd ι.nparams i) (by simp)
    · simpa [StrongCtorSource.targetValues, hγ] using empty_mem_type
  cases hlevel : I.level{ls}.eval ![] with
  | zero =>
    have ⟨bound, source⟩ := hctor.source hdecl hrule hE params
    exact make source fun _ _ => by omega
  | succ level =>
    have ⟨source⟩ : Nonempty (StrongCtorSource E₁ ε₁ I ls ctor params level) :=
      hctor.sourceAt hdecl hrule hE params (by simpa using hlevel)
    refine make source fun level₁ hlevel₁ => ?_
    obtain rfl : level₁ = level := by omega
    exact source.codeDomsIn

end Metalean
