/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.ConstructorPredecessors
public import Metalean.SetSemantics.Realization
public import Metalean.SetSemantics.Soundness

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {ℓ ℓ₁ n m count level bound bound₁ : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ ℓ → ZFSet.{u}} {ε₂ : Atom ζ₂ ℓ → ZFSet.{u}} {ν : Param ℓ → Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₁ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ}
  {Γ : Ctx ζ₁ ℓ 0 n} {Δ : Ctx ζ₁ ℓ n m}

structure StrongTeleModel (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat)
    (Γ : Ctx ζ₁ ℓ 0 n) : Type (u + 1) where
  sem : SemTele.{u} 0 n
  bounded : ∃ level, sem.DomsIn level
  realizes : Realizes ε₁ ν Set.univ Γ sem

structure StrongTeleExtension (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (Δ : Ctx ζ₁ ℓ n m) (bound : Nat) : Type (u + 1) where
  sem : SemTele.{u} n m
  bounded : sem.DomsIn bound
  realizes : Realizes ε₁ ν (Reachable Set.univ base.sem) Δ sem

variable {base : StrongTeleModel E₁ ε₁ ν Γ}

theorem StrongTeleModel.semCtx (model : StrongTeleModel E₁ ε₁ ν Γ)
    (γ : Slots n) (hγ : γ ∈ Reachable Set.univ model.sem) :
    ε₁[ν] ⊨ γ : Γ :=
  model.realizes.semCtx γ hγ

theorem StrongTeleExtension.semCtx (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound)
    (γ : Slots m) (hγ : γ ∈ Reachable (Reachable Set.univ base.sem) extension.sem) :
    ε₁[ν] ⊨ γ : (Γ ++ Δ) :=
  (base.realizes.append extension.realizes).semCtx γ (.append hγ)

def StrongTeleExtension.mono (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound)
    (hle : bound ≤ bound₁) :
    StrongTeleExtension E₁ ε₁ ν base Δ bound₁ where
  sem := extension.sem
  bounded := extension.bounded.mono hle
  realizes := extension.realizes

open scoped Classical in
private theorem SemDefeq.exists_domain {t : Expr ζ₁ ℓ m}
    {reach : Set (Slots.{u} m)} {l : Level ℓ}
    (interp : ∀ γ ∈ reach, ε₁[ν; γ] ⊨ t ≡ t : .sort l)
    (hlevel : l.eval ν ≤ bound + 1) :
    ∃ domain : Dom.{u} m, (∀ γ, domain γ ∈ U_ bound) ∧
      ∀ γ ∈ reach, ε₁[ν; γ]⟦t⟧ = domain γ := by
  refine ⟨fun γ => if γ ∈ reach then ε₁[ν; γ]⟦t⟧ else ∅,
    fun γ => ?_, fun γ hγ => by simp [hγ]⟩
  by_cases hγ : γ ∈ reach
  · simpa [hγ] using mem_type_of_mem_sort hlevel (interp γ hγ).mem
  · simpa [hγ] using empty_mem_type

theorem TeleWF.modelExtensionAt (hdecl : SemDecls E₁ ε₁ ν)
    (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    {P : Level ℓ → Prop}
    (hls : ∀ {l}, P l → l.eval ν ≤ bound + 1)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (hΔ : TeleWF E₁ P Γ Δ) :
    Nonempty (StrongTeleExtension E₁ ε₁ ν base Δ bound) := by
  induction hΔ with
  | nil => exact ⟨#t[], .nil, .nil⟩
  | @snoc m Δ t _ hA ih =>
    have ⟨model⟩ := ih
    have ⟨l, hl, ht⟩ := hA
    have ⟨_, hbounded, htype⟩ := SemDefeq.exists_domain
      (fun γ hγ => soundness hdecl hrule hE ht γ (model.semCtx γ hγ)) (hls hl)
    exact ⟨model.sem.snoc _, .snoc model.bounded hbounded, .snoc model.realizes htype⟩

theorem TeleWF.modelExtension (hdecl : SemDecls E₁ ε₁ ν)
    (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (hΔ : TeleWF E₁ (fun _ => True) Γ Δ) :
    Nonempty (Σ bound, StrongTeleExtension E₁ ε₁ ν base Δ bound) := by
  induction hΔ with
  | nil => exact ⟨0, #t[], .nil, .nil⟩
  | @snoc m Δ t _ hA ih =>
    have ⟨level, model⟩ := ih
    have ⟨l, _, ht⟩ := hA
    have ⟨_, hbounded, htype⟩ := SemDefeq.exists_domain
      (fun γ hγ => soundness hdecl hrule hE ht γ (model.semCtx γ hγ)) (Nat.le_succ (l.eval ν))
    exact ⟨max level (l.eval ν), model.sem.snoc _,
      .snoc (model.bounded.mono (Nat.le_max_left _ _))
        (fun γ => type_mono (Nat.le_max_right _ _) (hbounded γ)),
      .snoc model.realizes htype⟩

theorem TeleWF.model (hdecl : SemDecls E₁ ε₁ ν) (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    (hΓ : TeleWF E₁ (fun _ => True) #t[] Γ) :
    Nonempty (StrongTeleModel E₁ ε₁ ν Γ) :=
  have ⟨_, extension⟩ := hΓ.modelExtension hdecl hrule hE ⟨#t[], ⟨0, .nil⟩, .nil⟩
  ⟨extension.sem, ⟨_, extension.bounded⟩,
    extension.realizes.monoReach fun _ _ => .nil trivial⟩

def StrongTeleModel.append (base : StrongTeleModel E₁ ε₁ ν Γ)
    (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound) :
    StrongTeleModel E₁ ε₁ ν (Γ ++ Δ) where
  sem := base.sem ++ extension.sem
  bounded :=
    have ⟨baseLevel, hbase⟩ := base.bounded
    ⟨max baseLevel bound, (hbase.mono (Nat.le_max_left _ _)).append
      (extension.bounded.mono (Nat.le_max_right _ _))⟩
  realizes := base.realizes.append extension.realizes

theorem Realizes.mapInst {Δ : Ctx ζ₁ ℓ₁ n m} {levelSubst : Param ℓ₁ → Level ℓ}
    {reach : Set (Slots n)} {Δsem : SemTele n m}
    (h : Realizes ε₁ ν reach (Ctx.instL levelSubst Δ) Δsem)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    Realizes ε₂ ν reach (Ctx.instL levelSubst (Δ.map pre.sigs)) Δsem :=
  (congrArg (fun Δ => Realizes ε₂ ν _ Δ _)
    (Ctx.map_instL pre.sigs levelSubst Δ)).mp (h.map pre hatoms)

theorem StrongTeleModel.realizes_mapInst
    {Γ : Ctx ζ₁ ℓ₁ 0 n} {levelSubst : Param ℓ₁ → Level ℓ}
    (model : StrongTeleModel E₁ ε₁ ν (Ctx.instL levelSubst Γ))
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    Realizes ε₂ ν Set.univ (Ctx.instL levelSubst (Γ.map pre.sigs)) model.sem :=
  model.realizes.mapInst pre hatoms

theorem StrongTeleExtension.realizes_mapInst
    {Γ : Ctx ζ₁ ℓ₁ 0 n} {Δ : Ctx ζ₁ ℓ₁ n m} {levelSubst : Param ℓ₁ → Level ℓ}
    {base : StrongTeleModel E₁ ε₁ ν (Ctx.instL levelSubst Γ)}
    (extension : StrongTeleExtension E₁ ε₁ ν base (Ctx.instL levelSubst Δ) bound)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    Realizes ε₂ ν (Reachable Set.univ base.sem)
      (Ctx.instL levelSubst (Δ.map pre.sigs)) extension.sem :=
  extension.realizes.mapInst pre hatoms

inductive CtorCode.Interprets (ε₁ : Atom ζ₁ ℓ → ZFSet) (ν : Param ℓ → Nat) (block : ZFSet)
    (level : Nat) :
    {base scope : Nat} → (Slots scope → Slots base) →
      Set (Slots scope) →
      Expr ζ₁ ℓ scope → CtorCode base → Prop
  | target {base scope : Nat} {project : Slots scope → Slots base}
      {reach : Set (Slots scope)}
      {t : Expr ζ₁ ℓ scope} {index : Dom base} :
    (∀ γ ∈ reach,
      ε₁[ν; γ]⟦t⟧ = propSet level (fibreOp block (index (project γ)))) →
    CtorCode.Interprets ε₁ ν block level project reach t (.target index)
  | arg {base scope : Nat} {project : Slots scope → Slots base}
      {reach : Set (Slots scope)}
      {t : Expr ζ₁ ℓ scope} {rest : Expr ζ₁ ℓ (scope + 1)}
      {domain : Dom base} {restSem : CtorCode (base + 1)} :
    (∀ γ ∈ reach,
      ε₁[ν; γ]⟦t⟧ = domain (project γ)) →
    CtorCode.Interprets ε₁ ν block level
      (fun γ : Slots (scope + 1) =>
        (project (Fin.init γ)).snoc (γ (Fin.last scope)))
      {γ : Slots (scope + 1) |
        Fin.init γ ∈ reach ∧
          γ (Fin.last scope) ∈ domain (project (Fin.init γ))}
      rest restSem →
    CtorCode.Interprets ε₁ ν block level project reach (.forallE t rest)
      (.arg domain restSem)
  | recArg {base scope arity : Nat}
      {project : Slots scope → Slots base}
      {reach : Set (Slots scope)}
      {t : Expr ζ₁ ℓ scope} {rest : Expr ζ₁ ℓ (scope + 1)}
      {tele : SemTele base (base + arity)} {index : Dom (base + arity)}
      {restSem : CtorCode base} :
    (∀ γ ∈ reach,
      ε₁[ν; γ]⟦t⟧ = typedRecFieldSet tele index block level (project γ)) →
    CtorCode.Interprets ε₁ ν block level
      (fun γ : Slots (scope + 1) => project (Fin.init γ))
      {γ : Slots (scope + 1) |
        Fin.init γ ∈ reach ∧
          γ (Fin.last scope) ∈
            typedRecFieldSet tele index block level (project (Fin.init γ))}
      rest restSem →
    CtorCode.Interprets ε₁ ν block level project reach (.forallE t rest)
      (.recArg tele index restSem)

section

variable {block : ZFSet.{u}}

theorem CtorCode.Interprets.monoReach
    {base scope : Nat}
    {project : Slots scope → Slots base}
    {reach₁ reach₂ : Set (Slots scope)}
    {t : Expr ζ₁ ℓ scope} {code : CtorCode base}
    (h : CtorCode.Interprets ε₁ ν block level project reach₁ t code)
    (hreaches : reach₂ ⊆ reach₁) :
    CtorCode.Interprets ε₁ ν block level project reach₂ t code := by
  induction h with
  | target ht => exact .target fun γ hγ => ht γ (hreaches hγ)
  | arg hA hrest ih =>
    exact .arg (fun γ hγ => hA γ (hreaches hγ))
      (ih fun γ hγ => ⟨hreaches hγ.1, hγ.2⟩)
  | recArg hA hrest ih =>
    exact .recArg (fun γ hγ => hA γ (hreaches hγ))
      (ih fun γ hγ => ⟨hreaches hγ.1, hγ.2⟩)

theorem CtorCode.Interprets.prependOrdinary
    {reach : Set (Slots n)} {Δsem : SemTele n m}
    {t : Expr ζ₁ ℓ m} {rest : CtorCode m}
    (hargs : Realizes ε₁ ν reach Δ Δsem)
    (hrest : CtorCode.Interprets ε₁ ν block level (fun γ => γ)
      (Reachable reach Δsem) t rest) :
    CtorCode.Interprets ε₁ ν block level (fun γ => γ) reach (Ctx.pi t Δ)
      (CtorCode.prependOrdinary Δsem rest) := by
  induction hargs with
  | nil => exact hrest.monoReach fun γ hγ => .nil hγ
  | snoc _ hdomain ih =>
    refine ih (.arg hdomain ?_)
    simp only [Fin.snoc_init_self]
    exact hrest.monoReach fun _ ⟨hγ, hvalue⟩ => .snoc hγ hvalue

theorem CtorCode.Interprets.map
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    {base scope : Nat} {project : Slots scope → Slots base}
    {reach : Set (Slots scope)} {t : Expr ζ₁ ℓ scope} {code : CtorCode base}
    (h : CtorCode.Interprets ε₁ ν block level project reach t code) :
    CtorCode.Interprets ε₂ ν block level project reach (t.map pre.sigs) code := by
  induction h with
  | target ht =>
    exact .target fun γ hρ => (Expr.denote_map pre.sigs hatoms _ _).trans (ht γ hρ)
  | arg hA hrest ih =>
    exact .arg (fun γ hρ => (Expr.denote_map pre.sigs hatoms _ _).trans (hA γ hρ))
      (by simpa using ih)
  | recArg hA hrest ih =>
    exact .recArg (fun γ hρ => (Expr.denote_map pre.sigs hatoms _ _).trans (hA γ hρ))
      (by simpa using ih)

inductive RecursivePhaseRealizes (ε₁ : Atom ζ₁ ℓ → ZFSet) (ν : Param ℓ → Nat) {base : Nat}
    (block : Dom base) (level : Nat) :
    {scope : Nat} → (Slots scope → Slots base) →
      Set (Slots scope) →
    {count : Nat} → (Fin count → CtorRecCode.Packed base) →
      {endScope : Nat} → (Slots endScope → Slots base) →
      Set (Slots endScope) → Ctx ζ₁ ℓ scope endScope → Prop
  | nil {scope : Nat} {project : Slots scope → Slots base}
      {reach : Set (Slots scope)} :
    RecursivePhaseRealizes ε₁ ν block level project reach
      ![] project reach .nil
  | cons {scope count : Nat} {project : Slots scope → Slots base}
      {reach : Set (Slots scope)}
      {fields : Fin (count + 1) → CtorRecCode.Packed base}
      {endScope : Nat} {projectEnd : Slots endScope → Slots base}
      {reachEnd : Set (Slots endScope)} {t : Expr ζ₁ ℓ scope}
      {Θ : Ctx ζ₁ ℓ (scope + 1) endScope} :
    (∀ γ ∈ reach,
      ε₁[ν; γ]⟦t⟧ = typedRecFieldSetDep (fields 0).2.tele (fields 0).2.index
          block level (project γ)) →
    RecursivePhaseRealizes ε₁ ν block level
      (fun γ => project (Fin.init γ))
      {γ | Fin.init γ ∈ reach ∧
        γ (Fin.last scope) ∈
          typedRecFieldSetDep (fields 0).2.tele (fields 0).2.index
            block level (project (Fin.init γ))}
      (fun f => fields f.succ)
      projectEnd reachEnd Θ →
    RecursivePhaseRealizes ε₁ ν block level project reach
      fields projectEnd reachEnd (#t[t] ++ Θ)

section

variable {base : Nat} {project : Slots n → Slots base} {reach : Set (Slots n)}
  {fields : Fin count → CtorRecCode.Packed base} {projectEnd : Slots m → Slots base}
  {reachEnd : Set (Slots m)} {t : Expr ζ₁ ℓ m}

theorem RecursivePhaseRealizes.prepend
    (hphase : RecursivePhaseRealizes ε₁ ν (fun _ => block) level
      project reach fields projectEnd reachEnd Δ)
    {rest : CtorCode base}
    (hrest : CtorCode.Interprets ε₁ ν block level projectEnd reachEnd t rest) :
    CtorCode.Interprets ε₁ ν block level project reach (Ctx.pi t Δ)
      (CtorCode.prependRecursive count fields rest) := by
  induction hphase with
  | nil => simpa [CtorCode.prependRecursive] using hrest
  | cons hA htail ih =>
    simpa [Ctx.pi, Tele.foldr_append, CtorCode.prependRecursive] using
      CtorCode.Interprets.recArg hA (ih hrest)

theorem RecursivePhaseRealizes.snoc {block : Dom base}
    (hphase : RecursivePhaseRealizes (base := base) ε₁ ν block level
      project reach fields projectEnd reachEnd Δ)
    (f : CtorRecCode.Packed base)
    (ht : ∀ γ ∈ reachEnd,
      ε₁[ν; γ]⟦t⟧ = typedRecFieldSetDep f.2.tele f.2.index block level (projectEnd γ)) :
    RecursivePhaseRealizes (base := base) ε₁ ν block level project reach
      (Fin.snoc fields f)
      (fun γ => projectEnd (Fin.init γ))
      {γ | Fin.init γ ∈ reachEnd ∧
        γ (Fin.last m) ∈
          typedRecFieldSetDep f.2.tele f.2.index block level (projectEnd (Fin.init γ))}
      (Δ.snoc t) := by
  induction hphase with
  | nil =>
    rw [Fin.snoc_zero]
    exact (show Fin.cons f ![] = fun _ => f from
      funext (Fin.cases rfl fun i => i.elim0)) ▸ RecursivePhaseRealizes.cons
        (fields := Fin.cons f ![]) (Θ := .nil) ht .nil
  | @cons _ count₁ _ _ fields₁ _ _ _ _ _ hhead _ ih =>
    have hresult := RecursivePhaseRealizes.cons
      (fields := Fin.cons (fields₁ 0) (Fin.snoc (fun i => fields₁ i.succ) f)) hhead
      (by rw [Fin.cons_zero]; exact ih ht)
    rw [Fin.cons_snoc_eq_snoc_cons,
      show Fin.cons (fields₁ 0) (fun i => fields₁ i.succ) = fields₁ from
        Fin.cons_self_tail fields₁] at hresult
    simpa using hresult

end

end

structure InductiveModel (ι : IndSig) : Type (u + 1) where
  paramsSem : SemTele.{u} 0 ι.nparams
  codes (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) : CtorCode.{u} ι.nparams
  bound : ZFSet.{u}
  level : Nat
  ordinaryOf (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots.{u} ι.nparams) (vargs : ZFSet.{u}) :
    Slots.{u} (ι.nparams + (ι.ctors s c).nfields)
  indicesSem (s : Fin ι.nsorts) : SemTele.{u} ι.nparams (ι.nparams + ι.nindices s)
  targetValues (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Slots.{u} (ι.nparams + (ι.ctors s c).nfields) → Fin (ι.nindices s) → ZFSet.{u}

namespace InductiveModel

variable {witness : InductiveModel.{u} ι}

noncomputable def block (witness : InductiveModel ι) (vps : Slots ι.nparams) : ZFSet :=
  indSet witness.codes witness.bound vps

noncomputable def sortValue (witness : InductiveModel ι) (s : Fin ι.nsorts)
    (vps : Slots ι.nparams) (vis : Slots (ι.nindices s)) : ZFSet :=
  propSet witness.level (fibreOp (witness.block vps) (sortKey s.val (encode vis)))

structure Interprets (ε₁ : Atom ζ₁ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat)
    (I : Inductive ζ₁ ι) (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) (witness : InductiveModel.{u} ι) : Prop where
  level_eq : witness.level = (I.level.inst ls).eval ν
  params : Realizes ε₁ ν Set.univ (Ctx.instL ls I.params) witness.paramsSem
  indicesRealizes (s : Fin ι.nsorts) :
    Realizes ε₁ ν (Reachable Set.univ witness.paramsSem)
      (Ctx.instL ls (I.indices s)) (witness.indicesSem s)
  ctorRealizes : ∀ s c, ∀ vps ∈ Reachable Set.univ witness.paramsSem,
    CtorCode.Interprets ε₁ ν (witness.block vps) witness.level (fun γ => γ) {vps}
      (let sig := ι.ctors s c
       let C := I.ctors s c
       let ps : Fin ι.nparams → Expr ζ₁ ℓ ι.nparams := fun param => .var param
       Ctx.pi
         (.ind η s ls (sig.fieldParams ps)
           fun index => C.targetIndex ls (sig.fieldParams ps) sig.fieldOrdinary index)
         (C.fieldTele η ls ps))
      (witness.codes s c)
  ordinaryOf_castLE : ∀ s c vps vargs (param : Fin ι.nparams),
    witness.ordinaryOf s c vps vargs (param.castLE (Nat.le_add_right _ _)) = vps param
  targetIndex_eq : ∀ s c vps vargs,
    (witness.codes s c).targetIndex vps vargs =
      sortKey s.val (encode (witness.targetValues s c (witness.ordinaryOf s c vps vargs)))
  targetRealizes : ∀ s c, ∀ vps ∈ Reachable Set.univ witness.paramsSem,
    ∀ vargs ∈ (witness.codes s c).argSet (witness.block vps) vps, ∀ index,
    ε₁[ν; witness.ordinaryOf s c vps vargs]⟦Expr.instL ls ((I.ctors s c).targetIndices index)⟧ =
      witness.targetValues s c (witness.ordinaryOf s c vps vargs) index
  fieldsRealize : ∀ s c, ∀ vps ∈ Reachable Set.univ witness.paramsSem,
    ∀ vargs ∈ (witness.codes s c).argSet (witness.block vps) vps,
    ε₁[ν] ⊨ witness.ordinaryOf s c vps vargs :
      Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)
  bounded : ∀ vps,
    Set.MapsTo (indOp witness.codes vps) (Set.Iic witness.bound) (Set.Iic witness.bound)

theorem Interprets.map
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (h : witness.Interprets ε₁ ν I η ls) :
    witness.Interprets ε₂ ν (I.map pre.sigs) (η.map pre.sigs) ls where
  level_eq := h.level_eq
  params := h.params.mapInst pre hatoms
  indicesRealizes s := (h.indicesRealizes s).mapInst pre hatoms
  ctorRealizes s c vps hps := by
    refine (congrArg (fun Δ => CtorCode.Interprets ε₂ ν _ _ _ _ (Ctx.pi _ Δ) _)
      ((I.ctors s c).fieldTele_map pre.sigs η ls fun p => .var p)).mp ?_
    simpa [Inductive.map, Expr.map] using
      (h.ctorRealizes s c vps hps).map pre hatoms
  ordinaryOf_castLE := h.ordinaryOf_castLE
  targetIndex_eq := h.targetIndex_eq
  targetRealizes s c vps hps vargs hargs index := by
    simpa [Inductive.map, Ctor.map] using
      (Expr.denote_map pre.sigs hatoms _ _).trans (h.targetRealizes s c vps hps vargs hargs index)
  fieldsRealize s c vps hps vargs hargs v := by
    have hv := h.fieldsRealize s c vps hps vargs hargs v
    rw [← Expr.denote_map pre.sigs hatoms, ← Ctx.get_map] at hv
    simpa [Inductive.map] using hv
  bounded := h.bounded

end InductiveModel

end Metalean
