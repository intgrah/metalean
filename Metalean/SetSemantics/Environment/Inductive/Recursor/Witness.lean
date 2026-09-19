/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Realization
public import Metalean.SetSemantics.Soundness.Core
public import Metalean.Syntax.Inductive.LargeElimination
public import Metalean.Syntax.Inductive.Recursor.Substitution

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {ζ : Sigs} {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}} {ι : IndSig}
  {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level 0} {s s₁ : Fin ι.nsorts}

abbrev RecSlots (ι : IndSig) (s : Fin ι.nsorts) : Type (u + 1) :=
  Slots.{u} (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1)

namespace RecSlots

variable (vps : Slots.{u} ι.nparams) (vms : Slots.{u} ι.nsorts)
  (vmins : (target : Fin ι.nsorts) → Slots.{u} (ι.nctors target))
  (vis : Slots.{u} (ι.nindices s)) (vmaj : ZFSet.{u})
  (γ : RecSlots.{u} ι s) (outer : RecSlots.{u} ι s)
  (values : Slots.{u} (ι.nindices s₁)) (major : ZFSet.{u})

def args : RecSlots.{u} ι s :=
  Fin.snoc (Fin.append (Fin.append (Fin.append vps vms)
    fun tag =>
      let ⟨s₁, c⟩ := Fin.decodeSigma ι.nctors tag
      vmins s₁ c) vis) vmaj

theorem denote_recrSubst {ℓ n : Nat}
    (ε : Atom ζ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat) (γ : Slots n)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) (maj : Expr ζ ℓ n) :
    (ε[ν; γ]⟦Inductive.recrSubst ps ms mins is maj ·⟧) =
      args (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦ms ·⟧) (ε[ν; γ]⟦mins · ·⟧)
        (ε[ν; γ]⟦is ·⟧) ε[ν; γ]⟦maj⟧ := by
  change Expr.denote ε ν γ ∘ Inductive.recrSubst _ _ _ _ _ = _
  rw [Inductive.recrSubst, Fin.comp_snoc]
  simp [Function.comp_def, Fin.append_comp, args]

def prefixOf : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
  fun current => Fin.init γ (current.castLE (by omega))

def paramsOf : Slots ι.nparams :=
  fun param => prefixOf γ (param.castLE (by omega))

def motivesOf (target : Fin ι.nsorts) : ZFSet :=
  prefixOf γ ⟨ι.nparams + target.val, by omega⟩

def casesOf : Slots (Fin.sum ι.nctors) :=
  fun tag => prefixOf γ ⟨ι.nparams + ι.nsorts + tag.val, by omega⟩

@[simp] theorem paramsOf_args : paramsOf (args vps vms vmins vis vmaj) = vps := by
  funext param
  change args vps vms vmins vis vmaj (Fin.castAdd (ι.nindices s)
    (Fin.castAdd (Fin.sum ι.nctors) (Fin.castAdd ι.nsorts param))).castSucc = vps param
  simp [args]

@[simp] theorem motivesOf_args : motivesOf (args vps vms vmins vis vmaj) = vms := by
  funext target
  change args vps vms vmins vis vmaj (Fin.castAdd (ι.nindices s)
    (Fin.castAdd (Fin.sum ι.nctors) (Fin.natAdd ι.nparams target))).castSucc = vms target
  simp [args]

@[simp] theorem casesOf_args (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    casesOf (args vps vms vmins vis vmaj) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩) = vmins s₁ c := by
  change args vps vms vmins vis vmaj (Fin.castAdd (ι.nindices s)
    (Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩))).castSucc = _
  rw [args, Fin.snoc_castSucc, Fin.append_left, Fin.append_right, Fin.decodeSigma_encodeSigma]

def recrParams (γ : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors)) :
    Slots ι.nparams :=
  fun param => γ (param.castLE (by omega))

def recrIndices (s : Fin ι.nsorts)
    (γ : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s)) :
    Slots (ι.nindices s) :=
  fun index => γ
    ⟨ι.nparams + ι.nsorts + Fin.sum ι.nctors + index.val, by omega⟩

abbrev withIndices :
    Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s₁) :=
  Fin.append (prefixOf outer) values

abbrev childOf : RecSlots.{u} ι s₁ :=
  Fin.snoc (withIndices outer values) major

theorem append_params_motives_cases :
    Fin.append (Fin.append (paramsOf γ) (motivesOf γ)) (casesOf γ) =
      prefixOf γ := by
  funext current
  cases current using Fin.addCases with
  | left current =>
    cases current using Fin.addCases with
    | left param => simp; rfl
    | right target => simp; rfl
  | right tag => simp; rfl

abbrev indexValuesOf : Slots (ι.nindices s) :=
  fun index =>
    γ ⟨ι.nparams + ι.nsorts + Fin.sum ι.nctors + index.val, by omega⟩

@[simp] theorem indexValuesOf_args :
    indexValuesOf (args vps vms vmins vis vmaj) = vis :=
  funext fun index => by
    change args vps vms vmins vis vmaj
      (Fin.castSucc (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index)) = vis index
    rw [args, Fin.snoc_castSucc, Fin.append_right]

@[simp] theorem recrIndices_withIndices :
    recrIndices s₁ (withIndices outer values) = values :=
  funext fun index => Fin.append_right _ _ index

theorem withIndices_params :
    (fun param : Fin ι.nparams =>
      withIndices outer values (param.castLE (by omega))) = paramsOf outer :=
  funext fun param => Fin.append_of_lt _ _ _ (by
    change param.val < ι.nparams + ι.nsorts + Fin.sum ι.nctors
    omega)

@[simp] theorem pull_recrParams_withIndices :
    Slots.pull (recrParams) (withIndices outer values) =
      Fin.append (paramsOf outer) values := by
  rw [Slots.pull_append]
  rfl

@[simp] theorem prefixOf_childOf :
    prefixOf (childOf outer values major) = prefixOf outer :=
  funext fun current => by
    unfold prefixOf childOf withIndices Fin.init
    rw [Fin.snoc_of_lt _ _ _ (by
      change current.val < ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s₁
      omega), Fin.append_of_lt _ _ _ current.isLt]
    rfl

@[simp] theorem paramsOf_childOf :
    paramsOf (childOf outer values major) = paramsOf outer :=
  funext fun _ => congrFun (prefixOf_childOf outer values major) _

@[simp] theorem motivesOf_childOf :
    motivesOf (childOf outer values major) = motivesOf outer :=
  funext fun _ => congrFun (prefixOf_childOf outer values major) _

@[simp] theorem casesOf_childOf :
    casesOf (childOf outer values major) = casesOf outer :=
  funext fun _ => congrFun (prefixOf_childOf outer values major) _

noncomputable def indicesOfSlots : ZFSet :=
  encode (indexValuesOf γ)

def majorOfSlots : ZFSet :=
  γ (Fin.last (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s))

@[simp] theorem majorOfSlots_args :
    majorOfSlots (args vps vms vmins vis vmaj) = vmaj := by
  simp [majorOfSlots, args]

@[simp] theorem majorOfSlots_childOf :
    majorOfSlots (childOf outer values major) = major := by
  simp [majorOfSlots]

@[simp] theorem indexValuesOf_childOf :
    indexValuesOf (childOf outer values major) = values :=
  funext fun index => by
    rw [show indexValuesOf (childOf outer values major) index =
      withIndices outer values (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) index) from
      Fin.snoc_of_lt _ _ _ (by
        change ι.nparams + ι.nsorts + Fin.sum ι.nctors + index.val <
          ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s₁
        omega), withIndices, Fin.append_right]

@[simp] theorem indicesOfSlots_childOf :
    indicesOfSlots (childOf outer values major) = encode values := by
  simp [indicesOfSlots]

end RecSlots

theorem SemDefeq.recrSubst {I : Inductive ζ ι} {l : Level 0} {n : Nat} {γ : Slots n}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ 0 n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ 0 n}
    {mins₁ mins₂ : (target : Fin ι.nsorts) → Fin (ι.nctors target) → Expr ζ 0 n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ 0 n} {maj₁ maj₂ : Expr ζ 0 n}
    (v : Fin (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1)) :
    (∀ param, ε[γ] ⊨ ps₁ param ≡ ps₂ param : I.paramType ls ps₁ param) →
    (∀ target, ε[γ] ⊨ ms₁ target ≡ ms₂ target :
      I.motiveType η ls ps₁ l target) →
    (∀ target ctor, ε[γ] ⊨ mins₁ target ctor ≡ mins₂ target ctor :
      I.caseFnType η ls ps₁ ms₁ target ctor) →
    (∀ index, ε[γ] ⊨ is₁ index ≡ is₂ index : I.indexType ls s ps₁ is₁ index) →
    ε[γ] ⊨ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ →
    ε[γ] ⊨ Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v ≡
      Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v :
      (Ctx.get v (I.recrTele η s ls l)).subst (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁) := by
  intro hps hms hmins his hmaj
  cases v using Fin.lastCases with
  | last => simpa using hmaj
  | cast v =>
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases with
        | left param => simpa using hps param
        | right target => simpa using hms target
      | right tag =>
        obtain ⟨⟨s₁, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
          ⟨_, Fin.encodeSigma_decodeSigma ..⟩
        simpa using hmins s₁ c
    | right index =>
      simpa only [Inductive.recrSubst_index, Inductive.recrTele_get_index_subst] using his index

theorem SemDefeq.recr
    {l : Level 0}
    {tele : SemTele.{u} 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1)}
    {leaf : RecSlots.{u} ι s → ZFSet.{u}}
    (hrealizes : Realizes ε zeroNs Set.univ ((E.get η).block.recrTele η s ls l) tele)
    (hleaf : ∀ γ ∈ Reachable Set.univ tele, leaf γ ∈ ε[γ]⟦ι.recrBody s⟧)
    (hatom : ∀ vps vms vmins vis vmaj,
      ε (.recr η s ls l vps vms vmins vis vmaj) = leaf (RecSlots.args vps vms vmins vis vmaj))
    {n : Nat} {γ : Slots n}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ 0 n}
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ 0 n}
    {mins₁ mins₂ : (s : Fin ι.nsorts) →
      Fin (ι.nctors s) → Expr ζ 0 n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ 0 n}
    {maj₁ maj₂ : Expr ζ 0 n} :
    (∀ p, ε[γ] ⊨ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ s, ε[γ] ⊨ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ s c, ε[γ] ⊨ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c) →
    (∀ index, ε[γ] ⊨ is₁ index ≡ is₂ index : (E.get η).block.indexType ls s ps₁ is₁ index) →
    ε[γ] ⊨ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ →
    ε[γ] ⊨ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡ .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁ := by
  intro hps hms hmins his hmaj
  have hreachable := SemDefeq.reachable hrealizes
    (SemDefeq.recrSubst · hps hms hmins his hmaj)
  have hbody := Expr.denote_subst (ε := ε) (ν := zeroNs) γ
    (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁) (ι.recrBody s)
  rw [IndSig.recrBody_subst] at hbody
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun s => (hms s).eq,
      funext₂ fun s c => (hmins s c).eq,
      funext fun i => (his i).eq, hmaj.eq]
  · rw [hbody]
    change ε (.recr η s ls l _ _ _ _ _) ∈ _
    rw [hatom, ← RecSlots.denote_recrSubst]
    exact hleaf _ hreachable

end Metalean
