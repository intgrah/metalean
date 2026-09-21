/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
public import Metalean.SetSemantics.Soundness.Core
import Metalean.SetTheory.ZFC.AczelUniverse

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {ε : Atom ζ ℓ → ZFSet}
  {ν : Param ℓ → Nat} {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}

def SemDecls (E : Env ζ) (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) : Prop :=
  ∀ {kind : ConstKind} {nlevels : Nat} (η : Head ζ (.const kind nlevels))
    (ls : Fin nlevels → Level ℓ),
  ε (.const η ls) ∈ ε[ν; ![]]⟦(E.get η).constType.instL ls⟧

structure SemDeclRules (E : Env ζ) (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) : Prop where
  ind {n : Nat} {γ : Slots n} {ι} {η : Head ζ (.inductive ι)} {s ls ps₁ ps₂ is₁ is₂} :
    Env.Ordered E →
    (∀ p, ε[ν; γ] ⊨ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ i, ε[ν; γ] ⊨ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i) →
    ε[ν; γ] ⊨ .ind η s ls ps₁ is₁ ≡ .ind η s ls ps₂ is₂ : .sort ((E.get η).block.level.inst ls)
  ctor {n : Nat} {γ : Slots n} {ι} {η : Head ζ (.inductive ι)}
      {s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂} :
    Env.Ordered E →
    (∀ p, ε[ν; γ] ⊨ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ f, ε[ν; γ] ⊨ fds₁ f ≡ fds₂ f : (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le))) →
    (∀ f, ε[ν; γ] ⊨ recFds₁ f ≡ recFds₂ f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps₁ (Fin.append ps₁ fds₁)) →
    ε[ν; γ] ⊨ .ctor η s c ls ps₁ fds₁ recFds₁ ≡ .ctor η s c ls ps₂ fds₂ recFds₂ :
      .ind η s ls ps₁ (fun i => ((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i)
  recr {n : Nat} {γ : Slots n} {ι} {η : Head ζ (.inductive ι)}
      {s ls l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂} :
    Env.Ordered E →
    (E.get η).block.RecAllowed l →
    (∀ p, ε[ν; γ] ⊨ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ s, ε[ν; γ] ⊨ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ s c, ε[ν; γ] ⊨ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c) →
    (∀ i, ε[ν; γ] ⊨ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i) →
    ε[ν; γ] ⊨ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ →
    ε[ν; γ] ⊨ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡ .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁
  quot {n : Nat} {γ : Slots n} {η : Head ζ .quot} {l α α' r r'} :
    Env.Ordered E →
    ε[ν; γ] ⊨ α ≡ α' : .sort l →
    ε[ν; γ] ⊨ r ≡ r' : Quot.relType α →
    ε[ν; γ] ⊨ .quot η l α r ≡ .quot η l α' r' : .sort l
  quotMk {n : Nat} {γ : Slots n} {η : Head ζ .quot} {l α α' r r' a a'} :
    Env.Ordered E →
    ε[ν; γ] ⊨ α ≡ α' : .sort l →
    ε[ν; γ] ⊨ r ≡ r' : Quot.relType α →
    ε[ν; γ] ⊨ a ≡ a' : α →
    ε[ν; γ] ⊨ .quotMk η l α r a ≡ .quotMk η l α' r' a' : .quot η l α r
  quotLift {n : Nat} {γ : Slots n} {η : Head ζ .quot} {l₁ l₂ α α' r r' β β' f f' h h' a a'} :
    Env.Ordered E →
    ε[ν; γ] ⊨ α ≡ α' : .sort l₁ →
    ε[ν; γ] ⊨ r ≡ r' : Quot.relType α →
    ε[ν; γ] ⊨ β ≡ β' : .sort l₂ →
    ε[ν; γ] ⊨ f ≡ f' : .forallE α β.wk →
    ε[ν; γ] ⊨ h ≡ h' : Quot.compatType (E.get η).eqHead l₂ α r β f →
    ε[ν; γ] ⊨ a ≡ a' : .quot η l₁ α r →
    ε[ν; γ] ⊨ .quotLift η l₁ l₂ α r β f h a ≡ .quotLift η l₁ l₂ α' r' β' f' h' a' : β
  quotInd {n : Nat} {γ : Slots n} {η : Head ζ .quot} {l α α' r r' β β' f f' a a'} :
    Env.Ordered E →
    ε[ν; γ] ⊨ α ≡ α' : .sort l →
    ε[ν; γ] ⊨ r ≡ r' : Quot.relType α →
    ε[ν; γ] ⊨ β ≡ β' : Quot.motiveType η l α r →
    ε[ν; γ] ⊨ f ≡ f' : Quot.minorType η l α r β →
    ε[ν; γ] ⊨ a ≡ a' : .quot η l α r →
    ε[ν; γ] ⊨ .quotInd η l α r β f a ≡ .quotInd η l α' r' β' f' a' : .app β a
  quotIota {n : Nat} {γ : Slots n} {η : Head ζ .quot} {l₁ l₂ α r β f h a} :
    Env.Ordered E →
    ε[ν; γ] ⊨ α ≡ α : .sort l₁ →
    ε[ν; γ] ⊨ r ≡ r : Quot.relType α →
    ε[ν; γ] ⊨ β ≡ β : .sort l₂ →
    ε[ν; γ] ⊨ f ≡ f : .forallE α β.wk →
    ε[ν; γ] ⊨ h ≡ h : Quot.compatType (E.get η).eqHead l₂ α r β f →
    ε[ν; γ] ⊨ a ≡ a : α →
    ε[ν; γ] ⊨ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) ≡
      .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) : β →
    ε[ν; γ] ⊨ .app f a ≡ .app f a : β →
    ε[ν; γ] ⊨ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) ≡ .app f a : β
  iota {n : Nat} {γ : Slots n} {ι} {η : Head ζ (.inductive ι)} {ls l ps ms mins s c fds recFds} :
    Env.Ordered E →
    (E.get η).block.RecAllowed l →
    (∀ p, ε[ν; γ] ⊨ ps p ≡ ps p : (E.get η).block.paramType ls ps p) →
    (∀ s, ε[ν; γ] ⊨ ms s ≡ ms s : (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, ε[ν; γ] ⊨ mins s c ≡ mins s c : (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, ε[ν; γ] ⊨ fds f ≡ fds f : (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps fun previous : Fin f.val => fds (previous.castLE f.isLt.le))) →
    (∀ f, ε[ν; γ] ⊨ recFds f ≡ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps (Fin.append ps fds)) →
    ε[ν; γ] ⊨ (E.get η).block.iotaLhs η ls l ps ms mins s c fds recFds ≡
      (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
      (E.get η).block.iotaType η ls ps ms s c fds recFds
  delta {n : Nat} {γ : Slots n} {nlevels} {η : Head ζ (.const .def nlevels)} {ls} :
    Env.Ordered E →
    ε[ν; γ] ⊨ .const η ls ≡ ((E.get η).defValue.instL ls).wkClosed :
      ((E.get η).constType.instL ls).wkClosed
  etaStruct {n : Nat} {γ : Slots n} {ι} {η : Head ζ (.inductive ι)}
      {s c ls ps is maj} (h : (E.get η).block.IsStructure s c) :
    Env.Ordered E →
    (∀ p, ε[ν; γ] ⊨ ps p ≡ ps p : (E.get η).block.paramType ls ps p) →
    ε[ν; γ] ⊨ maj ≡ maj : .ind η s ls ps is →
    ε[ν; γ] ⊨ h.rebuildTerm η ls ps maj ≡ maj : .ind η s ls ps is

theorem soundness (hdecl : SemDecls E ε ν) (hrule : SemDeclRules E ε ν)
    (ho : Env.Ordered E) :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    ∀ γ, ε[ν] ⊨ γ : Γ → ε[ν; γ] ⊨ e₁ ≡ e₂ : t := by
  intro h γ hρ
  induction h with
  | @var n Γ v => exact ⟨rfl, hρ v⟩
  | symm _ ih => exact (ih γ hρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ γ hρ).trans (ih₂ γ hρ)
  | @sortDF n Γ l =>
    refine ⟨rfl, ?_⟩
    simpa! using sort_mem_succ (l.eval ν)
  | defeqDF _ _ iht ihe =>
    have ht := iht γ hρ
    have he := ihe γ hρ
    exact ⟨he.eq, ht.eq ▸ he.mem⟩
  | proofIrrel _ _ _ ihp ih₁ ih₂ =>
    have hp := ihp γ hρ
    have h₁ := ih₁ γ hρ
    have h₂ := ih₂ γ hρ
    exact ⟨eq_of_mem_truth hp.mem h₁.mem h₂.mem, h₁.mem⟩
  | @forallEDF n Γ l₁ l₂ body₁ body₂ t₁ t₂ _ _ iht ihbody =>
    have ht := iht γ hρ
    have hbody := fun x hx => ihbody (γ.snoc x) (hρ.snoc hx)
    constructor
    · change Aczel.pi _ _ = Aczel.pi _ _
      rw [← ht.eq]
      exact Aczel.pi_congr fun x hx => (hbody x hx).eq
    · change Aczel.pi _ _ ∈ S_ ((l₁.imax l₂).eval ν)
      rw [Level.eval_imax]
      refine pi_mem_sort_imax ht.mem fun x hx => ?_
      rw [app_map hx]
      exact (hbody x hx).mem
  | @lamDF n Γ l body₁ body₂ bt t₁ t₂ _ _ iht ihbody =>
    have ht := iht γ hρ
    have hbody := fun x hx => ihbody (γ.snoc x) (hρ.snoc hx)
    constructor
    · change Aczel.lam _ _ = Aczel.lam _ _
      rw [← ht.eq]
      exact Aczel.lam_congr fun x hx => (hbody x hx).eq
    · refine Aczel.lam_mem_piMap fun x hx => ?_
      rw [app_map hx]
      exact (hbody x hx).mem
  | @appDF n Γ f₁ f₂ a₁ a₂ t bt _ _ ihf iha =>
    have hf := ihf γ hρ
    have ha := iha γ hρ
    constructor
    · exact congr(Aczel.app $hf.eq $ha.eq)
    · simp
      have h := Aczel.app_mem hf.mem ha.mem
      rwa [app_map ha.mem] at h
  | @beta n Γ e t body bt _ _ ihbody ihe =>
    have he := ihe γ hρ
    have hbody := ihbody (γ.snoc ε[ν; γ]⟦e⟧) (hρ.snoc he.mem)
    have heq : ε[ν; γ]⟦Expr.app (.lam t body) e⟧ =
        ε[ν; γ]⟦body.inst e⟧ := by
      simpa! using Aczel.app_lam he.mem
    refine ⟨heq, ?_⟩
    simpa [heq] using hbody.mem
  | zeta _ _ _ _ _ ihbody =>
    have hbody := ihbody γ hρ
    refine ⟨?_, ?_⟩
    · simp!
    · simpa! using hbody.mem
  | @eta n Γ e t bt _ ihe =>
    have he := ihe γ hρ
    have heq : ε[ν; γ]⟦Expr.lam t (.app e.wk (.var (Fin.last n)))⟧ =
        ε[ν; γ]⟦e⟧ := by
      simpa! using Aczel.lam_app he.mem
    exact ⟨heq, heq ▸ he.mem⟩
  | @constDF n nlevels kind Γ η ls =>
    refine ⟨rfl, ?_⟩
    simpa! using hdecl η ls
  | indDF _ _ ihps ihis =>
    exact hrule.ind ho (fun p => ihps p γ hρ) fun i => ihis i γ hρ
  | ctorDF _ _ _ ihps ihfields ihrecFields =>
    exact hrule.ctor ho (fun p => ihps p γ hρ) (fun f => ihfields f γ hρ)
      fun f => ihrecFields f γ hρ
  | recrDF hallowed _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    exact hrule.recr ho hallowed (fun p => ihps p γ hρ) (fun s => ihms s γ hρ)
      (fun s c => ihmins s c γ hρ) (fun i => ihis i γ hρ) (ihmaj γ hρ)
  | quotDF _ _ ihα ihr => exact hrule.quot ho (ihα γ hρ) (ihr γ hρ)
  | quotMkDF _ _ _ ihα ihr iha =>
    exact hrule.quotMk ho (ihα γ hρ) (ihr γ hρ) (iha γ hρ)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact hrule.quotLift ho (ihα γ hρ) (ihr γ hρ) (ihβ γ hρ) (ihf γ hρ) (ihh γ hρ) (iha γ hρ)
  | quotIndDF _ _ _ _ _ ihα ihr ihβ ihf iha =>
    exact hrule.quotInd ho (ihα γ hρ) (ihr γ hρ) (ihβ γ hρ) (ihf γ hρ) (iha γ hρ)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    exact hrule.quotIota ho (ihα γ hρ) (ihr γ hρ) (ihβ γ hρ) (ihf γ hρ) (ihh γ hρ) (iha γ hρ)
      (ihlhs γ hρ) (ihrhs γ hρ)
  | iota hallowed _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields =>
    exact hrule.iota ho hallowed (fun p => ihps p γ hρ) (fun s => ihms s γ hρ)
      (fun s c => ihmins s c γ hρ) (fun f => ihfields f γ hρ) fun f => ihrecFields f γ hρ
  | etaStruct h _ _ ihps ihmaj =>
    exact hrule.etaStruct h ho (fun p => ihps p γ hρ) (ihmaj γ hρ)
  | delta => exact hrule.delta ho

@[simp] theorem Expr.denote_falseTy {ν : Param 0 → Nat}
    {ε : Atom ζ 0 → ZFSet} {γ : Slots 0} :
    ε[ν; γ]⟦.falseTy⟧ = ∅ :=
  Aczel.pi_truth_id_eq_falsum

theorem con_ordered {E : Env ζ} (ε : Atom ζ 0 → ZFSet.{u}) (ν : Param 0 → Nat)
    (hdecl : SemDecls E ε ν) (hrule : SemDeclRules E ε ν) (ho : Env.Ordered E) : Env.Con E := by
  intro hall
  have ⟨e, he⟩ := hall .falseTy (Expr.falseTy_isType E)
  have hi := soundness hdecl hrule ho he ![] SemCtx.nil
  simpa using hi.mem

end Metalean
