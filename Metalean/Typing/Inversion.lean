/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Context
public import Metalean.Typing.Quot
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.Defeq

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {e t t₁ α r β f a α₂ r₂ β₂ f₂ h₂ a₂ : Expr ζ ℓ n}
  {e' t' : Expr ζ ℓ (n + 1)} {η : Head ζ .quot} {l l₁ l₂ u : Level ℓ}

local macro "rigid " h:Lean.Parser.Tactic.elimTarget : tactic => `(tactic|
  rcases $h with hside | hside <;>
    first
      | (cases hside; done)
      | solve_by_elim [Or.inl, Or.inr])

theorem var_inv {v : Var n} :
    E[Γ] ⊢ .var v : t →
    E[Γ] ⊢ t ≡ Γ.get v typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n} {v : Var n},
      e₁ = .var v ∨ e₂ = .var v →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ t ≡ Γ.get v typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t v he h
  induction h with
  | var => rcases he with he | he <;> cases he <;> exact .ofDefEq ‹_›
  | defeqDF ht _ _ ihe => exact (IsTypeEq.ofDefEq ht).symm.trans (ihe he)
  | _ => rigid he

theorem sort_inv :
    E[Γ] ⊢ .sort l : t →
    E[Γ] ⊢ t ≡ .sort (.succ l) typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n},
      e₁ = .sort l ∨ e₂ = .sort l →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ t ≡ .sort (.succ l) typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t he h
  induction h with
  | sortDF =>
    rcases he with he | he <;> cases he <;> exact .ofDefEq .sortDF
  | defeqDF ht _ _ ihe =>
    exact (IsTypeEq.ofDefEq ht).symm.trans (ihe he)
  | _ => rigid he

theorem forallE_ty_inv :
    E[Γ] ⊢ .forallE t₁ t' : t →
    ∃ l₁ l₂ : Level ℓ,
      E[Γ] ⊢ t₁ : .sort l₁ ∧
      E[Γ.snoc t₁] ⊢ t' : .sort l₂ ∧
      E[Γ] ⊢ t ≡ .sort (.imax l₁ l₂) typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t t₁ : Expr ζ ℓ n}
      {t' : Expr ζ ℓ (n + 1)},
      e₁ = .forallE t₁ t' ∨ e₂ = .forallE t₁ t' →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ l₁ l₂ : Level ℓ,
        E[Γ] ⊢ t₁ : .sort l₁ ∧
        E[Γ.snoc t₁] ⊢ t' : .sort l₂ ∧
        E[Γ] ⊢ t ≡ .sort (.imax l₁ l₂) typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t t₁ t' he h
  induction h with
  | forallEDF ht ht' ht₂' =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, ht.left, ht'.left, .ofDefEq sortDF⟩
    · exact ⟨_, _, ht.right, ht₂'.right, .ofDefEq sortDF⟩
  | defeqDF ht _ _ ihe =>
    have ⟨l₁, l₂, hdom, hcod, hres⟩ := ihe he
    exact ⟨l₁, l₂, hdom, hcod, (IsTypeEq.ofDefEq ht).symm.trans hres⟩
  | _ => rigid he

theorem const_inv {kind nlevels}
    {η : Head ζ (.const kind nlevels)}
    {ls : Fin nlevels → Level ℓ}
    :
    E[Γ] ⊢ .const η ls : t →
    E[Γ] ⊢ t ≡ ((E.get η).constType.instL ls).wkClosed typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n},
      e₁ = .const η ls ∨ e₂ = .const η ls →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ t ≡ ((E.get η).constType.instL ls).wkClosed typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t he h
  induction h with
  | delta htype _ _ ih =>
    rcases he with he | he
    · cases he
      exact .ofDefEq htype
    · exact ih (Or.inl he)
  | constDF htype =>
    rcases he with he | he <;> cases he
    · exact .ofDefEq htype.left
    · exact .ofDefEq htype
  | defeqDF ht _ _ ihe =>
    exact (IsTypeEq.ofDefEq ht).symm.trans (ihe he)
  | _ => rigid he

section Inductive

variable {ι : IndSig} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {ls : Fin ι.nlevels → Level ℓ}
  {ps₂ : Fin ι.nparams → Expr ζ ℓ n}
  {is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}
  {fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
  {recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
  {ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
  {mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
  {maj₂ : Expr ζ ℓ n}

theorem ctor_inv :
    E[Γ] ⊢ .ctor η s c ls ps₂ fds₂ recFds₂ : t →
    ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
      (fds₁ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
      (recFds₁ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n),
      (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
        (E.get η).block.paramType ls ps₁ p) ∧
      (∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
        (((((E.get η).block.ctors s c).ordinary f).type).instL
          ls).subst
          (Fin.append ps₁ fun previous : Fin f.val =>
            fds₁ (previous.castLE f.isLt.le))) ∧
      (∀ f, E[Γ] ⊢ recFds₁ f ≡ recFds₂ f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType
          η ls ps₁
          (Fin.append ps₁ fds₁)) ∧
      E[Γ] ⊢ .ind η s ls ps₁
          (fun i => ((E.get η).block.ctors s c).targetIndex
            ls ps₁ fds₁ i) ≡
        .ind η s ls ps₂
          (fun i => ((E.get η).block.ctors s c).targetIndex
            ls ps₂ fds₂ i) :
          .sort ((E.get η).block.level.inst ls) ∧
      E[Γ] ⊢ t ≡ .ind η s ls ps₁
        (fun i => ((E.get η).block.ctors s c).targetIndex
          ls ps₁ fds₁ i) typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}
      {ps₂ : Fin ι.nparams → Expr ζ ℓ n}
      {fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
      {recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n},
      e₁ = .ctor η s c ls ps₂ fds₂ recFds₂ ∨ e₂ = .ctor η s c ls ps₂ fds₂ recFds₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
        (fds₁ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
        (recFds₁ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n),
        (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
          (E.get η).block.paramType ls ps₁ p) ∧
        (∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
          (((((E.get η).block.ctors s c).ordinary f).type).instL
            ls).subst
            (Fin.append ps₁ fun previous : Fin f.val =>
              fds₁ (previous.castLE f.isLt.le))) ∧
        (∀ f, E[Γ] ⊢ recFds₁ f ≡ recFds₂ f :
          (((E.get η).block.ctors s c).recursive f).instantiatedType
            η ls ps₁
            (Fin.append ps₁ fds₁)) ∧
        E[Γ] ⊢ .ind η s ls ps₁
            (fun i => ((E.get η).block.ctors s c).targetIndex
              ls ps₁ fds₁ i) ≡
          .ind η s ls ps₂
            (fun i => ((E.get η).block.ctors s c).targetIndex
              ls ps₂ fds₂ i) :
            .sort ((E.get η).block.level.inst ls) ∧
        E[Γ] ⊢ t ≡ .ind η s ls ps₁
          (fun i => ((E.get η).block.ctors s c).targetIndex
            ls ps₁ fds₁ i) typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t ps₂ fds₂ recFds₂ he h
  induction h with
  | ctorDF hps hfields hrecFields _ _ htype =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, _,
        fun p => (hps p).left,
        fun f => (hfields f).left,
        fun f => (hrecFields f).left,
        htype.left, .ofDefEq htype.left⟩
    · exact ⟨_, _, _, hps, hfields, hrecFields,
        htype, .ofDefEq htype.left⟩
  | defeqDF ht _ _ ih =>
    have ⟨ps₁, fds₁, recFds₁, hps,
      hfields, hrecFields, hresult, hT⟩ := ih he
    exact ⟨ps₁, fds₁, recFds₁, hps,
      hfields, hrecFields, hresult, (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | _ => rigid he

theorem recr_inv :
    E[Γ] ⊢ .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ : t →
    ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
      (ms₁ : Fin ι.nsorts → Expr ζ ℓ n)
      (mins₁ : (s : Fin ι.nsorts) →
        Fin (ι.nctors s) → Expr ζ ℓ n)
      (is₁ : Fin (ι.nindices s) → Expr ζ ℓ n)
      (maj₁ : Expr ζ ℓ n),
      (E.get η).block.RecAllowed l ∧
      (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
        (E.get η).block.paramType ls ps₁ p) ∧
      (∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s :
        (E.get η).block.motiveType η ls ps₁ l s) ∧
      (∀ s c,
        E[Γ] ⊢ mins₁ s c ≡ mins₂ s c :
          (E.get η).block.caseFnType η ls ps₁ ms₁ s c) ∧
      (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i :
        (E.get η).block.indexType ls s ps₁ is₁ i) ∧
      E[Γ] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ ∧
      E[Γ] ⊢ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
        Inductive.motiveResult (ms₂ s) is₂ maj₂ : .sort l ∧
      E[Γ] ⊢ t ≡
        Inductive.motiveResult (ms₁ s) is₁ maj₁ typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}
      {ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
      {mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
      {is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} {maj₂ : Expr ζ ℓ n},
      e₁ = .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ ∨ e₂ = .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
        (ms₁ : Fin ι.nsorts → Expr ζ ℓ n)
        (mins₁ : (s : Fin ι.nsorts) →
          Fin (ι.nctors s) → Expr ζ ℓ n)
        (is₁ : Fin (ι.nindices s) → Expr ζ ℓ n)
        (maj₁ : Expr ζ ℓ n),
        (E.get η).block.RecAllowed l ∧
        (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
          (E.get η).block.paramType ls ps₁ p) ∧
        (∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s :
          (E.get η).block.motiveType η ls ps₁ l s) ∧
        (∀ s c,
          E[Γ] ⊢ mins₁ s c ≡ mins₂ s c :
            (E.get η).block.caseFnType η ls ps₁ ms₁ s c) ∧
        (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i :
          (E.get η).block.indexType ls s ps₁ is₁ i) ∧
        E[Γ] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ ∧
        E[Γ] ⊢ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
          Inductive.motiveResult (ms₂ s) is₂ maj₂ : .sort l ∧
        E[Γ] ⊢ t ≡
          Inductive.motiveResult (ms₁ s) is₁ maj₁ typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t ps₂ ms₂ mins₂ is₂ maj₂ he h
  induction h with
  | recrDF hallowed hps hms hmins his hmaj hresult =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, _, _, _, hallowed,
        fun p => (hps p).left,
        fun s => (hms s).left,
        fun s c => (hmins s c).left,
        fun i => (his i).left,
        hmaj.left, hresult.left,
        .ofDefEq hresult.left⟩
    · exact ⟨_, _, _, _, _, hallowed, hps, hms,
        hmins, his, hmaj, hresult, .ofDefEq hresult.left⟩
  | defeqDF ht _ _ ih =>
    have ⟨ps₁, ms₁, mins₁, is₁, maj₁,
      hallowed, hps, hms, hmins, his, hmaj,
      hresult, hT⟩ := ih he
    exact ⟨ps₁, ms₁, mins₁, is₁, maj₁,
      hallowed, hps, hms, hmins, his, hmaj,
      hresult, (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | _ => rigid he

theorem ind_inv :
    E[Γ] ⊢ .ind η s ls ps₂ is₂ : t →
    ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
      (is₁ : Fin (ι.nindices s) → Expr ζ ℓ n),
      (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
        (E.get η).block.paramType ls ps₁ p) ∧
      (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i :
        (E.get η).block.indexType ls s ps₁ is₁ i) ∧
      E[Γ] ⊢ t ≡ .sort ((E.get η).block.level.inst ls) typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}
      {ps₂ : Fin ι.nparams → Expr ζ ℓ n} {is₂ : Fin (ι.nindices s) → Expr ζ ℓ n},
      e₁ = .ind η s ls ps₂ is₂ ∨ e₂ = .ind η s ls ps₂ is₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ (ps₁ : Fin ι.nparams → Expr ζ ℓ n)
        (is₁ : Fin (ι.nindices s) → Expr ζ ℓ n),
        (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
          (E.get η).block.paramType ls ps₁ p) ∧
        (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i :
          (E.get η).block.indexType ls s ps₁ is₁ i) ∧
        E[Γ] ⊢ t ≡ .sort ((E.get η).block.level.inst ls) typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t ps₂ is₂ he h
  induction h with
  | indDF hps his =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _,
        fun p => (hps p).left,
        fun i => (his i).left,
        .ofDefEq .sortDF⟩
    · exact ⟨_, _, hps, his, .ofDefEq .sortDF⟩
  | defeqDF ht _ _ ih =>
    have ⟨ps₁, is₁, hps, his, hT⟩ := ih he
    exact ⟨ps₁, is₁, hps, his,
      (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | _ => rigid he

end Inductive

theorem quot_inv :
    E[Γ] ⊢ .quot η l α r : t →
    E[Γ] ⊢ t ≡ .sort l typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t α r : Expr ζ ℓ n},
      e₁ = .quot η l α r ∨ e₂ = .quot η l α r →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ t ≡ .sort l typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t α r he h
  induction h with
  | quotDF =>
    rcases he with he | he <;> cases he <;> exact .ofDefEq .sortDF
  | defeqDF ht _ _ ih =>
    exact (IsTypeEq.ofDefEq ht).symm.trans (ih he)
  | _ => rigid he

theorem quotInd_prem :
    E[Γ] ⊢ .quotInd η l α₂ r₂ β₂ f₂ a₂ : t →
    ∃ α₁ r₁ β₁ f₁ a₁ : Expr ζ ℓ n,
      E[Γ] ⊢ α₁ ≡ α₂ : .sort l ∧
      E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
      E[Γ] ⊢ β₁ ≡ β₂ : Quot.motiveType η l α₁ r₁ ∧
      E[Γ] ⊢ f₁ ≡ f₂ : Quot.minorType η l α₁ r₁ β₁ ∧
      E[Γ] ⊢ a₁ ≡ a₂ : .quot η l α₁ r₁ ∧
      E[Γ] ⊢ .app β₁ a₁ ≡ .app β₂ a₂ : .prop ∧
      E[Γ] ⊢ t ≡ .app β₁ a₁ typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}
      {α₂ r₂ β₂ f₂ a₂ : Expr ζ ℓ n},
      e₁ = .quotInd η l α₂ r₂ β₂ f₂ a₂ ∨ e₂ = .quotInd η l α₂ r₂ β₂ f₂ a₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ α₁ r₁ β₁ f₁ a₁ : Expr ζ ℓ n,
        E[Γ] ⊢ α₁ ≡ α₂ : .sort l ∧
        E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
        E[Γ] ⊢ β₁ ≡ β₂ : Quot.motiveType η l α₁ r₁ ∧
        E[Γ] ⊢ f₁ ≡ f₂ : Quot.minorType η l α₁ r₁ β₁ ∧
        E[Γ] ⊢ a₁ ≡ a₂ : .quot η l α₁ r₁ ∧
        E[Γ] ⊢ .app β₁ a₁ ≡ .app β₂ a₂ : .prop ∧
        E[Γ] ⊢ t ≡ .app β₁ a₁ typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t α₂ r₂ β₂ f₂ a₂ he h
  induction h with
  | quotIndDF hα hr hβ he ha hresult =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, _, _, _,
        hα.left, hr.left, hβ.left,
        he.left, ha.left, hresult.left,
        .ofDefEq hresult.left⟩
    · exact ⟨_, _, _, _, _, hα, hr, hβ, he, ha, hresult,
        .ofDefEq hresult.left⟩
  | defeqDF ht _ _ ih =>
    have ⟨α₁, r₁, β₁, f₁, a₁, hα, hr, hβ, he, ha, hresult, hT⟩ := ih he
    exact ⟨α₁, r₁, β₁, f₁, a₁, hα, hr, hβ, he, ha, hresult,
      (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | _ => rigid he

theorem quotMk_prem :
    E[Γ] ⊢ .quotMk η l α₂ r₂ a₂ : t →
    ∃ α₁ r₁ a₁ : Expr ζ ℓ n,
      E[Γ] ⊢ α₁ ≡ α₂ : .sort l ∧
      E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
      E[Γ] ⊢ a₁ ≡ a₂ : α₁ ∧
      E[Γ] ⊢ t ≡ .quot η l α₁ r₁ typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t α₂ r₂ a₂ : Expr ζ ℓ n},
      e₁ = .quotMk η l α₂ r₂ a₂ ∨ e₂ = .quotMk η l α₂ r₂ a₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ α₁ r₁ a₁ : Expr ζ ℓ n,
        E[Γ] ⊢ α₁ ≡ α₂ : .sort l ∧
        E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
        E[Γ] ⊢ a₁ ≡ a₂ : α₁ ∧
        E[Γ] ⊢ t ≡ .quot η l α₁ r₁ typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t α₂ r₂ a₂ he h
  induction h with
  | quotMkDF hα hr ha =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, _, hα.left, hr.left,
        ha.left,
        .ofDefEq (.quotDF hα.left hr.left)⟩
    · exact ⟨_, _, _, hα, hr, ha,
        .ofDefEq (.quotDF hα.left hr.left)⟩
  | defeqDF ht _ _ ih =>
    have ⟨α₁, r₁, a₁, hα, hr, ha, hT⟩ := ih he
    exact ⟨α₁, r₁, a₁, hα, hr, ha,
      (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | _ => rigid he

theorem quotLift_prem :
    E[Γ] ⊢ .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ : t →
    ∃ α₁ r₁ β₁ f₁ h₁ a₁ : Expr ζ ℓ n,
      E[Γ] ⊢ α₁ ≡ α₂ : .sort l₁ ∧
      E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
      E[Γ] ⊢ β₁ ≡ β₂ : .sort l₂ ∧
      E[Γ] ⊢ f₁ ≡ f₂ : .forallE α₁ β₁.wk ∧
      E[Γ] ⊢ h₁ ≡ h₂ :
        Quot.compatType (E.get η).eqHead l₂ α₁ r₁ β₁ f₁ ∧
      E[Γ] ⊢ a₁ ≡ a₂ : .quot η l₁ α₁ r₁ ∧
      E[Γ] ⊢ t ≡ β₁ typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}
      {α₂ r₂ β₂ f₂ h₂ a₂ : Expr ζ ℓ n},
      e₁ = .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ ∨
        e₂ = .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ α₁ r₁ β₁ f₁ h₁ a₁ : Expr ζ ℓ n,
        E[Γ] ⊢ α₁ ≡ α₂ : .sort l₁ ∧
        E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁ ∧
        E[Γ] ⊢ β₁ ≡ β₂ : .sort l₂ ∧
        E[Γ] ⊢ f₁ ≡ f₂ : .forallE α₁ β₁.wk ∧
        E[Γ] ⊢ h₁ ≡ h₂ :
          Quot.compatType (E.get η).eqHead l₂ α₁ r₁ β₁ f₁ ∧
        E[Γ] ⊢ a₁ ≡ a₂ : .quot η l₁ α₁ r₁ ∧
        E[Γ] ⊢ t ≡ β₁ typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t α₂ r₂ β₂ f₂ h₂ a₂ he hd
  induction hd with
  | quotLiftDF hα hr hβ he hcompatType hcompat ha =>
    rcases he with he | he <;> cases he
    · exact ⟨_, _, _, _, _, _,
        hα.left, hr.left, hβ.left,
        he.left, hcompatType.left,
        hcompat.left,
        .ofDefEq hβ.left⟩
    · exact ⟨_, _, _, _, _, _, hα, hr, hβ, he,
        hcompatType, hcompat, .ofDefEq hβ.left⟩
  | defeqDF ht _ _ ih =>
    have ⟨α₁, r₁, β₁, f₁, h₁, a₁, hα,
      hr, hβ, he, hcompat, ha, hT⟩ := ih he
    exact ⟨α₁, r₁, β₁, f₁, h₁, a₁, hα,
      hr, hβ, he, hcompat, ha,
      (IsTypeEq.ofDefEq ht).symm.trans hT⟩
  | quotIota hα hr hβ he hcompat ha _ _ _ _ _ _ _ _ _ ih =>
    rcases he with he | he
    · cases he
      exact ⟨_, _, _, _, _, _,
        hα.left, hr.left, hβ.left,
        he.left, hcompat.left,
        .quotMkDF hα.left hr.left
          ha.left,
        .ofDefEq hβ.left⟩
    · exact ih (Or.inl he)
  | _ => rigid he

theorem quotMk_inv :
    E[Γ] ⊢ .quotMk η l α r a : t →
    E[Γ] ⊢ t ≡ .quot η l α r typ := by
  intro h
  have ⟨_, _, _, hα, hr, _, hres⟩ := h.quotMk_prem
  exact hres.trans (.ofDefEq (.quotDF hα hr))

theorem quotLift_inv {h : Expr ζ ℓ n} :
    E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h a : t →
    E[Γ] ⊢ t ≡ β typ := by
  intro hd
  have ⟨_, _, _, _, _, _, _, _, hβ, _, _, _, hres⟩ :=
    hd.quotLift_prem
  exact hres.trans (.ofDefEq hβ)

theorem forallE_inv :
    E[Γ] ⊢ .forallE t₁ t' : t →
    E[Γ] ⊢ t₁ typ ∧ E[Γ.snoc t₁] ⊢ t' typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t t₁ : Expr ζ ℓ n}
      {t' : Expr ζ ℓ (n + 1)},
      e₁ = .forallE t₁ t' ∨ e₂ = .forallE t₁ t' →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ t₁ typ ∧ E[Γ.snoc t₁] ⊢ t' typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t t₁ t' he h
  induction h with
  | forallEDF ht₁ ht' ht₂' =>
    rcases he with he | he <;> cases he
    · exact ⟨⟨_, ht₁.left⟩, ⟨_, ht'.left⟩⟩
    · exact ⟨⟨_, ht₁.right⟩, ⟨_, ht₂'.right⟩⟩
  | _ => rigid he

theorem quot_formation_inv :
    E[Γ] ⊢ .quot η u α r : t →
    E[Γ] ⊢ α : .sort u ∧ E[Γ] ⊢ r : Quot.relType α := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t α r : Expr ζ ℓ n},
      e₁ = .quot η u α r ∨ e₂ = .quot η u α r →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ α : .sort u ∧ E[Γ] ⊢ r : Quot.relType α from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t α r he h
  induction h with
  | quotDF hα hr =>
    rcases he with he | he <;> cases he
    · exact ⟨hα.left, hr.left⟩
    · exact ⟨hα.right,
        .defeqDF (Quot.relType_congr hα) hr.right⟩
  | _ => rigid he

theorem app_inv :
    E[Γ] ⊢ .app f e : t →
    ∃ (t₁ : Expr ζ ℓ n) (t' : Expr ζ ℓ (n + 1)),
    E[Γ] ⊢ f : .forallE t₁ t' ∧
    E[Γ] ⊢ e : t₁ ∧
    E[Γ] ⊢ t ≡ t'.inst e typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t f e : Expr ζ ℓ n},
      e₁ = .app f e ∨ e₂ = .app f e →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      ∃ (t₁ : Expr ζ ℓ n) (t' : Expr ζ ℓ (n + 1)),
      E[Γ] ⊢ f : .forallE t₁ t' ∧
      E[Γ] ⊢ e : t₁ ∧
      E[Γ] ⊢ t ≡ t'.inst e typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t f e hd h
  induction h with
  | etaStruct _ _ _ _ _ ih _ =>
    rcases hd with hd | hd
    · simp [Inductive.IsStructure.rebuildTerm] at hd
    · exact ih (Or.inl hd)
  | appDF ht₁ ht' hf he hres =>
    rcases hd with hd | hd <;> cases hd
    · exact ⟨_, _, hf.left, he.left,
        .ofDefEq hres.left⟩
    · exact ⟨_, _, hf.right, he.right,
        .ofDefEq hres⟩
  | defeqDF ht _ _ ih =>
    obtain ⟨t₁, t', hf, he, hinst⟩ := ih hd
    exact ⟨t₁, t', hf, he, (IsTypeEq.ofDefEq ht).symm.trans hinst⟩
  | beta ht₁ ht' hbody he hres _ _ _ _ _ _ ihresult =>
    rcases hd with hd | hd
    · cases hd
      exact ⟨_, _, .lamDF ht₁ ht' ht' hbody hbody, he, .ofDefEq hres⟩
    · exact ihresult (Or.inl hd)
  | _ => rigid hd

theorem letE_inv {v : Expr ζ ℓ n} :
    E[Γ] ⊢ .letE t₁ v e' : t →
    E[Γ] ⊢ ok →
    ∃ r : Expr ζ ℓ n,
    E[Γ] ⊢ t₁ typ ∧
    E[Γ] ⊢ v : t₁ ∧
    E[Γ] ⊢ e'.inst v : r ∧
    E[Γ] ⊢ t ≡ r typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t t₁ v : Expr ζ ℓ n}
      {e' : Expr ζ ℓ (n + 1)},
      e₁ = .letE t₁ v e' ∨ e₂ = .letE t₁ v e' →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ ok →
      ∃ r : Expr ζ ℓ n,
      E[Γ] ⊢ t₁ typ ∧
      E[Γ] ⊢ v : t₁ ∧
      E[Γ] ⊢ e'.inst v : r ∧
      E[Γ] ⊢ t ≡ r typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t t₁ v e' he h hΓ
  induction h with
  | defeqDF ht _ _ ih =>
    have ⟨t', ht₁, hv, he', hinst⟩ := ih he hΓ
    exact ⟨t', ht₁, hv, he', (IsTypeEq.ofDefEq ht).symm.trans hinst⟩
  | zeta ht hv htype hbody _ _ _ ihresult =>
    rcases he with he | he
    · cases he
      exact ⟨_, ⟨_, ht⟩, hv, hbody, .ofDefEq htype⟩
    · exact ihresult (Or.inl he) hΓ
  | etaStruct _ _ _ _ _ ih _ =>
    rcases he with he | he
    · simp [Inductive.IsStructure.rebuildTerm] at he
    · exact ih (Or.inl he) hΓ
  | _ => rigid he

theorem lam_inv :
    E[Γ] ⊢ .lam t₁ e' : t →
    E[Γ] ⊢ ok →
    ∃ t' : Expr ζ ℓ (n + 1),
    E[Γ.snoc t₁] ⊢ e' : t' ∧
    E[Γ] ⊢ t ≡ .forallE t₁ t' typ := by
  suffices hgen : ∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t t₁ : Expr ζ ℓ n}
      {e' : Expr ζ ℓ (n + 1)},
      e₁ = .lam t₁ e' ∨ e₂ = .lam t₁ e' →
      E[Γ] ⊢ e₁ ≡ e₂ : t →
      E[Γ] ⊢ ok →
      ∃ t' : Expr ζ ℓ (n + 1),
      E[Γ.snoc t₁] ⊢ e' : t' ∧
      E[Γ] ⊢ t ≡ .forallE t₁ t' typ from
    hgen (Or.inl rfl)
  intro n Γ e₁ e₂ t t₁ e' he h hΓ
  induction h with
  | var | sortDF | constDF | indDF | ctorDF | recrDF | appDF | forallEDF
  | quotDF | quotMkDF | quotLiftDF | quotIndDF | quotIota | delta =>
    simp_all
  | etaStruct _ _ _ _ _ ih _ =>
    rcases he with he | he
    · simp [Inductive.IsStructure.rebuildTerm] at he
    · exact ih (Or.inl he) hΓ
  | symm _ ih => exact ih he.symm hΓ
  | lamDF ht₁ ht' ht₂' he' hbody' =>
    rcases he with he | he <;> cases he
    · exact ⟨_, he'.left,
        .ofDefEq (.forallEDF ht₁.left
          ht'.left ht'.left)⟩
    · exact ⟨_, hbody'.right,
        .ofDefEq (.forallEDF ht₁
          ht'.left ht₂'.left)⟩
  | defeqDF ht _ _ ih =>
    obtain ⟨t', he', hinst⟩ := ih he hΓ
    exact ⟨t', he', (IsTypeEq.ofDefEq ht).symm.trans hinst⟩
  | beta => simp_all
  | zeta => simp_all
  | @eta n Γ u v e t₁ t' ht₁ ht' htw hew hee iht₁ iht' ihtw ihew ih =>
    rcases he with he | he
    · cases he
      have hΓt : E[Γ.snoc t₁] ⊢ ok := hΓ.snoc ⟨u, ht₁⟩
      have hvar : E[Γ.snoc t₁] ⊢ .var (Fin.last n) : t₁.wk := by
        have hvar := hΓt.var (Fin.last n)
        rwa [Ctx.get_last] at hvar
      have htwk' : E[(Γ.snoc t₁).snoc t₁.wk] ⊢ t'.wkFrom n : .sort v :=
        ht'.wkFrom Γ #t[t₁] t₁
      have he' : E[Γ.snoc t₁] ⊢ .app e.wk (.var (Fin.last n)) : t' := by
        have he' := appDF htw htwk' hew hvar
          (by rw [Expr.inst_wkFrom_last]; exact ht')
        rwa [Expr.inst_wkFrom_last] at he'
      exact ⟨t', he', .ofDefEq (forallEDF ht₁ ht' ht')⟩
    · exact ih (Or.inl he) hΓ
  | trans | proofIrrel | iota => rigid he

end Metalean.Defeq
