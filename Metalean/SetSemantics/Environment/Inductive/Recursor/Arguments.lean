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

structure RecSlots (ι : IndSig) (s : Fin ι.nsorts) : Type (u + 1) where
  params : Slots.{u} ι.nparams
  motives : Slots.{u} ι.nsorts
  cases : (s : Fin ι.nsorts) → Slots.{u} (ι.nctors s)
  indices : Slots.{u} (ι.nindices s)
  major : ZFSet.{u}

namespace RecSlots

variable (γ : RecSlots.{u} ι s)

def prefixValues : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
  Fin.append (Fin.append γ.params γ.motives) fun tag =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    γ.cases s c

def valuation : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  Fin.snoc (Fin.append γ.prefixValues γ.indices) γ.major

instance : CoeFun (RecSlots.{u} ι s)
    (fun _ => Fin (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) → ZFSet.{u}) :=
  ⟨valuation⟩

theorem denote_recrSubst {ℓ n : Nat}
    (ε : Atom ζ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat) (γ : Slots n)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) (maj : Expr ζ ℓ n) :
    (ε[ν; γ]⟦Inductive.recrSubst ps ms mins is maj ·⟧) =
      (mk (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦ms ·⟧) (ε[ν; γ]⟦mins · ·⟧)
        (ε[ν; γ]⟦is ·⟧) ε[ν; γ]⟦maj⟧).valuation := by
  change Expr.denote ε ν γ ∘ Inductive.recrSubst _ _ _ _ _ = _
  rw [Inductive.recrSubst, Fin.comp_snoc]
  simp [Function.comp_def, Fin.append_comp, valuation, prefixValues]

end RecSlots

theorem SemDefeq.recr
    {l : Level 0}
    {tele : SemTele.{u} 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1)}
    {leaf : RecSlots.{u} ι s → ZFSet.{u}}
    (hrealizes : Realizes ε ![] Set.univ ((E.get η).block.recrTele η s ls l) tele)
    (hleaf : ∀ γ : RecSlots ι s, γ.valuation ∈ Reachable Set.univ tele →
      leaf γ ∈ ε[γ]⟦ι.recrBody s⟧)
    (hatom : ∀ vps vms vmins vis vmaj,
      ε (.recr η s ls l vps vms vmins vis vmaj) = leaf (RecSlots.mk vps vms vmins vis vmaj))
    {n : Nat} {γ : Slots n}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ 0 n}
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ 0 n}
    {mins₁ mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ 0 n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ 0 n}
    {maj₁ maj₂ : Expr ζ 0 n} :
    (∀ p, ε[γ] ⊨ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ s, ε[γ] ⊨ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ s c, ε[γ] ⊨ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c) →
    (∀ i, ε[γ] ⊨ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i) →
    ε[γ] ⊨ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁ →
    ε[γ] ⊨ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡ .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁ := by
  intro hps hms hmins his hmaj
  have hreachable := SemDefeq.reachable hrealizes
    (Inductive.forall_recrSubst (motive := fun _ e₁ e₂ t => ε[γ] ⊨ e₁ ≡ e₂ : t)
      hps hms hmins his hmaj)
  have hbody := Expr.denote_subst (ε := ε) (ν := ![]) γ
    (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁) (ι.recrBody s)
  rw [IndSig.recrBody_subst] at hbody
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun s => (hms s).eq,
      funext₂ fun s c => (hmins s c).eq,
      funext fun i => (his i).eq, hmaj.eq]
  · rw [hbody]
    change ε (.recr η s ls l _ _ _ _ _) ∈ _
    rw [hatom]
    rw [RecSlots.denote_recrSubst] at hreachable ⊢
    exact hleaf _ hreachable

end Metalean
