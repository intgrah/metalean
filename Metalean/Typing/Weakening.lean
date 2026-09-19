/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Defeq
public import Metalean.Syntax.Weakening
import Metalean.Syntax.Structure.Projection
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs}
  {ℓ n cutPos d a b k p nsorts nparams nfields : Nat}
  {ι : IndSig} {s : Fin ι.nsorts}
  {csig : CtorSig ι.nsorts}
  (I : Inductive ζ ι) (ctor : Ctor ζ ι s csig)
  {arity : Nat} {target : Fin ι.nsorts}
  (fd : RecField ζ ι nfields arity target)
  (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
  (ps : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
  (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n)

namespace Quot

@[simp] theorem relType_wkFrom (α : Expr ζ ℓ n) :
    (relType α).wkFrom cutPos = relType (α.wkFrom cutPos) := by
  simp [Expr.wkFrom_eq_subst]

end Quot

namespace Inductive

@[simp] theorem paramType_wkFrom (f : Fin ι.nparams) :
    (I.paramType ls ps f).wkFrom cutPos =
      I.paramType ls (fun i => (ps i).wkFrom cutPos) f := by
  simp [Expr.wkFrom_eq_subst]

@[simp] theorem paramType_wkN (f : Fin ι.nparams) (k : Nat) :
    (I.paramType ls ps f).wkN k =
      I.paramType ls (fun i => (ps i).wkN k) f := by
  simp [Expr.wkN_eq_subst]

@[simp] theorem motiveType_wkN (l : Level ℓ) (s : Fin ι.nsorts) (k : Nat) :
    (I.motiveType η ls ps l s).wkN k =
      I.motiveType η ls (fun i => (ps i).wkN k) l s := by
  simp [Expr.wkN_eq_subst]

@[simp] theorem caseFnType_wkN (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (k : Nat) :
    (I.caseFnType η ls ps ms s c).wkN k =
      I.caseFnType η ls (fun i => (ps i).wkN k)
        (fun s => (ms s).wkN k) s c := by
  simp [Expr.wkN_eq_subst]

end Inductive

namespace RecField

@[simp] theorem instantiatedType_wkN (σ : Subst ζ ℓ (ι.nparams + nfields) n) (k : Nat) :
    (fd.instantiatedType η ls ps σ).wkN k =
      fd.instantiatedType η ls (fun p => (ps p).wkN k)
        fun v => (σ v).wkN k := by
  simp only [Expr.wkN_eq_subst, instantiatedType_subst]

end RecField

namespace Ctor

@[simp] theorem ordinaryFieldType_wkN (f : Fin csig.nfields)
    (previous : Fin f.val → Expr ζ ℓ n) (k : Nat) :
    (((ctor.ordinaryType f).instL ls).subst (Fin.append ps previous)).wkN k =
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append (fun i => (ps i).wkN k) fun i => (previous i).wkN k) := by
  simp [Expr.wkN_eq_subst]

end Ctor

namespace Defeq

private theorem substRenames {E : Env ζ} {m : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}
    {σ : Subst ζ ℓ n m} {e₁ e₂ t : Expr ζ ℓ n} (hσ : Subst.Renames Γ₁ Γ₂ σ) :
    E[Γ₁] ⊢ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ e₁.subst σ ≡ e₂.subst σ : t.subst σ := by
  intro d
  induction d generalizing m Γ₂ with
  | @var _ _ v =>
    have ⟨w, hw, htype⟩ := hσ v
    change E[Γ₂] ⊢ σ v ≡ σ v : _
    rw [hw, ← htype]
    exact .var
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hσ) (ih₂ hσ)
  | sortDF => exact .sortDF
  | constDF => simpa using .constDF
  | indDF _ _ ihps ihis =>
    simpa! using Defeq.indDF
      (fun p => by simpa using ihps p hσ)
      (fun i => by simpa using ihis i hσ)
  | ctorDF _ _ _ ihps ihfields ihrecFields =>
    simpa! using Defeq.ctorDF
      (fun p => by simpa using ihps p hσ)
      (fun f => by simpa using ihfields f hσ)
      (fun f => by simpa using ihrecFields f hσ)
  | recrDF hallowed _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [Inductive.motiveResult_subst]
    exact .recrDF hallowed
      (fun p => by simpa using ihps p hσ)
      (fun s => by simpa using ihms s hσ)
      (fun s c => by simpa using ihmins s c hσ)
      (fun i => by simpa using ihis i hσ)
      (ihmaj hσ)
  | appDF _ _ ihf iha =>
    rw [Expr.inst_subst]
    exact .appDF (ihf hσ) (iha hσ)
  | lamDF _ _ iht ihbody => exact .lamDF (iht hσ) (ihbody hσ.lift)
  | forallEDF _ _ iht ihbody => exact .forallEDF (iht hσ) (ihbody hσ.lift)
  | defeqDF _ _ ih₁ ih₂ => exact .defeqDF (ih₁ hσ) (ih₂ hσ)
  | beta _ _ ihbody iha =>
    rw [Expr.inst_subst, Expr.inst_subst]
    exact .beta (ihbody hσ.lift) (iha hσ)
  | zeta _ _ _ iht ihv ihbody =>
    simpa! [Expr.inst_subst] using Defeq.zeta
      (iht hσ) (ihv hσ)
      (by simpa [Expr.inst_subst] using ihbody hσ)
  | eta _ ih =>
    simpa! [Expr.wk_subst_lift] using Defeq.eta (ih hσ)
  | etaStruct h _ _ ihps ihmaj =>
    simpa! using Defeq.etaStruct h
      (fun p => by simpa using ihps p hσ)
      (by simpa! using ihmaj hσ)
  | proofIrrel _ _ _ ihp ih ih' =>
    exact .proofIrrel (ihp hσ) (ih hσ) (ih' hσ)
  | iota hallowed _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields =>
    rw [Inductive.iotaLhs_subst, Inductive.iotaRhs_subst, Inductive.iotaType_subst]
    exact .iota hallowed
      (fun p => by simpa using ihps p hσ)
      (fun s => by simpa using ihms s hσ)
      (fun s c => by simpa using ihmins s c hσ)
      (fun f => by simpa using ihfields f hσ)
      (fun f => by simpa using ihrecFields f hσ)
  | quotDF _ _ ihα ihr =>
    exact .quotDF
      (ihα hσ)
      (by simpa using ihr hσ)
  | quotMkDF _ _ _ ihα ihr iha =>
    exact .quotMkDF
      (ihα hσ)
      (by simpa using ihr hσ)
      (iha hσ)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact .quotLiftDF
      (ihα hσ)
      (by simpa using ihr hσ) (ihβ hσ)
      (by simpa [Expr.wk_subst_lift] using ihf hσ)
      (by simpa using ihh hσ) (iha hσ)
  | quotIndDF _ _ _ _ _ ihα ihr ihβ ihf iha =>
    exact .quotIndDF
      (ihα hσ)
      (by simpa using ihr hσ)
      (by simpa using ihβ hσ)
      (by simpa using ihf hσ)
      (iha hσ)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    simpa! using Defeq.quotIota
      (ihα hσ)
      (by simpa using ihr hσ)
      (ihβ hσ)
      (by simpa [Expr.wk_subst_lift] using ihf hσ)
      (by simpa using ihh hσ)
      (iha hσ)
      (ihlhs hσ)
      (ihrhs hσ)
  | delta => simpa using .delta

theorem wkFrom {E : Env ζ} {cut n : Nat} (Γ₀ : Ctx ζ ℓ 0 cut) (Δ : Ctx ζ ℓ cut n)
    (t₁ : Expr ζ ℓ cut) {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ₀ ++ Δ] ⊢ e₁ ≡ e₂ : t →
    E[Γ₀.insert t₁ Δ] ⊢ e₁.wkFrom cut ≡ e₂.wkFrom cut : t.wkFrom cut := by
  intro h
  simpa [Expr.wkFrom_eq_subst] using h.substRenames (Subst.renames_wkFrom Γ₀ t₁ Δ)

theorem wk {E : Env ζ} {Γ : Ctx ζ ℓ 0 n} (t₁ : Expr ζ ℓ n) {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ.snoc t₁] ⊢ e₁.wk ≡ e₂.wk : t.wk :=
  wkFrom Γ #t[] t₁

end Defeq

end Metalean
