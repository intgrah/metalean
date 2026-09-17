module

public import Metalean.Semantics.Interpretation.Binder.Abstraction
public import Metalean.Semantics.Interpretation.Binder.Pi
public import Metalean.Semantics.Interpretation.Family.Basic
public import Metalean.Semantics.Interpretation.Family.Application
public import Metalean.Semantics.Interpretation.Family.Substitution
public import Metalean.Semantics.Interpretation.Inductive
public import Metalean.Semantics.Interpretation.Quotient.Basic
public import Metalean.Semantics.Interpretation.Recursor.Fixpoint
public import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Semantics.Domain.Decoder.FixedPoint

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} (D : CodeAssignment E ℓ)

set_option linter.unusedVariables false in
noncomputable def rawInterpret (Γ₁ : CtxCat E ℓ) : Expr ζ ℓ Γ₁.as.len → RawFamily Γ₁
  | .var v => RawFamily.lookup v.db
  | .sort l => RawFamily.sort l
  | .const (kind := .def) η ls =>
      rawInterpret Γ₁ ((E.get η).defValue.instL ls).wkClosed
  | .const (kind := .axiom) _ _ => ⊥
  | .const (kind := .opaque) _ _ => ⊥
  | .ind η s ls ps is =>
      ⨆ h : IndTyping Γ₁ η s ls ps is,
        ⨆ _hB : (E.get η).block.WFStrong E,
          RawFamily.ind h.code fun c =>
            RawFamily.closedApps
              (rawInterpret (CtxCat.nil E ℓ) (((E.get η).block.ctorTypeFn s c).instL fun p => ls p))
              (fun p => Tm.label Γ₁.as (h.param p)) fun p => rawInterpret Γ₁ (ps p)
  | .ctor η s c ls ps fds recFds =>
      match Level.rel ((E.get η).block.level.inst ls) with
      | false => ⊥
      | true =>
        ⨆ h : CtorTyping Γ₁ η s c ls ps fds recFds,
          RawFamily.ctor ⟨η, s, c⟩ h.names fun i => rawInterpret Γ₁ (Fin.append fds recFds i)
  | .recr η s ls l ps ms mins is maj =>
      match l.rel with
      | false => ⊥
      | true =>
        ⨆ h : RecTyping Γ₁ η s ls l ps ms mins is maj,
          RawFamily.closedApps (recursorWith D (fun Γ' e _ => rawInterpret Γ' e) h.toRecDecl ls s)
            (fun v => Tm.label Γ₁.as (h.recrSubstWF v))
            fun v => rawInterpret Γ₁ (Inductive.recrSubst ps ms mins is maj v)
  | .quot η u α r => ⨆ h : QuotTyping Γ₁ u α r, RawFamily.quot (h.code η)
  | .quotMk η u α _ a =>
      match u.rel with
      | false => ⊥
      | true => ⨆ ha : E[Γ₁.as.ctx] ⊢ₛ a : α, RawFamily.quotMk η (Tm.label Γ₁.as ha) (rawInterpret Γ₁ a)
  | .quotLift η l₁ l₂ α r β f hr a =>
      match l₁.rel with
      | false =>
        ⨆ h : E[Γ₁.as.ctx] ⊢ₛ Expr.quotLift η l₁ l₂ α r β f hr a : β,
          RawFamily.decode D (Tm.label Γ₁.as h) (rawInterpret Γ₁ β)
            (RawFamily.proofApplication (Ty.ofTyping Γ₁.as (QuotTyping.ofLift h).carrier)
              (rawInterpret Γ₁ f))
      | true =>
        ⨆ h : E[Γ₁.as.ctx] ⊢ₛ Expr.quotLift η l₁ l₂ α r β f hr a : β,
          RawFamily.decode D (Tm.label Γ₁.as h) (rawInterpret Γ₁ β)
            (RawFamily.quotLift D η (rawInterpret Γ₁ α) (rawInterpret Γ₁ f) (rawInterpret Γ₁ a))
  | .quotInd _ _ _ _ _ _ _ => ⊥
  | .app f e =>
      RawFamily.application (rawInterpret Γ₁ f) (rawInterpret Γ₁ e) (RawFamily.sourceQuery Γ₁ e)
  | .lam t e' =>
      ⨆ h : {u : Level ℓ // E[Γ₁.as.ctx] ⊢ₛ t : .sort u},
        have ⟨_, ht⟩ := h
        RawFamily.abstraction D (CtxCat.rawComprehension ht) (rawInterpret Γ₁ t)
          (rawInterpret (Γ₁.extension ht) e')
  | .forallE t t' =>
      ⨆ h : {p : Level ℓ × Level ℓ //
          E[Γ₁.as.ctx] ⊢ₛ t : .sort p.1 ∧ E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort p.2},
        have ⟨_, ht, ht'⟩ := h
        RawFamily.pi D (CtxCat.rawComprehension ht) (Ty.pairOfTyping Γ₁.as ht ht')
          (rawInterpret Γ₁ t) (rawInterpret (Γ₁.extension ht) t')
  | .letE _ e e' => rawInterpret Γ₁ (e'.inst e)
termination_by t => t.measure
decreasing_by
  all_goals first
    | exact Expr.measure_const_def ..
    | exact Expr.measure_ind_ctorTypeFn ..
    | exact Expr.measure_ind_param ..
    | exact Expr.measure_ctorField ..
    | exact Prod.Lex.left _ _ (lt_of_lt_of_le ‹_› (le_max_left _ _))
    | exact Inductive.forall_recrSubst_image
        (fun _ => Expr.measure_recr_param ..)
        (fun _ => Expr.measure_recr_motive ..)
        (fun _ _ => Expr.measure_recr_case ..)
        (fun _ => Expr.measure_recr_index ..)
        (Expr.measure_recr_major ..) _
    | exact Expr.measure_inst ..
    | exact Expr.measure_lt (by simp [Expr.headRank]) (by simp [Expr.size, Expr.sizeWith, Var]; omega)

variable {Γ₁ Γ₂ : CtxCat E ℓ} {nlevels : Nat} (l : Level ℓ)

@[simp] theorem rawInterpret_var (v : Var Γ₁.as.len) :
    rawInterpret D Γ₁ (.var v) = RawFamily.lookup v.db := by
  rw [rawInterpret]

@[simp] theorem rawInterpret_sort :
    rawInterpret D Γ₁ (.sort l) = RawFamily.sort l := by
  rw [rawInterpret]

@[simp] theorem rawInterpret_const_def (η : Head ζ (.const .def nlevels))
    (ls : Fin nlevels → Level ℓ) :
    rawInterpret D Γ₁ (.const η ls) = rawInterpret D Γ₁ ((E.get η).defValue.instL ls).wkClosed := by
  rw [rawInterpret]

@[simp] theorem rawInterpret_const_axiom (η : Head ζ (.const .axiom nlevels))
    (ls : Fin nlevels → Level ℓ) :
    rawInterpret D Γ₁ (.const η ls) = ⊥ := by
  rw [rawInterpret]

@[simp] theorem rawInterpret_const_opaque (η : Head ζ (.const .opaque nlevels))
    (ls : Fin nlevels → Level ℓ) :
    rawInterpret D Γ₁ (.const η ls) = ⊥ := by
  rw [rawInterpret]

variable {l}

section

variable {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  {is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} {maj : Expr ζ ℓ Γ₁.as.len}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}

theorem rawInterpret_ctor_prop (hrel : Level.rel ((E.get η).block.level.inst ls) = false) :
    rawInterpret D Γ₁ (.ctor η s c ls ps fds recFds) = ⊥ := by
  rw [rawInterpret, hrel]

theorem rawInterpret_recr_prop (hrel : l.rel = false) :
    rawInterpret D Γ₁ (.recr η s ls l ps ms mins is maj) = ⊥ := by
  rw [rawInterpret, hrel]

end

@[simp] theorem rawInterpret_app (f e : Expr ζ ℓ Γ₁.as.len) :
    rawInterpret D Γ₁ (.app f e) =
      RawFamily.application (rawInterpret D Γ₁ f) (rawInterpret D Γ₁ e) (RawFamily.sourceQuery Γ₁ e) := by
  rw [rawInterpret]

section

variable {Γ₁ Γ₂ : CtxCat E ℓ} {t₁ : Expr ζ ℓ Γ₁.as.len} {t₁' e' : Expr ζ ℓ (Γ₁.as.len + 1)}
  {u v : Level ℓ}

theorem rawInterpret_sort_fixed (l : Level ℓ) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (n : Tm_ Γ₂) :
    (CodeAssignment.piLimit E ℓ).rawExtend
      ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ (.sort l.succ)).app _ σ.op ρ) n
      ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ (.sort l)).app _ σ.op ρ) =
      (rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ (.sort l)).app _ σ.op ρ := by
  have hrel : Level.rel l.succ = true := by simp
  rw [rawInterpret, rawInterpret, RawFamily.sort_value, RawFamily.sort_value,
    CodeAssignment.rawExtend_toLower, CodeAssignment.piLimit_extend_sort, hrel,
    universeIdeal_principal .sort]

theorem rawInterpret_lam (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) :
    rawInterpret D Γ₁ (.lam t₁ e') =
      RawFamily.abstraction D (CtxCat.rawComprehension ht₁) (rawInterpret D Γ₁ t₁)
        (rawInterpret D (CtxCat.extension Γ₁ ht₁) e') := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq ⟨u, ht₁⟩ fun _ => rfl

theorem rawInterpret_forallE
    (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v) :
    rawInterpret D Γ₁ (.forallE t₁ t₁') =
      RawFamily.pi D (CtxCat.rawComprehension ht₁) (Ty.pairOfTyping Γ₁.as ht₁ ht₁')
        (rawInterpret D Γ₁ t₁) (rawInterpret D (CtxCat.extension Γ₁ ht₁) t₁') := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq ⟨(u, v), ht₁, ht₁'⟩ fun ⟨_, _, _⟩ => rfl

theorem rawInterpret_ind_typed {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
    {is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} (h : IndTyping Γ₁ η s ls ps is)
    (hB : (E.get η).block.WFStrong E) :
    rawInterpret D Γ₁ (.ind η s ls ps is) =
      RawFamily.ind h.code fun c =>
        RawFamily.closedApps
          (rawInterpret D (CtxCat.nil E ℓ) (((E.get η).block.ctorTypeFn s c).instL fun p => ls p))
          (fun p => Tm.label Γ₁.as (h.param p)) fun p => rawInterpret D Γ₁ (ps p) := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq h fun _ => RawFamily.iSup_eq hB fun _ => rfl

theorem rawInterpret_ctor_typed {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}
    (h : CtorTyping Γ₁ η s c ls ps fds recFds)
    (hrel : Level.rel ((E.get η).block.level.inst ls) = true) :
    rawInterpret D Γ₁ (.ctor η s c ls ps fds recFds) =
      RawFamily.ctor ⟨η, s, c⟩ h.names fun i => rawInterpret D Γ₁ (Fin.append fds recFds i) := by
  rw [rawInterpret, hrel]
  exact RawFamily.iSup_eq h fun _ => rfl

noncomputable abbrev recursor {ι : IndSig} {η : Head ζ (.inductive ι)} {l : Level ℓ}
    (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ) : RecApprox E ℓ ι :=
  recursorWith D (fun Γ₁ e _ => rawInterpret D Γ₁ e) hd ls

theorem rawInterpret_recr {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
    {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
    {is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} {maj : Expr ζ ℓ Γ₁.as.len}
    (h : RecTyping Γ₁ η s ls l ps ms mins is maj) (hrel : l.rel = true) :
    rawInterpret D Γ₁ (.recr η s ls l ps ms mins is maj) =
      RawFamily.closedApps (recursor D h.toRecDecl ls s) (fun v => Tm.label Γ₁.as (h.recrSubstWF v))
        fun v => rawInterpret D Γ₁ (Inductive.recrSubst ps ms mins is maj v) := by
  rw [rawInterpret, hrel]
  exact RawFamily.iSup_eq h fun _ => rfl

@[simp] theorem rawInterpret_letE (t e : Expr ζ ℓ Γ₁.as.len)
    (e' : Expr ζ ℓ (Γ₁.as.len + 1)) :
    rawInterpret D Γ₁ (.letE t e e') = rawInterpret D Γ₁ (e'.inst e) := by
  rw [rawInterpret]

end

section

variable {η : Head ζ .quot} {u v : Level ℓ} {α r β f h a : Expr ζ ℓ Γ₁.as.len}

theorem rawInterpret_quot (h : QuotTyping Γ₁ u α r) :
    rawInterpret D Γ₁ (.quot η u α r) = RawFamily.quot (h.code η) := by
  rw [rawInterpret]
  exact RawFamily.iSup_eq h fun _ => rfl

theorem rawInterpret_quotMk (ha : E[Γ₁.as.ctx] ⊢ₛ a : α) (hu : u.rel = true) :
    rawInterpret D Γ₁ (.quotMk η u α r a) =
      RawFamily.quotMk η (Tm.label Γ₁.as ha) (rawInterpret D Γ₁ a) := by
  rw [rawInterpret, hu]
  exact RawFamily.iSup_eq ha fun _ => rfl

theorem rawInterpret_quotMk_prop (hu : u.rel = false) :
    rawInterpret D Γ₁ (.quotMk η u α r a) = ⊥ := by
  rw [rawInterpret, hu]

theorem rawInterpret_quotLift_typed (hlift : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a : β)
    (hu : u.rel = true) :
    rawInterpret D Γ₁ (.quotLift η u v α r β f h a) =
      RawFamily.decode D (Tm.label Γ₁.as hlift) (rawInterpret D Γ₁ β)
        (RawFamily.quotLift D η (rawInterpret D Γ₁ α) (rawInterpret D Γ₁ f) (rawInterpret D Γ₁ a)) := by
  rw [rawInterpret, hu]
  exact RawFamily.iSup_eq hlift fun _ => rfl

theorem rawInterpret_quotLift_proof (hlift : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a : β)
    (hu : u.rel = false) (hα : E[Γ₁.as.ctx] ⊢ₛ α : .sort u) :
    rawInterpret D Γ₁ (.quotLift η u v α r β f h a) =
      RawFamily.decode D (Tm.label Γ₁.as hlift) (rawInterpret D Γ₁ β)
        (RawFamily.proofApplication (Ty.ofTyping Γ₁.as hα) (rawInterpret D Γ₁ f)) := by
  rw [rawInterpret, hu]
  exact RawFamily.iSup_eq hlift fun _ => rfl

@[simp] theorem rawInterpret_quotInd : rawInterpret D Γ₁ (.quotInd η u α r β f a) = ⊥ := by
  rw [rawInterpret]

end

variable (Γ₁)

theorem rawInterpret_isFinitary (t : Expr ζ ℓ Γ₁.as.len) :
    (rawInterpret D Γ₁ t).IsFinitary := by
  fun_induction rawInterpret D Γ₁ t with
  | case1 Γ₁ v => exact RawFamily.lookup_isFinitary v.db
  | case2 Γ₁ l => exact RawFamily.sort_isFinitary l
  | case3 _ _ _ _ ih | case20 _ _ _ _ ih => exact ih
  | case4 | case5 | case16 => exact RawFamily.bottom_isFinitary
  | case6 _ _ _ _ _ _ _ ihinterp ihparam =>
    exact RawFamily.IsFinitary.iSup fun h => RawFamily.IsFinitary.iSup fun _ =>
      RawFamily.ind_isFinitary h.code fun c => RawFamily.IsFinitary.closedApps (ihinterp h c) _ ihparam
  | case7 | case9 | case12 => exact RawFamily.bottom_isFinitary
  | case8 _ _ _ _ _ _ _ _ _ _ ih =>
    exact RawFamily.IsFinitary.iSup fun h => RawFamily.IsFinitary.ctor _ _ ih
  | case10 _ _ _ _ _ _ _ _ _ _ _ _ ihinterp ihargs =>
    exact RawFamily.IsFinitary.iSup fun h =>
      RawFamily.IsFinitary.closedApps (recursorWith_isFinitary D _ _ _ ihinterp _) _ (ihargs h)
  | case11 => exact RawFamily.IsFinitary.iSup fun h => RawFamily.quot_isFinitary (h.code _)
  | case13 _ _ _ _ _ _ _ ih =>
    exact RawFamily.IsFinitary.iSup fun ha => RawFamily.IsFinitary.quotMk _ _ ih
  | case14 _ _ _ _ _ _ _ _ _ _ _ ihβ ihf =>
    exact RawFamily.IsFinitary.iSup fun _ =>
      RawFamily.IsFinitary.decode D ihβ (RawFamily.IsFinitary.proofApplication _ ihf)
  | case15 _ _ _ _ _ _ _ _ _ _ _ ihβ ihα ihf iha =>
    exact RawFamily.IsFinitary.iSup fun _ =>
      RawFamily.IsFinitary.decode D ihβ (RawFamily.IsFinitary.quotLift D _ ihα ihf iha)
  | case17 _ _ _ ihf ihe => exact RawFamily.IsFinitary.application ihf ihe _
  | case18 _ _ _ iht ihe' =>
    exact RawFamily.IsFinitary.iSup fun ⟨u, ht⟩ =>
      RawFamily.IsFinitary.abstraction D (CtxCat.rawComprehension ht) iht (ihe' u ht)
  | case19 _ _ _ iht iht' =>
    exact RawFamily.IsFinitary.iSup fun ⟨uv, ht, _⟩ =>
      RawFamily.IsFinitary.pi D (CtxCat.rawComprehension ht) _ iht (iht' uv ht)

end Metalean.CoherentShape
