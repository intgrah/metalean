/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Inductive
import Metalean.Strong.InstLevel
import Metalean.Strong.Structure
import Metalean.Strong.Substitution
import Metalean.Strong.Telescope
import Metalean.Strong.WeakenEnv
import Metalean.Typing.Builtin.Eq
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}

namespace Entry

variable {sig sig₁ : Sig} {entry : Entry ζ sig}

inductive WFStrong (E : Env ζ) : {sig : Sig} → Entry ζ sig → Prop where
  | axiom {nlevels : Nat} {t : Expr ζ nlevels 0}
    {u : Level nlevels} :
    E[.nil] ⊢ₛ t : .sort u →
    WFStrong E (.axiom t)
  | opaque {nlevels : Nat} {value t : Expr ζ nlevels 0}
    {u : Level nlevels} :
    E[.nil] ⊢ₛ value : t →
    E[.nil] ⊢ₛ t : .sort u →
    WFStrong E (.opaque t)
  | def {nlevels : Nat} {e t : Expr ζ nlevels 0}
    {u : Level nlevels} :
    E[.nil] ⊢ₛ t : .sort u →
    E[.nil] ⊢ₛ e : t →
    WFStrong E (.def t e)
  | quot {η : Head ζ (.inductive Eq.sig)} :
    (E.get η).block = Eq.block →
    WFStrong E (.quot η)
  | inductive {ι : IndSig} {I : Inductive ζ ι} :
    I.WFStrong E →
    WFStrong E (.inductive I)

theorem WF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t) :
    entry.WF E →
    entry.WFStrong E
  | .axiom  ⟨_, ht⟩ =>
    .axiom (tr ht .nil)
  | .opaque he ⟨_, ht⟩ =>
    .opaque (tr he .nil) (tr ht .nil)
  | .def ⟨_, ht⟩ he =>
    .def (tr ht .nil) (tr he .nil)
  | .quot hη => .quot hη
  | .inductive hI => .inductive (hI.toStrong tr)

theorem WFStrong.weakenEnv
    {entry' : Entry ζ sig₁} :
    entry.WFStrong E →
    (entry.weakenEnv).WFStrong (E.snoc entry')
  | .axiom ht =>
    .axiom <| by
      simpa! [Ctx.weakenEnv, Expr.weakenEnv] using ht.weakenEnv entry'
  | .opaque hvalue ht =>
    .opaque
      (by simpa [Ctx.weakenEnv, Expr.weakenEnv] using hvalue.weakenEnv entry')
      (by simpa! [Ctx.weakenEnv, Expr.weakenEnv] using ht.weakenEnv entry')
  | .def ht hvalue =>
    .def
      (by simpa! [Ctx.weakenEnv, Expr.weakenEnv] using ht.weakenEnv entry')
      (by simpa [Ctx.weakenEnv, Expr.weakenEnv] using hvalue.weakenEnv entry')
  | .quot heq =>
    .quot <| by
      simpa using congrArg (Inductive.map (.step .refl : ζ ⟶ ζ.snoc sig₁)) heq
  | .inductive hI => .inductive hI.weakenEnv

theorem WFStrong.block {ι : IndSig}
    {entry : Entry ζ (.inductive ι)} :
     entry.WFStrong E →
    entry.block.WFStrong E
  | .inductive hI => hI

theorem WFStrong.value {nlevels : Nat}
    {entry : Entry ζ (.const .def nlevels)} :
    entry.WFStrong E →
    E[.nil] ⊢ₛ entry.defValue : entry.constType
  | .def _ hvalue => hvalue

theorem WFStrong.type {kind : ConstKind} {nlevels : Nat}
    {entry : Entry ζ (.const kind nlevels)} :
    entry.WFStrong E →
    E[.nil] ⊢ₛ entry.constType typ
  | .axiom ht => ⟨_, ht⟩
  | .opaque _ ht => ⟨_, ht⟩
  | .def ht _ => ⟨_, ht⟩

theorem WFStrong.constType
    {kind : ConstKind} {nlevels : Nat}
    {η : Head ζ (.const kind nlevels)}
    (h : (E.get η).WFStrong E) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (ls : Fin nlevels → Level ℓ) :
    E[Γ] ⊢ₛ ((E.get η).constType.instL ls).wkClosed typ :=
  have ⟨u, ht⟩ := h.type
  ⟨u.inst ls, by simpa! using (ht.instLevel ls).wkClosed⟩

theorem WFStrong.defValue
    {nlevels : Nat} {η : Head ζ (.const .def nlevels)}
    (h : (E.get η).WFStrong E) {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (ls : Fin nlevels → Level ℓ) :
    E[Γ] ⊢ₛ ((E.get η).defValue.instL ls).wkClosed :
      ((E.get η).constType.instL ls).wkClosed :=
  (h.value.instLevel ls).wkClosed

theorem WFStrong.ctorType
    {ι : IndSig} {η : Head ζ (.inductive ι)}
    (h : (E.get η).WFStrong E)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) ≡
      .ind η s ls ps₂ (((E.get η).block.ctors s c).targetIndex ls ps₂ fds₂) :
      .sort ((E.get η).block.level.inst ls) := by
  intro hps hfields
  have hctor := h.block.ctors s c
  exact .indDF hps (hctor.targetIndex_congr h.block.params · hps hfields)

end Entry

theorem Defeq.toStrong
    (hwf : ∀ {sig} (η : Head ζ sig), (E.get η).WFStrong E) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t := by
  intro hΓ h
  induction h with
  | var => exact hΓ.var _
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hΓ).trans (ih₂ hΓ)
  | sortDF => exact .sortDF
  | @etaStruct n Γ ι η s c ls ps is maj h _ _ ihps ihmaj =>
    have hps := fun p => ihps p hΓ
    have hmaj := ihmaj hΓ
    have hindices : is = h.indices :=
      funext h.no_indices.elim
    subst hindices
    exact .etaStruct h hps hmaj
      (h.rebuildTerm_hasTypeStrong (hwf η).block h.indices hΓ hps hmaj)
  | @constDF n nlevels kind Γ η ls =>
    have ⟨_, ht⟩ := (hwf η).type
    exact .constDF (by simpa [Expr.instL] using (ht.instLevel ls).wkClosed)
  | indDF _ _ ihps ihis =>
    exact .indDF (fun p => ihps p hΓ) fun i => ihis i hΓ
  | @ctorDF _ _ ι η s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂
      _ _ _ ihps ihfields ihrecFields =>
    have hps := fun p => ihps p hΓ
    have hfields := fun f => ihfields f hΓ
    have hrecFields := fun f => ihrecFields f hΓ
    have hB := (hwf η).block
    exact .ctorDF hps hfields hrecFields
      (fun f => ((hB.ctors s c).ordinaryFieldExpr_congr hB.params f
        hps hfields).choose_spec)
      (fun f => ((hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f
        hps hfields).choose_spec)
      (hwf _ |>.ctorType _ _ hps hfields)
  | recrDF hallowed _ _ _ _ _ ihps ihms ihmins
      ihis ihmaj =>
    have hps := fun p => ihps p hΓ
    have hms := fun s => ihms s hΓ
    have hmins := fun s c => ihmins s c hΓ
    have his := fun i => ihis i hΓ
    have hmaj := ihmaj hΓ
    exact .recrDF hallowed hps hms hmins his hmaj
      (hwf _ |>.block.motiveResult_congr hΓ
        hps hms his hmaj)
  | appDF _ _ ihf ihe =>
    have hf := ihf hΓ
    have he := ihe hΓ
    obtain ⟨_, hpi⟩ := hf.regular
    obtain ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hpi.forallE_inv
    exact .appDF ht ht' hf he (ht'.inst_congr he)
  | lamDF _ _ iht ihbody =>
    have ht := iht hΓ
    have hbody := ihbody (hΓ.snoc ⟨_, ht.left⟩)
    obtain ⟨_, ht'⟩ := hbody.regular
    exact .lamDF ht ht' (ht.snocConv ht') hbody (ht.snocConv hbody)
  | forallEDF _ _ iht ihbody =>
    have ht := iht hΓ
    have hbody := ihbody (hΓ.snoc ⟨_, ht.left⟩)
    exact .forallEDF ht hbody (ht.snocConv hbody)
  | defeqDF _ _ iht ihe => exact .defeqDF (iht hΓ) (ihe hΓ)
  | beta _ _ ihbody ihe =>
    have he := ihe hΓ
    obtain ⟨u, ht⟩ := he.regular
    have hbody := ihbody (hΓ.snoc ⟨u, ht⟩)
    obtain ⟨_, ht'⟩ := hbody.regular
    have hσ := SubstWFStrong.inst hΓ he
    exact .beta ht ht' hbody he (ht'.substitution hσ)
      (hbody.substitution hσ)
  | zeta _ _ _ iht ihv ihbody =>
    have hbody := ihbody hΓ
    have ⟨_, hr⟩ := hbody.regular
    exact .zeta (iht hΓ) (ihv hΓ) hr hbody
  | @eta _ _ _ t _ _ ih =>
    have he := ih hΓ
    obtain ⟨_, hpi⟩ := he.regular
    obtain ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hpi.forallE_inv
    exact .eta ht ht' (by simpa [Expr.wk] using ht.wk t)
      (by simpa [Expr.wk] using he.wk t) he
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp hΓ) (ihh hΓ) (ihh' hΓ)
  | @iota _ _ ι η s c ls l ps ms mins fds recFds hallowed _ _ _ _ _
      ihps ihms ihmins ihfields ihrecFields =>
    have hps := fun p => ihps p hΓ
    have hms := fun s => ihms s hΓ
    have hmins := fun s c => ihmins s c hΓ
    have hfields := fun f => ihfields f hΓ
    have hrecFields := fun f => ihrecFields f hΓ
    have hB := (hwf η).block
    have hσ := Ctor.targetSubstWFStrong (ctor := (E.get η).block.ctors s c)
      hps hfields
    have his := fun i => (hB.ctors s c).targetIndex i hσ
    have hmaj := DefeqStrong.ctorDF hps hfields hrecFields
      (fun f => (hB.ctors s c).ordinaryFieldExprStrong f hps hfields)
      (fun f => ((hB.ctors s c).recursiveFieldExprStrong rfl f hΓ hps hfields).choose_spec)
      (.indDF hps his)
    have htype := hB.motiveResult_congr hΓ hps hms his hmaj
    exact .iota hallowed hps hms hmins hfields hrecFields htype
      (Inductive.iotaLhs_hasTypeStrong (hB.ctors s c) hallowed hΓ hps hms hmins
        hfields hrecFields hσ htype)
      (hB.iotaRhs_hasTypeStrong hallowed hΓ hps hms hmins hfields hrecFields)
  | quotDF _ _ ihα ihr =>
    have hα := ihα hΓ
    exact .quotDF hα (ihr hΓ)
  | quotMkDF _ _ _ ihα ihr iha =>
    have hα := ihα hΓ
    exact .quotMkDF hα (ihr hΓ) (iha hΓ)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    have hα := ihα hΓ
    have hβ := ihβ hΓ
    exact .quotLiftDF hα (ihr hΓ) hβ (ihf hΓ) (ihh hΓ) (iha hΓ)
  | quotIndDF _ _ _ _ _ ihα ihr ihβ ihf iha =>
    have hα := ihα hΓ
    have ha := iha hΓ
    have hβ := ihβ hΓ
    obtain ⟨_, hmotive⟩ := hβ.regular
    obtain ⟨⟨_, hquot⟩, ⟨_, hprop⟩⟩ :=
      hmotive.forallE_inv
    have hresultTy := hprop.substitution
      (SubstWFStrong.inst hΓ ha.left)
    have hresult := DefeqStrong.appDF hquot hprop hβ ha hresultTy
    exact .quotIndDF hα (ihr hΓ) hβ (ihf hΓ) ha
      (by simpa [Expr.inst] using hresult)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    exact .quotIota (ihα hΓ) (ihr hΓ) (ihβ hΓ) (ihf hΓ) (ihh hΓ)
      (iha hΓ) (ihlhs hΓ) (ihrhs hΓ)
  | delta =>
    exact .delta
      (hwf _ |>.constType _ |>.choose_spec)
      (hwf _ |>.defValue _)

theorem Env.Ordered.entryWFStrong (ho : E.Ordered) {sig : Sig} (η : Head ζ sig) :
    (E.get η).WFStrong E := by
  induction ho generalizing sig with
  | nil => exact nomatch η
  | snoc _ hentry ih =>
    cases η with
    | here =>
      simpa [Env.get] using
        (hentry.toStrong fun h hΓ => h.toStrong ih hΓ).weakenEnv
    | there η =>
      simpa [Env.get] using (ih η).weakenEnv

theorem Defeq.toStrongOrdered (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t :=
  Defeq.toStrong ho.entryWFStrong

theorem Env.Ordered.block_spec {ι : IndSig} {ζ₀ : Sigs} {E₀ : Env ζ₀} (ho : E₀.Ordered)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.inductive ι)) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (I : Inductive ζ₂ ι),
      ζ₂.length < ζ₀.length ∧ I.WFStrong E₂ ∧
        (E.get (η.map pre.sigs)).block = I.map (pre₂ ≫ pre).sigs := by
  induction ho with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry ho hentry ih =>
    cases η with
    | here =>
      cases entry with
      | «inductive» I =>
        have .«inductive» hI := hentry
        refine ⟨_, E₀, .step .refl, I, Nat.lt_succ_self _,
          hI.toStrong fun hd hΓ => hd.toStrongOrdered ho hΓ, ?_⟩
        rw [dsimp% (Env.lookup _).naturality_apply pre Head.here]
        exact (Functor.map_comp_apply (Env.forget ⋙ Inductive.functor ι) (X := E₀.as)
          (Y := (E₀.snoc (.inductive I)).as) (Z := E.as) (.step .refl) pre I).symm
    | there η =>
      have ⟨ζ₂, E₂, pre₂, I, hlen, hI, hget⟩ := ih (.step .refl ≫ pre) η
      refine ⟨ζ₂, E₂, pre₂ ≫ .step .refl, I, Nat.lt_succ_of_lt hlen, hI, ?_⟩
      have hsigs := Env.forget.map_comp (X := E₀.as) (Y := (E₀.snoc entry).as) (Z := E.as)
        (.step .refl) pre
      have hη := ConcreteCategory.congr_hom ((Head.functor _).map_comp
        (Sigs.Prefix.step .refl : ζ₁ ⟶ ζ₁.snoc sig) pre.sigs) η
      dsimp at hsigs hη
      rw [Category.assoc, ← hget, hsigs]
      exact congrArg (fun η => (E.get η).block) hη.symm

open CategoryTheory in
theorem Env.Ordered.def_spec {nlevels : Nat} {ζ₀ : Sigs} {E₀ : Env ζ₀} (ho : E₀.Ordered)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.const .def nlevels)) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (t e : Expr ζ₂ nlevels 0),
      ζ₂.length < ζ₀.length ∧ E₂[.nil] ⊢ₛ e : t ∧
        E.get (η.map pre.sigs) = (Entry.def t e).map (pre₂ ≫ pre).sigs := by
  induction ho with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry ho hentry ih =>
    cases η with
    | here =>
      cases entry with
      | «def» t e =>
        have .«def» _ he := hentry
        refine ⟨_, E₀, .step .refl, t, e, Nat.lt_succ_self _, he.toStrongOrdered ho .nil, ?_⟩
        rw [dsimp% (Env.lookup _).naturality_apply pre Head.here]
        exact (Functor.map_comp_apply (Env.forget ⋙ Entry.functor _) (X := E₀.as)
          (Y := (E₀.snoc (.def t e)).as) (Z := E.as) (.step .refl) pre (.def t e)).symm
    | there η =>
      have ⟨ζ₂, E₂, pre₂, t, e, hlen, he, hget⟩ := ih (.step .refl ≫ pre) η
      refine ⟨ζ₂, E₂, pre₂ ≫ .step .refl, t, e, Nat.lt_succ_of_lt hlen, he, ?_⟩
      have hsigs := Env.forget.map_comp (X := E₀.as) (Y := (E₀.snoc entry).as) (Z := E.as)
        (.step .refl) pre
      have hη := ConcreteCategory.congr_hom ((Head.functor _).map_comp
        (Sigs.Prefix.step .refl : ζ₁ ⟶ ζ₁.snoc sig) pre.sigs) η
      dsimp at hsigs hη
      rw [Category.assoc, ← hget, hsigs]
      exact congrArg E.get hη.symm

theorem CtxWF.toStrongOf :
    (∀ {n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t) →
    E[Γ] ⊢ ok →
    E[Γ] ⊢ₛ ok := by
  intro tr hΓ
  induction hΓ with
  | nil => exact .nil
  | snoc hΓ ht ih =>
    have ⟨u, ht⟩ := ht
    exact .snoc ih ⟨u, tr ht ih⟩

theorem CtxWF.toStrongOrdered (ho : E.Ordered) :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ₛ ok :=
  fun h => h.toStrongOf fun h hΓ => h.toStrongOrdered ho hΓ

theorem CtxWFStrong.snocOfHasType {t : Expr ζ ℓ n} {l : Level ℓ}
    (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ t : .sort l →
    E[Γ.snoc t] ⊢ₛ ok :=
  fun hΓ ht => hΓ.snoc ⟨l, ht.toStrongOrdered ho hΓ⟩

theorem CtxWFStrong.append {P : Level ℓ → Prop}
    (ho : E.Ordered) {m : Nat} :
    E[Γ] ⊢ₛ ok →
    {Δ : Ctx ζ ℓ n m} →
    WFTele E P Γ Δ →
    E[Γ ++ Δ] ⊢ₛ ok := by
  intro hΓ Δ hΔ
  induction hΔ with
  | nil => exact hΓ
  | @snoc m Δ t hΔ ht ih =>
    have ⟨_, htu, _⟩ := ht
    exact ih.snocOfHasType ho htu

end Metalean
