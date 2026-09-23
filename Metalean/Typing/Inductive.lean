/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Context
import Metalean.Typing.InstLevel
import Metalean.Typing.Map
import Metalean.Typing.Substitution
import Metalean.Typing.Telescope
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₂ : Sigs} {E : Env ζ} {E₂ : Env ζ₂} {ℓ n m : Nat}
  {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}
  {ι : IndSig} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)}
  {nfields arity : Nat} {s target : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {csig : CtorSig ι.nsorts} {ctor : Ctor ζ ι s csig}
  {fd : RecField ζ ι nfields arity target}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
  {ms ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
  {is is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}
  {σ : Subst ζ ℓ (ι.nparams + nfields) n} {r : Expr ζ ℓ n}

theorem TeleWF.mono {P Q : Level ℓ → Prop} (hPQ : ∀ {u}, P u → Q u) (hΔ : TeleWF E P Γ Δ) :
    TeleWF E Q Γ Δ := by
  induction hΔ with
  | nil => exact .nil
  | snoc _ ht ih =>
    have ⟨u, hu, ht⟩ := ht
    exact .snoc ih ⟨u, hPQ hu, ht⟩

theorem TeleWF.instLevel {P : Level ℓ → Prop}
    {ℓ' : Nat} {Q : Level ℓ' → Prop} (ls : Param ℓ → Level ℓ')
    (hPQ : ∀ {u}, P u → Q u{ls}) (hΔ : TeleWF E P Γ Δ) :
    TeleWF E Q Γ{ls} Δ{ls} := by
  induction hΔ with
  | nil => exact .nil
  | @snoc b Δ t _ ht ih =>
    have ⟨u, hu, ht⟩ := ht
    refine .snoc ih ⟨u{ls}, hPQ hu, ?_⟩
    have ht := ht.instLevel ls
    rwa [Ctx.instL_append] at ht

theorem TeleWF.get_instL_subst_congr {ℓ' : Nat} {P : Level ℓ' → Prop}
    {Θ : Ctx ζ ℓ' 0 m} {σ₁ σ₂ : Subst ζ ℓ m n} (hΘ : TeleWF E P .nil Θ) (ls : Param ℓ' → Level ℓ)
    (v : Var m) :
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Θ{ls} →
    ∃ u : Level ℓ,
    E[Γ] ⊢ (Θ.get v){ls}.subst σ₁ ≡
      (Θ.get v){ls}.subst σ₂ : .sort u := by
  intro hσ
  have hΘctx : E[Θ] ⊢ ok := by
    simpa using hΘ.appendCtxWF .nil
  have ⟨u, hu⟩ := hΘctx.get v
  have hΘ' : TeleWF E (fun _ : Level ℓ => True) .nil Θ{ls} :=
    hΘ.instLevel (Q := fun _ => True) ls fun _ => trivial
  have h := hu.instLevel ls
  exact ⟨_, hΘ'.substitution_congr hσ (by simpa using h)⟩

theorem TeleWF.pi_instL_substN_congr {ℓ' a k : Nat} {P : Level ℓ' → Prop}
    {Γ₀ : Ctx ζ ℓ' 0 a} {Θ : Ctx ζ ℓ' a (a + k)}
    {σ₁ σ₂ : Subst ζ ℓ a n} {e₁ e₂ : Expr ζ ℓ (n + k)} {l : Level ℓ}
    (hΓ₀ : TeleWF E P .nil Γ₀) (hΘ : TeleWF E P Γ₀ Θ) (ls : Param ℓ' → Level ℓ) :
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Γ₀{ls} →
    E[Γ ++ Ctx.substN σ₁ k Θ{ls}] ⊢ e₁ ≡ e₂ : .sort l →
    ∃ u : Level ℓ,
    E[Γ] ⊢ Ctx.pi e₁ (Ctx.substN σ₁ k Θ{ls}) ≡
      Ctx.pi e₂ (Ctx.substN σ₂ k Θ{ls}) : .sort u := by
  intro hσ he
  induction Θ using Tele.addInduction generalizing l with
  | nil =>
    exact ⟨l, by simpa using he⟩
  | snoc k Θ t ih =>
    have .snoc hΘ ⟨u, _, ht⟩ := hΘ
    have hΘ : TeleWF E P Γ₀ Θ := hΘ
    have hclosed : TeleWF E P .nil (Γ₀ ++ Θ) :=
      hΓ₀.append (by simpa using hΘ)
    have hclosed' : TeleWF E (fun _ : Level ℓ => True) .nil (Γ₀ ++ Θ){ls} :=
      hclosed.instLevel (Q := fun _ => True) ls fun _ => trivial
    have hlevel := ht.instLevel ls
    have hlift : E[Γ ++ Ctx.substN σ₁ k Θ{ls}] ⊢ σ₁.liftN k ≡ σ₂.liftN k ⊣
        (Γ₀ ++ Θ){ls} := by
      rw [Ctx.instL_append]
      exact SubstEq.liftN (hΘ.instLevel (Q := fun _ : Level ℓ => True) ls fun _ => trivial) hσ
    have htype := hclosed'.substitution_congr hlift
      (by simpa using hlevel)
    have hbody : E[(Γ ++ Ctx.substN σ₁ k Θ{ls}).snoc
        (t{ls}.subst (σ₁.liftN k))] ⊢ e₁ ≡ e₂ : .sort l := by
      simpa [Ctx.substN] using he
    exact ih hΘ (.forallEDF htype hbody (htype.snocConv hbody))

theorem TeleWF.map (pre : E.as ⟶ E₂.as) {P : Level ℓ → Prop} {T : Ctx ζ ℓ n m}
    (h : TeleWF E P Γ T) :
    TeleWF E₂ P (Γ.map pre.sigs) (T.map pre.sigs) := by
  induction h with
  | nil => exact .nil
  | snoc hT ht ih =>
    have ⟨u, hu, ht⟩ := ht
    exact .snoc ih ⟨u, hu, by simpa [Expr.map] using ht.map pre⟩

section

open Inductive

theorem Inductive.paramSubstEq :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ ps₁ ≡ ps₂ ⊣ I.params{ls} := by
  intro hps v
  rw [← Ctx.get_instL, I.paramType_eq_get_subst ls ps₁ v]
  exact hps v

theorem Inductive.IdxWF.instLevel {ℓ' : Nat} (h : I.IdxWF E Γ s ls ps is)
    (ls' : Param ℓ → Level ℓ') :
    I.IdxWF E Γ{ls'} s ls{ls'} ps{ls'} is{ls'} := by
  intro i
  simpa using (h i).instLevel ls'

theorem Inductive.IdxWF.map (pre : E.as ⟶ E₂.as) (h : I.IdxWF E Γ s ls ps is) :
    (I.map pre.sigs).IdxWF E₂ (Γ.map pre.sigs) s ls
      (fun p => (ps p).map pre.sigs) fun i => (is i).map pre.sigs := by
  intro i
  simpa using (h i).map pre

end

section

open Field

variable {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)} {fd : Field ζ ι nfields}

theorem FieldWF.type :
    FieldWF E I Γ fd →
    E[Γ] ⊢ fd.type typ
  | ⟨htype, _⟩ => ⟨_, htype⟩

theorem FieldWF.map (pre : E.as ⟶ E₂.as) :
    FieldWF E I Γ fd →
    FieldWF E₂ (I.map pre.sigs) (Γ.map pre.sigs) (fd.map pre.sigs) := by
  intro ⟨htype, hlevel⟩
  exact ⟨by simpa [Expr.map, Field.map] using htype.map pre, hlevel⟩

end

section

open RecField

variable {Γ Δ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}

theorem RecFieldWF.map (pre : E.as ⟶ E₂.as) :
    RecFieldWF E I Γ fd →
    RecFieldWF E₂ (I.map pre.sigs) (Γ.map pre.sigs) (fd.map pre.sigs) := by
  intro ⟨htele, his⟩
  exact ⟨htele.map pre, by simpa [RecField.map, Expr.map] using his.map pre⟩

section

variable {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
variable {arity : Nat} {s : Fin ι.nsorts}
  {Θ : Ctx ζ ι.nlevels (ι.nparams + nfields) (ι.nparams + nfields + arity)}
  {is : Fin (ι.nindices s) → Expr ζ ι.nlevels (ι.nparams + nfields + arity)}

theorem RecFieldWF.teleAt (h : RecFieldWF E I Γ ⟨Θ, is⟩)
    {ls : Fin ι.nlevels → Level 0} {bound : Nat}
    (hblock : I.level{ls}.eval ![] = bound + 1) :
    TeleWF E (fun l => l.eval ![] ≤ bound + 1) Γ{ls} Θ{ls} := by
  have hnz : I.level.eval (Level.eval ![] ∘ ls) ≠ 0 := by
    rw [← Level.eval_inst]
    omega
  apply h.tele.instLevel ls
  intro l hl
  rw [Level.eval_inst, ← hblock, Level.eval_inst]
  exact Level.eval_le_of_imax_le hl hnz

theorem RecFieldWF.recursiveIndex (h : RecFieldWF E I Γ ⟨Θ, is⟩)
    {ls : Fin ι.nlevels → Level ℓ} (index : Fin (ι.nindices s)) :
    E[Γ{ls} ++ Θ{ls}] ⊢
      (is index){ls} :
        I.indexType ls s
          (fun param => .var ⟨param.val, by omega⟩)
          is{ls} index := by
  simpa! using h.indices.instLevel ls index

end

theorem RecFieldWF.instantiatedIndices {fd : RecField ζ ι nfields arity s} (h : RecFieldWF E I Δ fd)
    {Γ : Ctx ζ ℓ 0 n}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p)
    (i) :
    E[Γ] ⊢ σ ⊣ Δ{ls} →
    E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ fd.instantiatedIndices ls σ i :
      I.indexType ls s (fun p => (ps p).wkN arity)
        (fd.instantiatedIndices ls σ) i := by
  intro hσ
  have ⟨htele, his⟩ := h
  have htele := htele.instLevel (Q := fun _ => True) ls
    fun _ => trivial
  have hσLift := SubstWF.liftN htele hσ
  have his := his.instLevel ls
  rw [Ctx.instL_append] at his
  have hi := (his i).substitution hσLift
  have hpsEq :
      (fun p : Fin ι.nparams =>
        (Expr.var ⟨p.val, by omega⟩ : Expr ζ ℓ _).subst (σ.liftN arity)) =
        fun p => (ps p).wkN arity := by
    funext p
    rw [Expr.subst, show (⟨p.val, by omega⟩ :
      Fin (ι.nparams + nfields + arity)) =
        (p.castAdd nfields).castAdd arity by ext; rfl,
      Subst.liftN_castAdd, hσparams]
  simp at hi
  rwa [hpsEq] at hi

theorem RecFieldWF.instantiatedType (h : RecFieldWF E I Δ fd) (hhead : (E.get η).block = I)
    {Γ₁ : Ctx ζ ℓ 0 n}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ₁] ⊢ ok →
    (∀ p, E[Γ₁] ⊢ ps p : I.paramType ls ps p) →
    E[Γ₁] ⊢ σ ⊣ Δ{ls} →
    E[Γ₁] ⊢ fd.instantiatedType η ls ps σ typ := by
  intro hΓ hps hσ
  cases hhead
  have ⟨telescope, is⟩ := fd
  have htele' := (h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ
  have hΓtele := htele'.appendCtxWF hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk p :
      E[Γ₁ ++ Ctx.substN σ arity telescope{ls}] ⊢ (ps p).wkN arity :
          (E.get η).block.paramType ls
            (fun p => (ps p).wkN arity) p := by
    simpa using (hps p).wkN
  exact Ctx.pi_isType hΓtele <| Defeq.indDF hpsWk his

end

variable {fds fds₁ fds₂ : Fin csig.nfields → Expr ζ ℓ n}

section

open Ctor

theorem CtorWF.map (pre : E.as ⟶ E₂.as) (h : CtorWF E I ctor) :
    CtorWF E₂ (I.map pre.sigs) (ctor.map pre.sigs) where
  ordinary f := by simpa [Inductive.map, Ctor.map] using (h.ordinary f).map pre
  recursive f := by simpa [Inductive.map, Ctor.map] using (h.recursive f).map pre
  targetIndices := by
    simpa [Inductive.map, Ctor.map, Expr.map] using h.targetIndices.map pre

theorem CtorWF.ordinaryFieldExpr (hctor : CtorWF E I ctor) (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ fds f :
      ((ctor.ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ ctor.ordinaryFieldExpr ls ps fds f : .sort (ctor.ordinary f).level{ls} := by
  intro hps hfields
  have hσ := Ctor.forall_ordinarySubst f.isLt.le hps
    fun prior => hfields (prior.castLE f.isLt.le)
  simpa! [Ctor.ordinaryFieldExpr] using ((hctor.ordinary f).typeExact.instLevel ls).substitution hσ

theorem CtorWF.recursiveFieldExpr (hctor : CtorWF E I ctor) (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ fds f :
      ((ctor.ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ ctor.recursiveFieldExpr η ls ps fds f typ :=
  fun hΓ hps hfields =>
    (hctor.recursive f).instantiatedType hhead (by simp) hΓ hps
      (Ctor.forall_ordinarySubst le_rfl hps hfields)

theorem Ctor.wfOrdinaryTeleAux (count : Nat) (hcount : count ≤ csig.nfields)
    (h : ∀ f : Fin count,
      FieldWF E I (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
        (ctor.ordinary (f.castLE hcount))) :
    TeleWF E I.LevelOK I.params (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    have ⟨htype, hlevel⟩ := h ⟨count, by omega⟩
    exact .snoc (ih (by omega) fun f => h (f.castSucc)) ⟨_, hlevel, htype⟩

theorem CtorWF.ordinaryTeleAux (h : CtorWF E I ctor) (count : Nat) (hcount : count ≤ csig.nfields) :
    TeleWF E I.LevelOK I.params (ctor.ordinaryTeleAux count hcount) :=
  wfOrdinaryTeleAux count hcount fun f => h.ordinary (f.castLE hcount)

private theorem CtorWF.ordinaryTeleAux_get (h : CtorWF E I ctor) (count : Nat)
    (hcount : count ≤ csig.nfields) (f : Fin count) :
    E[I.params ++ ctor.ordinaryTeleAux count hcount] ⊢
      Ctx.get (Fin.natAdd ι.nparams f)
        (I.params ++ ctor.ordinaryTeleAux count hcount) :
      .sort (ctor.ordinary (f.castLE hcount)).level := by
  induction f using Fin.lastInduction with
  | last count =>
    rw [Ctor.ordinaryTeleAux, Tele.append_snoc, Fin.natAdd_last, Ctx.get_last]
    exact (h.ordinary ((Fin.last count).castLE hcount)).typeExact.wk
      ((ctor.ordinary ⟨count, hcount⟩).type)
  | @cast count f ih =>
    rw [Ctor.ordinaryTeleAux, Tele.append_snoc, Ctx.get_snoc _ _ _ (by simp; omega)]
    exact (ih (by omega)).wk ((ctor.ordinary ⟨count, hcount⟩).type)

theorem CtorWF.ordinaryTele_get (h : CtorWF E I ctor) (f : Fin csig.nfields) :
    E[I.params ++ ctor.ordinaryTele] ⊢
      Ctx.get (Fin.natAdd ι.nparams f)
        (I.params ++ ctor.ordinaryTele) :
      .sort (ctor.ordinary f).level :=
  h.ordinaryTeleAux_get csig.nfields le_rfl f

theorem CtorWF.ordinaryFieldTele (h : CtorWF E I ctor)
    (hps : ∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) :
    TeleWF E (fun _ => True) Γ (ctor.ordinaryFieldTele η ls ps) :=
  (((h.ordinaryTeleAux csig.nfields le_rfl).instLevel ls fun _ => trivial).substitution
    (Inductive.paramSubstEq hps).left)

theorem CtorWF.boundOrdinarySubstWF (h : CtorWF E I ctor) :
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ Fin.append (fun p => (ps p).wkN csig.nfields)
        (Expr.boundVars n csig.nfields 0) ⊣
      (I.params ++ ctor.ordinaryTele){ls} := by
  intro hps
  have hσ := (Inductive.paramSubstEq hps).left
  have hfields := (h.ordinaryTeleAux csig.nfields le_rfl).instLevel
    (Q := fun _ => True) ls fun _ => trivial
  have hσ := SubstWF.liftN hfields hσ
  simpa [Ctor.ordinaryFieldTele, Ctor.ordinaryFieldTeleAux, Subst.liftN_eq_append] using hσ

private theorem CtorWF.recursiveFieldType (h : CtorWF E I ctor) (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ (ctor.recursive f).instantiatedType η ls
        (fun p => (ps p).wkN csig.nfields)
        (Fin.append (fun p => (ps p).wkN csig.nfields)
          fun fds => .var ⟨n + fds.val, by omega⟩) typ :=
  fun hΓ hps =>
    have htele := h.ordinaryFieldTele (η := η) hps
    (h.recursive f).instantiatedType hhead (by simp)
      (htele.appendCtxWF hΓ)
      (fun p => by simpa using (hps p).wkN)
      (h.boundOrdinarySubstWF hps)

theorem CtorWF.fieldTele (h : CtorWF E I ctor) (hhead : (E.get η).block = I) (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p)
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    TeleWF E (fun _ => True) Γ (ctor.fieldTele η ls ps stop) := by
  refine (h.ordinaryFieldTele (η := η) hps).append ?_
  apply TeleWF.ofTypes
  intro f
  have ⟨u, ht⟩ := h.recursiveFieldType hhead (f.castLE (Nat.le_of_lt_succ stop.isLt)) hΓ hps
  exact ⟨u, trivial, ht⟩

theorem CtorWF.targetIndex (h : CtorWF E I ctor) (i : Fin (ι.nindices s)) :
    E[Γ] ⊢ Fin.append ps fds ⊣
      (I.params ++ ctor.ordinaryTele){ls} →
    E[Γ] ⊢ ctor.targetIndex ls ps fds i :
      I.indexType ls s ps
        (fun i => ctor.targetIndex ls ps fds i) i := by
  intro hσ
  have hpsEq :
      (fun p : Fin ι.nparams =>
        ((Expr.var ⟨p.val, by omega⟩ :
          Expr ζ ℓ (ι.nparams + csig.nfields))).subst
            (Fin.append ps fds)) = ps :=
    funext (Fin.append_left ps fds)
  simpa [Ctor.targetIndex, hpsEq] using
    ((h.targetIndices i).instLevel ls).substitution hσ

theorem CtorWF.targetIndex_congr (h : CtorWF E I ctor)
    (hBparams : TeleWF E (fun _ => True) .nil I.params) (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
      ((ctor.ordinary f).type{ls}).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ ctor.targetIndex ls ps₁ fds₁ i ≡
      ctor.targetIndex ls ps₂ fds₂ i :
      I.indexType ls s ps₁
        (fun i => ctor.targetIndex ls ps₁ fds₁ i) i := by
  intro hps hfields
  have hfieldsTele : TeleWF E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params) ctor.ordinaryTele := by
    simpa using
      (h.ordinaryTeleAux csig.nfields le_rfl).mono
        fun _ => trivial
  have hsource := hBparams.append hfieldsTele
  have hsource := hsource.instLevel (Q := fun _ => True)
    ls fun _ => trivial
  have hσ := Ctor.forall_ordinarySubst le_rfl hps hfields
  have hpsEq :
      (fun p : Fin ι.nparams =>
        ((Expr.var ⟨p.val, by omega⟩ :
          Expr ζ ℓ (ι.nparams + csig.nfields))).subst
            (Fin.append ps₁ fds₁)) = ps₁ :=
    funext (Fin.append_left ps₁ fds₁)
  simpa [Ctor.targetIndex, hpsEq] using
    hsource.substitution_congr hσ ((h.targetIndices i).instLevel ls)

end

theorem RecFieldWF.instantiatedType_congr
    {Θ : Ctx ζ ι.nlevels ι.nparams
      (ι.nparams + nfields)}
    (hfield : RecFieldWF E I (I.params ++ Θ) fd)
    (hBparams : TeleWF E (fun _ => True) .nil I.params)
    (hsource : TeleWF E (fun _ => True) .nil (I.params ++ Θ))
    (hhead : (E.get η).block = I)
    {σ₁ σ₂ : Subst ζ ℓ (ι.nparams + nfields) n}
    (hps₁ : ∀ p, σ₁ (p.castAdd nfields) = ps₁ p)
    (hps₂ : ∀ p, σ₂ (p.castAdd nfields) = ps₂ p) :
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ (I.params ++ Θ){ls} →
    ∃ u : Level ℓ, E[Γ] ⊢ fd.instantiatedType η ls ps₁ σ₁ ≡
      fd.instantiatedType η ls ps₂ σ₂ : .sort u := by
  intro hσ
  let psId (p : Fin ι.nparams) : Expr ζ ι.nlevels (ι.nparams + nfields) :=
    .var (p.castAdd nfields)
  have hΔ : E[I.params ++ Θ] ⊢ ok := by
    simpa using hsource.appendCtxWF .nil
  have hpsCtx : E[I.params] ⊢ ok := by
    simpa using hBparams.appendCtxWF .nil
  have hpsId (p) : E[I.params ++ Θ] ⊢ psId p :
      I.paramType .param psId p := by
    have hp : E[I.params] ⊢ (.var p : Expr ζ ι.nlevels ι.nparams) :
        I.paramType .param (fun q => .var q) p := by
      have hp' : E[I.params] ⊢ .var p :
          (I.params.get p).subst .var := by
        change E[I.params] ⊢ .var p : (I.params.get p).subst Subst.id
        simpa using hpsCtx.var p
      rw [I.params.get_subst .var p p.val p.isLt rfl] at hp'
      simpa [Inductive.paramType] using hp'
    have hp := hp.wkN (Δ := Θ)
    have hterm : (Expr.var p).wkN nfields = psId p := by simp [psId]
    have hvars : (fun i => (Expr.var i).wkN nfields) = psId := by simp [psId]
    rw [hterm, Inductive.paramType_wkN, hvars] at hp
    exact hp
  have hid : E[I.params ++ Θ] ⊢ Subst.id ⊣
      (I.params ++ Θ){(Level.param : Param ι.nlevels → Level ι.nlevels)} := fun v => by
    simp only [Ctx.instL_param, Expr.subst_id]
    simpa only [Subst.id] using hΔ.var v
  have ⟨u, hraw⟩ := hfield.instantiatedType hhead (fun _ => rfl) hΔ hpsId hid
  have hraw := (hsource.instLevel (Q := fun _ => True) ls
    fun _ => trivial).substitution_congr hσ (hraw.instLevel ls)
  simp! [hps₁, hps₂] at hraw
  exact ⟨u{ls}, hraw⟩

section

open Ctor

theorem CtorWF.ordinaryFieldExpr_congr (h : CtorWF E I ctor)
    (hBparams : TeleWF E (fun _ => True) .nil I.params)
    (f : Fin csig.nfields)
    (hps : ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p)
    (hfields : ∀ g : Fin csig.nfields, g < f → E[Γ] ⊢ fds₁ g ≡ fds₂ g :
      ((ctor.ordinary g).type{ls}).subst
        (Fin.append ps₁ fun previous : Fin g.val =>
          fds₁ (previous.castLE g.isLt.le))) :
    E[Γ] ⊢ ctor.ordinaryFieldExpr ls ps₁ fds₁ f ≡
      ctor.ordinaryFieldExpr ls ps₂ fds₂ f : .sort (ctor.ordinary f).level{ls} := by
  have hfieldsTele : TeleWF E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params)
      (ctor.ordinaryTeleAux f.val f.isLt.le) := by
    simpa using (h.ordinaryTeleAux f.val f.isLt.le).mono fun _ => trivial
  simpa! [Ctor.ordinaryFieldExpr] using
    ((hBparams.append hfieldsTele).instLevel (Q := fun _ => True) ls
      fun _ => trivial).substitution_congr
        (Ctor.forall_ordinarySubst f.isLt.le hps fun g =>
          hfields (g.castLE f.isLt.le) g.isLt)
        ((h.ordinary f).typeExact.instLevel ls)

theorem CtorWF.recursiveFieldExpr_congr (h : CtorWF E I ctor)
    (hBparams : TeleWF E (fun _ => True) .nil I.params) (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
      ((ctor.ordinary f).type{ls}).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    ∃ u : Level ℓ, E[Γ] ⊢ ctor.recursiveFieldExpr η ls ps₁ fds₁ f ≡
      ctor.recursiveFieldExpr η ls ps₂ fds₂ f : .sort u :=
  fun hps hfields =>
    (h.recursive f).instantiatedType_congr
      hBparams
      (hBparams.append <| by simpa using
        (h.ordinaryTeleAux csig.nfields le_rfl).mono fun _ => trivial)
      hhead (by simp) (by simp)
      (Ctor.forall_ordinarySubst le_rfl hps hfields)

end

section

open Inductive

theorem InductiveWF.paramClosedWF {ℓ : Nat} (hB : InductiveWF E I) (ls : Fin ι.nlevels → Level ℓ) :
    E[I.params{ls}] ⊢ ok := by
  simpa [Ctx.instL] using
    (hB.params.instLevel (Q := fun _ => True) ls fun _ => trivial).appendCtxWF .nil

theorem InductiveWF.indexTele (hB : InductiveWF E I)
    (hps : ∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) :
    TeleWF E (fun _ => True) Γ (I.indexTele ls s ps) :=
  ((hB.indices s).instLevel ls fun _ => trivial).substitution (paramSubstEq hps).left

theorem Inductive.paramType_isType (hB : InductiveWF E I) (p : Fin ι.nparams) :
    (∀ q : Fin ι.nparams, q < p → E[Γ] ⊢ ps q : I.paramType ls ps q) →
    E[Γ] ⊢ I.paramType ls ps p typ := by
  intro hps
  have hΘ := hB.params.instLevel (Q := fun _ : Level ℓ => True) ls fun _ => trivial
  simpa [Inductive.paramType] using TeleWF.entry_isType_nil hΘ p.val p.isLt
    fun q hq => by
      simpa [Inductive.paramType] using
        hps ⟨q, by omega⟩ (by simpa [Fin.lt_def] using hq)

theorem Inductive.indexType_isType (hidx : TeleWF E (fun _ => True) I.params (I.indices s))
    (i : Fin (ι.nindices s)) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    (∀ j : Fin (ι.nindices s), j < i → E[Γ] ⊢ is j : I.indexType ls s ps is j) →
    E[Γ] ⊢ I.indexType ls s ps is i typ := by
  intro hΓ hps his
  have hΔ : TeleWF E (fun _ => True) Γ (I.indexTele ls s ps) :=
    (hidx.instLevel ls fun _ => trivial).substitution (paramSubstEq hps).left
  have h := TeleWF.entry_isType hΔ i
    (fun v => by rw [Expr.subst_id]; exact hΓ.var v)
    (by simpa using his)
  simpa using h

theorem Inductive.paramType_congr (hB : InductiveWF E I) (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ I.paramType ls ps₁ p ≡ I.paramType ls ps₂ p typ := by
  intro hps
  have ⟨u, h⟩ := hB.params.get_instL_subst_congr ls p (paramSubstEq hps)
  rw [I.paramType_eq_get_subst ls ps₁ p,
    I.paramType_eq_get_subst ls ps₂ p] at h
  exact .ofDefEq h

theorem Inductive.indexSubstEq (hB : InductiveWF E I) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ Fin.append ps₁ is₁ ≡ Fin.append ps₂ is₂ ⊣ (I.params ++ I.indices s){ls} := by
  intro hps his
  have hindices := (hB.indices s).instLevel (Q := fun _ : Level ℓ => True)
    ls fun _ => trivial
  rw [Ctx.instL_append]
  exact SubstEq.extendFamily hindices (paramSubstEq hps) fun i => by
    simpa [Inductive.indexType, Ctx.proj_eq_entry] using his i

theorem Inductive.indexType_congr (hB : InductiveWF E I) (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ I.indexType ls s ps₁ is₁ i ≡ I.indexType ls s ps₂ is₂ i typ := by
  intro hps his
  have hΘ : TeleWF E (fun _ : Level ι.nlevels => True) .nil (I.params ++ I.indices s) :=
    hB.params.append (by simpa using hB.indices s)
  have ⟨u, h⟩ := hΘ.get_instL_subst_congr ls (Fin.natAdd ι.nparams i) (indexSubstEq hB hps his)
  rw [I.indexType_eq_get_subst ls s ps₁ is₁ i,
    I.indexType_eq_get_subst ls s ps₂ is₂ i] at h
  exact .ofDefEq h

theorem Inductive.paramType_conv (hB : InductiveWF E I) (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ ps₂ p : I.paramType ls ps₂ p :=
  fun hps => (paramType_congr hB p hps).conv (hps p).right

theorem Inductive.indexType_conv (hB : InductiveWF E I) (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ is₂ i : I.indexType ls s ps₂ is₂ i :=
  fun hps his => (indexType_congr hB i hps his).conv (his i).right

theorem InductiveWF.motiveTele
    (hB : InductiveWF E (E.get η).block)
    (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ ps p :
      (E.get η).block.paramType ls ps p) :
    TeleWF E (fun _ => True) Γ ((E.get η).block.motiveTele η ls ps s) := by
  have hΓindices : E[Γ ++
      (E.get η).block.indexTele ls s ps] ⊢ ok :=
    (hB.indexTele hps).appendCtxWF hΓ
  constructor
  · exact hB.indexTele hps
  · exact ⟨(E.get η).block.level{ls}, trivial,
      Defeq.indDF
        (fun p => by simpa using (hps p).wkN)
        fun i => by
          have hv := hΓindices.var (Fin.natAdd n i)
          rw [Inductive.indexTele_get] at hv
          simpa [Fin.natAdd] using hv⟩

theorem Inductive.motiveType_congr (hB : InductiveWF E (E.get η).block) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    E[Γ] ⊢ (E.get η).block.motiveType η ls ps₁ l s ≡
      (E.get η).block.motiveType η ls ps₂ l s typ := by
  intro hΓ hps
  have hpsSelf (p) := (hps p).left
  have hΓindices : E[Γ ++
      (E.get η).block.indexTele ls s ps₁] ⊢ ok :=
    (hB.indexTele hpsSelf).appendCtxWF hΓ
  have hind : E[Γ ++ (E.get η).block.indexTele ls s ps₁] ⊢
      .ind η s ls (fun p => (ps₁ p).wkN (ι.nindices s))
        (fun i => .var (Fin.natAdd n i)) ≡
      .ind η s ls (fun p => (ps₂ p).wkN (ι.nindices s))
        (fun i => .var (Fin.natAdd n i)) :
      .sort (E.get η).block.level{ls} :=
    Defeq.indDF
      (fun p => by simpa using (hps p).wkN)
      fun i => by
        have hv := hΓindices.var (Fin.natAdd n i)
        rw [Inductive.indexTele_get] at hv
        exact hv
  have hsort : E[(Γ ++ (E.get η).block.indexTele ls s ps₁).snoc
      (.ind η s ls (fun p => (ps₁ p).wkN (ι.nindices s))
        fun i => .var (Fin.natAdd n i))] ⊢ Expr.sort l ≡ .sort l : .sort l.succ :=
    .sortDF
  have hforall := Defeq.forallEDF hind hsort (hind.snocConv hsort)
  have ⟨u, hpi⟩ := TeleWF.pi_instL_substN_congr
    hB.params (hB.indices s) ls (paramSubstEq hps) hforall
  exact .ofDefEq hpi

end

namespace CtorWF

theorem fieldParams (ctor : Ctor ζ ι s csig)
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ csig.fieldParams ps₁ p ≡ csig.fieldParams ps₂ p :
        (E.get η).block.paramType ls (csig.fieldParams ps₁) p := by
  intro hps
  have hp := ((hps p).wkN (Δ := ctor.ordinaryFieldTele η ls ps₁)).wkN
    (Δ := ctor.recursiveFieldTele η ls (fun p => (ps₁ p).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  change E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ ((ps₁ p).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ps₂ p).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.paramType ls
      (fun p => ((ps₁ p).wkN csig.nfields).wkN csig.nrecFields) p
  simpa [Tele.append_assoc, Ctor.fieldTele] using hp

theorem fieldMotive (ctor : Ctor ζ ι s csig)
    (s₁ : Fin ι.nsorts) :
    (∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps l s) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
        ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.motiveType η ls (csig.fieldParams ps) l s₁ := by
  intro hms
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) l s₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using (hms s₁).wkN.wkN

theorem fieldCase (ctor : Ctor ζ ι s csig)
    (s₁ : Fin ι.nsorts) (c₁ : Fin (ι.nctors s₁)) :
    (∀ s₁ c₁, E[Γ] ⊢ mins s₁ c₁ : (E.get η).block.caseFnType η ls ps ms s₁ c₁) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.caseFnType η ls (csig.fieldParams ps)
          (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁ := by
  intro hmins
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
      (E.get η).block.caseFnType η ls
        (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields)
        (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using
    (hmins s₁ c₁).wkN.wkN

theorem fieldOrdinary (hctor : CtorWF E (E.get η).block ctor) (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ csig.fieldOrdinary f :
      ((ctor.ordinary f).type{ls}).subst
        (Fin.append (csig.fieldParams ps) fun previous : Fin f.val =>
          csig.fieldOrdinary (previous.castLE f.isLt.le)) := by
  intro hps
  have hl := hctor.boundOrdinarySubstWF (η := η) hps (Fin.natAdd ι.nparams f)
  rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL] at hl
  have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
    simp
  rw [(E.get η).block.params.entry_append_right _ (by omega) hb (by omega)] at hl
  have hl : E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ Expr.boundVars n csig.nfields 0 f :
        ((ctor.ordinary f).type{ls}).subst
          (Fin.append (fun p => (ps p).wkN csig.nfields)
            fun previous => Expr.boundVars n csig.nfields 0
              (previous.castLE f.isLt.le)) := by
    simpa using hl
  unfold CtorSig.fieldParams CtorSig.fieldOrdinary
  have hl := hl.wkN (Δ := ctor.recursiveFieldTele η ls (fun p => (ps p).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  simpa [Tele.append_assoc, Expr.boundVars, Ctor.fieldTele, Expr.instL] using hl

theorem fieldTargetSubst (hctor : CtorWF E (E.get η).block ctor) :
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ Fin.append (csig.fieldParams ps) csig.fieldOrdinary ⊣
        ((E.get η).block.params ++ ctor.ordinaryTele){ls} :=
  fun hps =>
    Ctor.forall_ordinarySubst le_rfl (CtorWF.fieldParams ctor · hps) (hctor.fieldOrdinary · hps)

theorem fieldRecursive (hctor : CtorWF E (E.get η).block ctor) (f : Fin csig.nrecFields) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ csig.fieldRecursive f :
      (ctor.recursive f).instantiatedType η ls (csig.fieldParams ps)
        (Fin.append (csig.fieldParams ps) csig.fieldOrdinary) := by
  intro hΓ hps
  have hΓfield := (hctor.fieldTele rfl hΓ hps).appendCtxWF hΓ
  unfold Ctor.fieldTele
  rw [← Tele.append_assoc]
  have hl := hΓfield.var (Fin.natAdd (n + csig.nfields) f)
  rw [Ctor.fieldTele, ← Tele.append_assoc] at hl
  erw [Ctor.recursiveFieldTeleAux, Ctx.get_append_ofTypes (Γ ++ ctor.ordinaryFieldTele η ls ps) _ f] at hl
  rw [RecField.instantiatedType_wkN] at hl
  have hpsEq :
      (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) = csig.fieldParams ps := rfl
  have hsubstEq :
      (fun v => (Fin.append (fun i => (ps i).wkN csig.nfields)
        (Expr.boundVars n csig.nfields 0) v).wkN csig.nrecFields) =
        Fin.append (csig.fieldParams ps) csig.fieldOrdinary := by
    rw [CtorSig.targetSubst_fields]
    funext v
    exact Expr.wkN_eq_rename _ _
  rw [hpsEq, hsubstEq] at hl
  simpa [CtorSig.fieldRecursive, Ctor.recursiveFieldTeleAux] using hl

end CtorWF

theorem Defeq.nullaryCtor {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
    (hB : InductiveWF E (E.get η).block) (hf : IsEmpty (Fin (ι.ctors s c).nfields))
    (hr : IsEmpty (Fin (ι.ctors s c).nrecFields)) :
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ .ctor η s c ls ps fds recFds :
      .ind η s ls ps fun i => ((E.get η).block.ctors s c).targetIndex ls ps fds i := by
  intro hps
  have hσ := Ctor.forall_ordinarySubst le_rfl (ctor := (E.get η).block.ctors s c) (fds₁ := fds) (fds₂ := fds) hps
    fun f => hf.elim f
  exact .ctorDF (fieldLevels := hf.elim) (recFieldLevels := hr.elim)
    hps hf.elim hr.elim hf.elim hr.elim
    (.indDF hps fun i => (hB.ctors s c).targetIndex i hσ)

section Recursor

variable {Δ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}

section

open Inductive

theorem InductiveWF.motiveResult_congr (hB : InductiveWF E (E.get η).block)
    {maj₁ maj₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i :
      (E.get η).block.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ maj₁ ≡ maj₂ :
      .ind η s ls ps₁ is₁ →
    E[Γ] ⊢ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
      Inductive.motiveResult (ms₂ s) is₂ maj₂ :
      .sort l := by
  intro hΓ hps hms his hmaj
  have hpsSelf := fun p => (hps p).left
  have htele := hB.motiveTele (s := s) hΓ hpsSelf
  have .snoc hisTele ⟨_, _, hind⟩ := htele
  have hmotive := hms s
  change E[Γ] ⊢ ms₁ s ≡ ms₂ s :
    Ctx.pi (.forallE
      (.ind η s ls
        (fun p => (ps₁ p).wkN (ι.nindices s))
        fun i => .var (Fin.natAdd n i))
      (.sort l))
      ((E.get η).block.indexTele ls s ps₁) at hmotive
  have hcodomain : E[Γ ++
      (E.get η).block.indexTele ls s ps₁] ⊢ .forallE
        (.ind η s ls
          (fun p => (ps₁ p).wkN (ι.nindices s))
          fun i => .var (Fin.natAdd n i))
        (.sort l) typ :=
    ⟨_, .forallEDF hind .sortDF .sortDF⟩
  have hisPhase (i : Fin (ι.nindices s)) : E[Γ] ⊢ is₁ i ≡ is₂ i :
      (((E.get η).block.indexTele ls s ps₁).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          is₁ (previous.castLE i.isLt.le)) := by
    simpa using his i
  have hfun := Ctx.pi_applyFamily hΓ hisTele hcodomain hisPhase hmotive
  have ⟨_, hmajType⟩ := hmaj.regular
  simpa [Inductive.motiveResult] using .appDF
    hmajType .sortDF
    (by simpa! using hfun) hmaj
    (by simpa! using .sortDF)

theorem Inductive.paramsWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hps : ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) (p) :
    E[Γ ++ Θ] ⊢ (ps₁ p).wkN arity ≡ (ps₂ p).wkN arity :
      (E.get η).block.paramType ls (fun p => (ps₁ p).wkN arity) p := by
  simpa using (hps p).wkN

theorem Inductive.motivesWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hms : ∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps₁ l s) (s) :
    E[Γ ++ Θ] ⊢ (ms₁ s).wkN arity ≡ (ms₂ s).wkN arity :
      (E.get η).block.motiveType η ls (fun p => (ps₁ p).wkN arity) l s := by
  simpa using (hms s).wkN

theorem Inductive.casesWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hmins : ∀ s c, E[Γ] ⊢ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) (s c) :
    E[Γ ++ Θ] ⊢ (mins s c).wkN arity :
      (E.get η).block.caseFnType η ls (fun p => (ps p).wkN arity)
        (fun s => (ms s).wkN arity) s c := by
  simpa using (hmins s c).wkN

end

theorem RecFieldWF.ihType (h : RecFieldWF E I Δ fd) (hB : InductiveWF E I)
    (hhead : (E.get η).block = I)
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ ms s :
      I.motiveType η ls ps l s) →
    E[Γ] ⊢ σ ⊣ Δ{ls} →
    E[Γ] ⊢ r : fd.instantiatedType η ls ps σ →
    E[Γ] ⊢ fd.ihType ls ms σ r typ := by
  intro hΓ hps hms hσ hr
  cases hhead
  have hΓtele := ((h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ).appendCtxWF hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk := Inductive.paramsWkN (Θ := fd.instantiatedTelescope ls σ) hps
  have hmsWk := Inductive.motivesWkN (Θ := fd.instantiatedTelescope ls σ) hms
  exact Ctx.pi_isType hΓtele
    (InductiveWF.motiveResult_congr (hB := hB) hΓtele
      (fun p => (hpsWk p).left)
      (fun s => (hmsWk s).left)
      (fun i => (his i).left)
      (Ctx.pi_applyBound hΓtele (.indDF hpsWk his) hr).left)

theorem RecFieldWF.ihType_congr (h : RecFieldWF E I Δ fd) (hB : InductiveWF E I)
    (hΔ : TeleWF E (fun _ => True) .nil Δ) (hhead : (E.get η).block = I)
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n} {l : Level ℓ}
    {σ₁ σ₂ : Subst ζ ℓ (ι.nparams + nfields) n}
    (hσparams : ∀ p, σ₁ (p.castAdd nfields) = ps₁ p) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s : I.motiveType η ls ps₁ l s) →
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Δ{ls} →
    E[Γ] ⊢ r : fd.instantiatedType η ls ps₁ σ₁ →
    ∃ u : Level ℓ,
    E[Γ] ⊢ fd.ihType ls ms₁ σ₁ r ≡
      fd.ihType ls ms₂ σ₂ r : .sort u := by
  intro hΓ hps hms hσ hr
  cases hhead
  have ⟨telescope, is⟩ := fd
  have ⟨htele, his⟩ := h
  have htele : TeleWF E (fun _ => True) Δ telescope :=
    htele.mono fun _ => trivial
  have hteleL := htele.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hΓtele := (hteleL.substitution hσ.left).appendCtxWF hΓ
  have hsource : TeleWF E (fun _ => True) .nil (Δ ++ telescope) :=
    hΔ.append (by simpa using htele)
  have hsourceL := hsource.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hlift : E[Γ ++ Ctx.substN σ₁ arity telescope{ls}] ⊢
      σ₁.liftN arity ≡ σ₂.liftN arity ⊣ (Δ ++ telescope){ls} := by
    simpa using SubstEq.liftN hteleL hσ
  have hpsEq :
      (fun p : Fin ι.nparams =>
        (Expr.var ⟨p.val, by omega⟩ :
          Expr ζ ℓ (ι.nparams + nfields + arity)).subst (σ₁.liftN arity)) =
        fun p => (ps₁ p).wkN arity := by
    funext p
    change (Expr.var ⟨p.val, by omega⟩ :
      Expr ζ ℓ (ι.nparams + nfields + arity)).subst (σ₁.liftN arity) = _
    rw [Expr.subst, show (⟨p.val, by omega⟩ :
      Fin (ι.nparams + nfields + arity)) =
        (p.castAdd nfields).castAdd arity by ext; rfl,
      Subst.liftN_castAdd, hσparams]
  have hpsWk := Inductive.paramsWkN
    (Θ := Ctx.substN σ₁ arity telescope{ls}) hps
  have hisWk (i) : E[Γ ++ Ctx.substN σ₁ arity telescope{ls}] ⊢
      (is i){ls}.subst (σ₁.liftN arity) ≡
      (is i){ls}.subst (σ₂.liftN arity) :
      (E.get η).block.indexType ls target
        (fun p => (ps₁ p).wkN arity)
        (fun i => (is i){ls}.subst (σ₁.liftN arity)) i := by
    simpa [hpsEq] using
      hsourceL.substitution_congr hlift ((his i).instLevel ls)
  have hind := Defeq.indDF
    (fun p => (hpsWk p).left)
    fun i => (hisWk i).left
  have hmsWk := Inductive.motivesWkN
    (Θ := Ctx.substN σ₁ arity telescope{ls}) hms
  exact TeleWF.pi_instL_substN_congr hΔ htele ls hσ
    (InductiveWF.motiveResult_congr hB hΓtele hpsWk hmsWk hisWk
      (Ctx.pi_applyBound hΓtele hind hr))

theorem RecFieldWF.iotaIH (h : RecFieldWF E I Δ fd) (hB : InductiveWF E I)
    (hhead : (E.get η).block = I)
    (hallowed : I.RecAllowed l)
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : I.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ ms s :
      I.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ mins s c :
      I.caseFnType η ls ps ms s c) →
    E[Γ] ⊢ σ ⊣ Δ{ls} →
    E[Γ] ⊢ r : fd.instantiatedType η ls ps σ →
    E[Γ] ⊢ fd.iotaIH η ls l ps ms mins σ r :
      fd.ihType ls ms σ r := by
  intro hΓ hps hms hmins hσ hr
  cases hhead
  have hΓtele := ((h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ).appendCtxWF hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk := Inductive.paramsWkN (Θ := fd.instantiatedTelescope ls σ) hps
  have hind := Defeq.indDF hpsWk his
  rw [RecField.instantiatedType] at hr
  have hmaj := Ctx.pi_applyBound hΓtele hind hr
  have hmsWk := Inductive.motivesWkN (Θ := fd.instantiatedTelescope ls σ) hms
  have hminsWk := Inductive.casesWkN (Θ := fd.instantiatedTelescope ls σ) hmins
  have hresult := InductiveWF.motiveResult_congr
    hB hΓtele
    (fun p => (hpsWk p).left)
    (fun s => (hmsWk s).left)
    (fun i => (his i).left)
    hmaj.left
  exact Ctx.lam_congr hΓtele (.recrDF hallowed hpsWk hmsWk hminsWk his hmaj hresult)

section

open Inductive

theorem InductiveWF.caseType_congr
    (hB : InductiveWF E (E.get η).block)
    {Γcase : Ctx ζ ℓ 0
      (n + (ι.ctors s c).nfields +
        (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields)} :
    E[Γcase] ⊢ ok →
    (∀ p, E[Γcase] ⊢ (ι.ctors s c).caseParams ps₁ p ≡
      (ι.ctors s c).caseParams ps₂ p :
      (E.get η).block.paramType ls
        ((ι.ctors s c).caseParams ps₁) p) →
    (∀ s₁, E[Γcase] ⊢ (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields :
      (E.get η).block.motiveType η ls
        ((ι.ctors s c).caseParams ps₁) l s₁) →
    (∀ f, E[Γcase] ⊢ (ι.ctors s c).caseOrdinary f :
        (((E.get η).block.ctors s c).ordinary f).type{ls}.subst (Fin.append
            ((ι.ctors s c).caseParams ps₁)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le))) →
    (∀ f, E[Γcase] ⊢ (ι.ctors s c).caseRecursive f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType
          η ls ((ι.ctors s c).caseParams ps₁)
            (Fin.append
              ((ι.ctors s c).caseParams ps₁)
              (ι.ctors s c).caseOrdinary)) →
    E[Γcase] ⊢ (E.get η).block.caseType η ls ps₁ ms₁ s c ≡
      (E.get η).block.caseType η ls ps₂ ms₂ s c : .sort l := by
  intro hΓcase hps hms hfields hrecFields
  have his := fun i =>
    (hB.ctors s c).targetIndex_congr hB.params i hps hfields
  have htarget := Defeq.indDF hps his
  have hordinary := fun f =>
    (hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps (fun g _ => hfields g)
  have hrecursive := fun f =>
    (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps hfields
  have hmaj := Defeq.ctorDF hps hfields hrecFields
    hordinary
    (fun f => (hrecursive f).choose_spec)
    htarget
  simpa [caseType] using hB.motiveResult_congr hΓcase hps hms his hmaj

theorem InductiveWF.motiveBinders
    {Γ : Ctx ζ ℓ 0 ι.nparams}
    (hB : InductiveWF E (E.get η).block)
    (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ Expr.var p :
      (E.get η).block.paramType ls Expr.var p) :
    TeleWF E (fun _ => True) Γ ((E.get η).block.motiveBinders η ls l) := by
  apply TeleWF.ofTypes
  intro s
  have htele := hB.motiveTele (s := s) hΓ hps
  have ⟨v, ht⟩ := Ctx.pi_isType (htele.appendCtxWF hΓ) (Defeq.sortDF (l := l))
  exact ⟨v, trivial, ht⟩

theorem InductiveWF.motiveBinders_var {Γ : Ctx ζ ℓ 0 ι.nparams} (hB : InductiveWF E (E.get η).block)
    (s : Fin ι.nsorts) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ Expr.var p :
      (E.get η).block.paramType ls Expr.var p) →
    E[Γ ++ (E.get η).block.motiveBinders η ls l] ⊢ Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun p => Expr.var (p.castLE (by omega))) l s := by
  intro hΓ hps
  have hv := ((hB.motiveBinders (l := l) hΓ hps).appendCtxWF hΓ).var (Fin.natAdd ι.nparams s)
  simp [Inductive.motiveBinders] at hv
  simpa [Inductive.motiveBinders, Fin.natAdd, Fin.castAdd] using hv

end

theorem CtorWF.ihTele (hctor : CtorWF E (E.get η).block ctor) (hB : InductiveWF E (E.get η).block)
    (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p)
    (hms : ∀ s₁, E[Γ] ⊢ ms s₁ : (E.get η).block.motiveType η ls ps l s₁) :
    TeleWF E (fun _ => True)
      (Γ ++ ctor.fieldTele η ls ps)
      (ctor.ihTele ls ps ms) := by
  apply TeleWF.ofTypes
  intro f
  have ⟨u, ht⟩ := (hctor.recursive f).ihType hB
    rfl
    (by simp)
    ((hctor.fieldTele rfl hΓ hps).appendCtxWF hΓ) (CtorWF.fieldParams ctor · hps)
    (CtorWF.fieldMotive ctor · hms) (hctor.fieldTargetSubst hps)
    (hctor.fieldRecursive f hΓ hps)
  exact ⟨u, trivial, ht⟩

theorem CtorWF.ihType_congr (hctor : CtorWF E (E.get η).block ctor)
    (hB : InductiveWF E (E.get η).block) (f : Fin csig.nrecFields) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps₁ l s₁) →
    ∃ u : Level ℓ,
    E[Γ ++ ctor.fieldTele η ls ps₁] ⊢
      ctor.ihType ls ps₁ ms₁ f ≡ ctor.ihType ls ps₂ ms₂ f : .sort u := by
  intro hΓ hps hms
  have hpsSelf (p) := (hps p).left
  have hΓfield := (hctor.fieldTele rfl hΓ hpsSelf).appendCtxWF hΓ
  have hordinaryTele : TeleWF E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ (E.get η).block.params)
      ctor.ordinaryTele := by
    simpa using
      (hctor.ordinaryTeleAux csig.nfields le_rfl).mono fun _ => trivial
  have hΔ := hB.params.append hordinaryTele
  have ⟨u, hih⟩ := (hctor.recursive f).ihType_congr hB hΔ
    rfl (by simp) hΓfield
    (CtorWF.fieldParams ctor · hps)
    (CtorWF.fieldMotive ctor · hms)
    (Ctor.forall_ordinarySubst le_rfl
      (CtorWF.fieldParams ctor · hps)
      (hctor.fieldOrdinary · hpsSelf))
    (hctor.fieldRecursive f hΓ hpsSelf)
  exact ⟨u, by simpa [Ctor.ihType, Ctor.ihTypeWith] using hih⟩

section

open Inductive

theorem InductiveWF.caseTele (hB : InductiveWF E (E.get η).block) (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p)
    (hms : ∀ s, E[Γ] ⊢ ms s : (E.get η).block.motiveType η ls ps l s) :
    TeleWF E (fun _ => True) Γ ((E.get η).block.caseTele η ls ps ms s c) := by
  simpa [Inductive.caseTele] using
    ((hB.ctors s c).fieldTele rfl hΓ hps).append ((hB.ctors s c).ihTele hB hΓ hps hms)

theorem Inductive.caseParams_congr
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢ (ι.ctors s c).caseParams ps₁ p ≡
        (ι.ctors s c).caseParams ps₂ p :
        (E.get η).block.paramType ls
          ((ι.ctors s c).caseParams ps₁) p := by
  intro hps
  have hp := (hps p).wkN
    (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps₁)
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
      (fun p => (ps₁ p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars n (ι.ctors s c).nfields 0))
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps₁ ms)
  change E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢
    (((ps₁ p).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ps₂ p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.paramType ls
      (fun p => (((ps₁ p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) p
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hp

theorem Inductive.caseMotives_congr
    (s₁ : Fin ι.nsorts) :
    (∀ s₁, E[Γ] ⊢ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps l s₁) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢ (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
        (E.get η).block.motiveType η ls
          ((ι.ctors s c).caseParams ps) l s₁ := by
  intro hms
  change E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢
    (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => (((ps p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) l s₁
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using (hms s₁).wkN.wkN.wkN

theorem InductiveWF.caseOrdinary_typed (hB : InductiveWF E (E.get η).block)
    (f : Fin (ι.ctors s c).nfields) :
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ (ι.ctors s c).caseOrdinary f :
        ((((E.get η).block.ctors s c).ordinary f).type{ls}).subst
          (Fin.append ((ι.ctors s c).caseParams ps)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le)) := by
  intro hps
  unfold CtorSig.caseOrdinary CtorSig.caseParams
  simpa [Inductive.caseTele, Tele.append_assoc, Expr.instL] using
    ((hB.ctors s c).fieldOrdinary f hps).wkN

theorem InductiveWF.caseRecursive_typed (hB : InductiveWF E (E.get η).block)
    (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ (ι.ctors s c).caseRecursive f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType η ls
          ((ι.ctors s c).caseParams ps)
          (Fin.append
            ((ι.ctors s c).caseParams ps)
            (ι.ctors s c).caseOrdinary) := by
  intro hΓ hps
  have hrecFieldsField := (hB.ctors s c).fieldRecursive f hΓ hps
  have hv := hrecFieldsField.wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms)
  rw [RecField.instantiatedType_wkN] at hv
  have hpsEq :
      (fun p => ((ι.ctors s c).fieldParams ps p).wkN
        (ι.ctors s c).nrecFields) =(ι.ctors s c).caseParams ps := rfl
  have hsubstEq :
      (fun v => (Fin.append
        ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary v).wkN (ι.ctors s c).nrecFields) =
        Fin.append ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary := by
    funext v
    cases v using Fin.addCases with
    | left p => simp [CtorSig.caseParams]
    | right fds => simp [CtorSig.caseOrdinary]
  rw [hpsEq, hsubstEq] at hv
  simpa [Tele.append_assoc, Inductive.caseTele, CtorSig.caseRecursive] using hv

theorem Inductive.caseFnType_congr (hB : InductiveWF E (E.get η).block) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps₁ l s₁) →
    E[Γ] ⊢ (E.get η).block.caseFnType η ls ps₁ ms₁ s c ≡
      (E.get η).block.caseFnType η ls ps₂ ms₂ s c typ := by
  intro hΓ hps hms
  have hpsSelf (p) := (hps p).left
  have hmsSelf (s₁) := (hms s₁).left
  have hΓcase := (hB.caseTele (c := c) hΓ hpsSelf hmsSelf).appendCtxWF hΓ
  have hcaseType := hB.caseType_congr hΓcase
    (fun p => caseParams_congr p hps)
    (fun s₁ => caseMotives_congr s₁ hms)
    (hB.caseOrdinary_typed · hpsSelf)
    (hB.caseRecursive_typed · hΓ hpsSelf)
  rw [caseTele, ← Tele.append_assoc] at hcaseType
  have ⟨u, hihs⟩ := Ctx.pi_ofTypes_congr
    (fun f => (hB.ctors s c).ihType_congr hB f hΓ hps hms) hcaseType
  have hpsWk (p) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ (ps₁ p).wkN (ι.ctors s c).nfields ≡
        (ps₂ p).wkN (ι.ctors s c).nfields :
      (E.get η).block.paramType ls
        (fun i => (ps₁ i).wkN (ι.ctors s c).nfields) p := by
    simpa using (hps p).wkN
      (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps₁)
  have hfields (f) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ Expr.boundVars n (ι.ctors s c).nfields 0 f :
        ((((E.get η).block.ctors s c).ordinary f).type{ls}).subst
          (Fin.append
            (fun p => (ps₁ p).wkN (ι.ctors s c).nfields)
            fun previous => Expr.boundVars n (ι.ctors s c).nfields 0
              (previous.castLE f.isLt.le)) := by
    have hv := (hB.ctors s c).boundOrdinarySubstWF (η := η) hpsSelf (Fin.natAdd ι.nparams f)
    rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL] at hv
    have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
      simp
    rw [Ctx.entry_append_right (E.get η).block.params _
      (by omega) hb (by omega)] at hv
    simpa using hv
  rw [Ctor.fieldTele, ← Tele.append_assoc] at hihs
  have ⟨v, hrec⟩ := Ctx.pi_ofTypes_congr
    (fun f => (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hpsWk hfields) hihs
  have ⟨_, hpi⟩ := TeleWF.pi_instL_substN_congr hB.params
    (((hB.ctors s c).ordinaryTeleAux (ι.ctors s c).nfields le_rfl).mono fun _ => trivial)
    ls (paramSubstEq hps) hrec
  exact TypeEq.ofDefEq <| by
    simpa [caseFnType, caseTele, Ctor.fieldTele, Ctx.pi, Tele.foldr_append]

theorem Inductive.caseFnType_conv
    (hB : InductiveWF E (E.get η).block) {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
    {mins₁ mins₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁) →
    E[Γ] ⊢ mins₁ ≡ mins₂ : (E.get η).block.caseFnType η ls ps₁ ms₁ s c →
    E[Γ] ⊢ mins₂ : (E.get η).block.caseFnType η ls ps₂ ms₂ s c :=
  fun hΓ hps hms hmin => (caseFnType_congr hB hΓ hps hms).conv hmin.right

theorem InductiveWF.caseBinders
    {Γ : Ctx ζ ℓ 0 (ι.nparams + ι.nsorts)}
    (hB : InductiveWF E (E.get η).block)
    (hΓ : E[Γ] ⊢ ok)
    (hps : ∀ p, E[Γ] ⊢ Expr.var (p.castLE (by omega)) :
      (E.get η).block.paramType ls
        (fun p => Expr.var (p.castLE (by omega))) p)
    (hms : ∀ s, E[Γ] ⊢ Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun p => Expr.var (p.castLE (by omega))) l s) :
    TeleWF E (fun _ => True) Γ ((E.get η).block.caseBinders η ls) := by
  apply TeleWF.ofTypes
  intro tag
  obtain ⟨⟨s, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
    ⟨_, Fin.encodeSigma_decodeSigma ..⟩
  have ⟨v, ht⟩ := (caseFnType_congr hB (c := c) hΓ hps hms).left
  rw [Fin.decodeSigma_encodeSigma]
  exact ⟨v, trivial, ht⟩

theorem InductiveWF.recrTele {s : Fin ι.nsorts} (hB : InductiveWF E (E.get η).block) :
    TeleWF E (fun _ => True) .nil ((E.get η).block.recrTele η s ls l) := by
  have hps := hB.params.instLevel (Q := fun _ => True) ls
    fun _ => trivial
  have hpsTele : TeleWF E (fun _ => True) .nil (E.get η).block.params{ls} := by
    simpa using hps
  have hΓparams : E[(E.get η).block.params{ls}] ⊢ ok := by
    simpa using hpsTele.appendCtxWF .nil
  have hparamVars (p : Fin ι.nparams) :
      E[(E.get η).block.params{ls}] ⊢ Expr.var p :
        (E.get η).block.paramType ls Expr.var p := by
    simpa using hΓparams.var p
  have hms := hB.motiveBinders (l := l) hΓparams hparamVars
  have hΓmotives := hms.appendCtxWF hΓparams
  have hparamMotives (p : Fin ι.nparams) :
      E[(E.get η).block.params{ls} ++
          (E.get η).block.motiveBinders η ls l] ⊢ Expr.var (p.castLE (by omega)) :
          (E.get η).block.paramType ls
            (fun p => Expr.var (p.castLE (by omega))) p := by
    simpa [Fin.castAdd] using (hparamVars p).wkN
      (Δ := (E.get η).block.motiveBinders η ls l)
  have hmins := hB.caseBinders hΓmotives hparamMotives
    (hB.motiveBinders_var · hΓparams hparamVars)
  have hΓcases := hmins.appendCtxWF hΓmotives
  let casesEnd := ι.nparams + ι.nsorts + Fin.sum ι.nctors
  let ps : Fin ι.nparams → Expr ζ ℓ casesEnd :=
    fun p => .var (p.castLE (by omega))
  have hparamCases (p : Fin ι.nparams) :
      E[(E.get η).block.params{ls} ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls] ⊢ ps p : (E.get η).block.paramType ls ps p := by
    simpa [Fin.castAdd] using (hparamMotives p).wkN
      (Δ := (E.get η).block.caseBinders η ls)
  have his := hB.indexTele (s := s) hparamCases
  have hΓindices := his.appendCtxWF hΓcases
  have hparamIndices (p : Fin ι.nparams) :
      E[(E.get η).block.params{ls} ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ (ps p).wkN (ι.nindices s) :
          (E.get η).block.paramType ls
            (fun p => (ps p).wkN (ι.nindices s)) p := by
    simpa using (hparamCases p).wkN
  have hindexVars (i : Fin (ι.nindices s)) :
      E[(E.get η).block.params{ls} ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ Expr.var ⟨casesEnd + i.val, by omega⟩ :
          (E.get η).block.indexType ls s
            (fun p => (ps p).wkN (ι.nindices s))
            (fun i => Expr.var ⟨casesEnd + i.val, by omega⟩) i := by
    have hv := hΓindices.var (Fin.natAdd casesEnd i)
    rw [Inductive.indexTele_get] at hv
    simpa [Fin.natAdd] using hv
  have hmaj := Defeq.indDF hparamIndices hindexVars
  have hpsMotives : TeleWF E (fun _ => True) .nil
      ((E.get η).block.params{ls} ++
        (E.get η).block.motiveBinders η ls l) :=
    hpsTele.append <| by simpa using hms
  have hminsTele : TeleWF E (fun _ => True)
      ((#t[] : Ctx ζ ℓ 0 0) ++
        ((E.get η).block.params{ls} ++
          (E.get η).block.motiveBinders η ls l))
      ((E.get η).block.caseBinders η ls) := by
    simpa using hmins
  have hpsMotivesCases := hpsMotives.append hminsTele
  have hisTele : TeleWF E (fun _ => True)
      ((#t[] : Ctx ζ ℓ 0 0) ++
        ((E.get η).block.params{ls} ++
        (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls))
      ((E.get η).block.indexTele ls s ps) := by
    simpa using his
  exact .snoc (hpsMotivesCases.append hisTele)
    ⟨(E.get η).block.level{ls}, trivial, by
      simpa [casesEnd, ps] using hmaj⟩

theorem InductiveWF.map (pre : E.as ⟶ E₂.as) (h : InductiveWF E I) :
    InductiveWF E₂ (I.map pre.sigs) where
  params := by simpa [Inductive.map] using h.params.map pre
  indices s := by simpa [Inductive.map] using (h.indices s).map pre
  ctors s c := by simpa [Inductive.map] using (h.ctors s c).map pre

theorem Inductive.iotaLhs_hasType
    {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ}
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Expr ζ ℓ n}
    (hctor : CtorWF E (E.get η).block ((E.get η).block.ctors s c))
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ ms s : (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ mins s c : (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ fds f :
      ((((E.get η).block.ctors s c).ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ Fin.append ps fds ⊣
      ((E.get η).block.params ++
        ((E.get η).block.ctors s c).ordinaryTele){ls} →
    E[Γ] ⊢ (E.get η).block.iotaType η ls ps ms s c fds recFds : .sort l →
    E[Γ] ⊢ (E.get η).block.iotaLhs η ls l ps ms mins s c fds recFds :
        (E.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hΓ hps hms hmins hfields hrecFields hσ hresult
  have his := fun i => hctor.targetIndex i hσ
  have hmaj := Defeq.ctorDF hps hfields hrecFields
    (fun f => hctor.ordinaryFieldExpr f hps hfields)
    (fun f => (hctor.recursiveFieldExpr rfl f hΓ hps hfields).choose_spec)
    (Defeq.indDF hps his)
  exact .recrDF hallowed hps hms hmins his hmaj hresult

theorem InductiveWF.iotaRhs_hasType {η : Head ζ (.inductive ι)} (hB : InductiveWF E (E.get η).block)
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) → Expr ζ ℓ n}
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ ok →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ ms s : (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ fds f :
      ((((E.get η).block.ctors s c).ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
        (E.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hΓ hps hms hmins hfields hrecFields
  have hfn : (E.get η).block.caseFnType η ls ps ms s c =
      Ctx.pi (Ctx.pi (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
          (((E.get η).block.ctors s c).ihTele ls ps ms))
        (((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0)))
        (((E.get η).block.ctors s c).ordinaryFieldTele η ls ps) := by
    unfold Inductive.caseFnType Inductive.caseTele Ctor.fieldTele Ctx.pi
    rw [Tele.foldr_append, Tele.foldr_append]
  have hΔord := (hB.ctors s c).ordinaryFieldTele (η := η) hps
  have hΓord := hΔord.appendCtxWF hΓ
  have hΔrec : TeleWF E (fun _ => True)
      (Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
      (((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0)) :=
    TeleWF.ofTypes fun f =>
      let ⟨u, ht⟩ := (hB.ctors s c).recursiveFieldType rfl f hΓ hps
      ⟨u, trivial, ht⟩
  have hΓrec := hΔrec.appendCtxWF hΓord
  have hΔih : TeleWF E (fun _ => True)
      (Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0))
      (((E.get η).block.ctors s c).ihTele ls ps ms) := by
    have h := (hB.ctors s c).ihTele hB hΓ hps hms
    rwa [show Γ ++ ((E.get η).block.ctors s c).fieldTele η ls ps =
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) from
      (Tele.append_assoc _ _ _).symm] at h
  have hΓcase := hΔih.appendCtxWF hΓrec
  have hcaseType : E[Γ ++
      ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) ++
        ((E.get η).block.ctors s c).ihTele ls ps ms] ⊢
      (E.get η).block.caseType η ls ps ms s c : .sort l := by
    have h := hB.caseType_congr ((hB.caseTele hΓ hps hms).appendCtxWF hΓ)
      (Inductive.caseParams_congr · hps)
      (Inductive.caseMotives_congr (c := c) · hms)
      (hB.caseOrdinary_typed · hps)
      (hB.caseRecursive_typed · hΓ hps)
    rwa [show Γ ++ (E.get η).block.caseTele η ls ps ms s c =
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) ++
        ((E.get η).block.ctors s c).ihTele ls ps ms by
      unfold Inductive.caseTele Ctor.fieldTele
      simp only [Tele.append_assoc]] at h
  have htA : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps] ⊢
      Ctx.pi (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
          (((E.get η).block.ctors s c).ihTele ls ps ms))
        (((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0)) typ := by
    have h := Ctx.pi_isType
      (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0) ++
          ((E.get η).block.ctors s c).ihTele ls ps ms)
      (by rw [← Tele.append_assoc]; exact hΓcase)
      (by rw [← Tele.append_assoc]; exact hcaseType)
    unfold Ctx.pi at h ⊢
    rwa [Tele.foldr_append] at h
  have hxsA : ∀ p : Fin (ι.ctors s c).nfields, E[Γ] ⊢ fds p :
      ((((E.get η).block.ctors s c).ordinaryFieldTele η ls ps).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          fds (previous.castLE p.isLt.le)) := by
    intro p
    rw [Ctor.ordinaryFieldTele]
    simpa [Expr.boundVars, Expr.subst] using hfields p
  have hA := Ctx.pi_applyFamily (P := fun _ => True) hΓ hΔord htA hxsA (hfn ▸ hmins s c)
  have hΔrecSubst : Ctx.substN (Fin.append Subst.id fds)
      (ι.ctors s c).nrecFields
      (((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0)) =
      ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds := by
    simp [Expr.boundVars, Expr.subst]
  rw [Ctx.pi_subst, hΔrecSubst] at hA
  have hσA : E[Γ] ⊢ Fin.append Subst.id fds ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps :=
    TeleWF.extendFamily hΔord (fun v => by rw [Expr.subst_id]; exact hΓ.var v) hxsA
  have hΔrecWF : TeleWF E (fun _ => True) Γ
      (((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds) := by
    have h := hΔrec.substitution hσA
    rwa [hΔrecSubst] at h
  have hσAlift : E[Γ ++ ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds] ⊢
      Subst.liftN (Fin.append Subst.id fds) (ι.ctors s c).nrecFields ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) := by
    have h := SubstWF.liftN hΔrec hσA
    rwa [hΔrecSubst] at h
  have htB : E[Γ ++ ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds] ⊢
      (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
        (((E.get η).block.ctors s c).ihTele ls ps ms)).subst
        (Subst.liftN (Fin.append Subst.id fds) (ι.ctors s c).nrecFields) typ :=
    have ⟨u, h⟩ := Ctx.pi_isType hΓcase hcaseType
    ⟨u, h.substitution hσAlift⟩
  have hxsB : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ recFds f :
      ((((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          recFds (previous.castLE f.isLt.le)) := by
    intro f
    rw [Ctor.recursiveFieldTele, Ctor.recursiveFieldTeleAux, Ctx.entry_ofTypes,
      Expr.wkN_subst_id_append]
    exact hrecFields f
  have hB' := Ctx.pi_applyFamily (P := fun _ => True) hΓ hΔrecWF htB hxsB hA
  rw [Expr.subst_subst, Subst.liftN_comp_append, Subst.comp_id, Ctx.pi_subst] at hB'
  have hxsB' : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ recFds f :
      ((((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0)).entry
        (by omega) (by omega)).subst
        (Fin.append (Fin.append Subst.id fds) fun previous =>
          recFds (previous.castLE f.isLt.le)) := by
    intro f
    rw [Ctor.recursiveFieldTele, Ctor.recursiveFieldTeleAux, Ctx.entry_ofTypes,
      Expr.wkN_subst_append]
    simpa [Expr.boundVars, Expr.subst] using hrecFields f
  have hσAB : E[Γ] ⊢ Fin.append (Fin.append Subst.id fds) recFds ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) :=
    TeleWF.extendFamily hΔrec hσA hxsB'
  have hxsC : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢
      (E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds f :
      ((Ctx.substN (Fin.append (Fin.append Subst.id fds) recFds) (ι.ctors s c).nrecFields
            (((E.get η).block.ctors s c).ihTele ls ps ms)).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          (E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds
            (previous.castLE f.isLt.le)) := by
    intro f
    rw [Ctx.entry_substN _ _ _ f.val (by omega) (by omega) (by omega) (by omega), Ctor.ihTele,
      Ctx.entry_ofTypes, Ctor.ihType]
    simpa [iotaIHs, Ctor.iotaIH, Ctor.ihTypeWith, CtorSig.fieldParams, CtorSig.fieldOrdinary,
      CtorSig.fieldRecursive, Expr.subst] using
      ((hB.ctors s c).recursive f).iotaIH hB rfl hallowed (by simp) hΓ hps hms hmins
        (Ctor.forall_ordinarySubst le_rfl hps hfields) (hrecFields f)
  have hC := Ctx.pi_applyFamily (P := fun _ => True) hΓ (hΔih.substitution hσAB)
    ⟨l, hcaseType.substitution (SubstWF.liftN hΔih hσAB)⟩ hxsC hB'
  simp at hC
  change E[Γ] ⊢ (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
    ((E.get η).block.caseType η ls ps ms s c).subst
      ((ι.ctors s c).caseSubst fds recFds
        ((E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds)) at hC
  simpa! [caseType, iotaType] using hC

end

end Recursor

variable {ζ₁ ζ₂ : Sigs} {ι : IndSig}

def Inductive.ctorTypeFn (I : Inductive ζ ι) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Expr ζ ι.nlevels 0 :=
  I.params.lam ((I.ctors s c).ordinaryTele.pi (.sort I.level))

@[simp] theorem Inductive.ctorTypeFn_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.ctorTypeFn s c).map pre = (I.map pre).ctorTypeFn s c := by
  simp! [ctorTypeFn, map]

theorem InductiveWF.ctorTypeFn {I : Inductive ζ ι} (hI : InductiveWF E I)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    ∃ u, E[(#t[] : Ctx ζ ι.nlevels 0 0)] ⊢ I.ctorTypeFn s c : I.params.pi (.sort u) :=
  have hparams : E[I.params] ⊢ ok := by
    simpa using hI.params.appendCtxWF .nil
  have hfields :=
    ((hI.ctors s c).ordinaryTeleAux _ le_rfl).appendCtxWF hparams
  have ⟨u, ht⟩ := Ctx.pi_isType hfields (.sortDF (l := I.level))
  ⟨u, Ctx.lam_congr (by simpa using hparams) (by simpa using ht)⟩

end Metalean
