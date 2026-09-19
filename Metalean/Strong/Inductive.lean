/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Context
import Metalean.Strong.InstLevel
import Metalean.Strong.Substitution
import Metalean.Strong.Telescope
import Metalean.Strong.WeakenEnv
import Metalean.Syntax.Substitution
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {sig : Sig} {E : Env ζ} {ℓ n m : Nat}
  {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}

theorem WFTeleStrong.mono {P Q : Level ℓ → Prop}
    (hPQ : ∀ {u}, P u → Q u) (hΔ : WFTeleStrong E P Γ Δ) :
    WFTeleStrong E Q Γ Δ := by
  induction hΔ with
  | nil => exact .nil
  | snoc _ ht ih =>
    have ⟨u, hu, ht⟩ := ht
    exact .snoc ih ⟨u, hPQ hu, ht⟩

theorem WFTele.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t)
    {P : Level ℓ → Prop} :
    E[Γ] ⊢ₛ ok →
    WFTele E P Γ Δ →
    WFTeleStrong E P Γ Δ := by
  intro hΓ hΔ
  induction hΔ with
  | nil => exact .nil
  | snoc _ ht ih =>
    have ⟨_, ht, hu⟩ := ht
    exact .snoc ih ⟨_, hu, tr ht (ih.appendCtxWFStrong hΓ)⟩

theorem WFTeleStrong.instLevel {P : Level ℓ → Prop}
    {ℓ' : Nat} {Q : Level ℓ' → Prop} (levelSubst : Param ℓ → Level ℓ')
    (hPQ : ∀ {u}, P u → Q (u.inst levelSubst)) (hΔ : WFTeleStrong E P Γ Δ) :
    WFTeleStrong E Q (Γ.instL levelSubst) (Δ.instL levelSubst) := by
  induction hΔ with
  | nil => exact .nil
  | @snoc b Δ t _ ht ih =>
    have ⟨u, hu, ht⟩ := ht
    refine .snoc ih ⟨u.inst levelSubst, hPQ hu, ?_⟩
    have ht := ht.instLevel levelSubst
    rw [Ctx.instL_append] at ht
    change E[Ctx.instL levelSubst Γ ++ Ctx.instL levelSubst Δ] ⊢ₛ
      Expr.instL levelSubst t : .sort (u.inst levelSubst)
    simpa [Expr.instL] using ht

theorem WFTeleStrong.get_instL_subst_congr {ℓ' : Nat} {P : Level ℓ' → Prop}
    {Θ : Ctx ζ ℓ' 0 m} {σ₁ σ₂ : Subst ζ ℓ m n}
    (hΘ : WFTeleStrong E P .nil Θ)
    (ls : Param ℓ' → Level ℓ)
    (v : Var m) :
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ Ctx.instL ls Θ →
    ∃ u : Level ℓ,
    E[Γ] ⊢ₛ ((Θ.get v).instL ls).subst σ₁ ≡
      ((Θ.get v).instL ls).subst σ₂ : .sort u := by
  intro hσ
  have hΘctx : E[Θ] ⊢ₛ ok := by
    simpa using hΘ.appendCtxWFStrong .nil
  have ⟨u, hu⟩ := hΘctx.get v
  have hΘ' : WFTeleStrong E (fun _ : Level ℓ => True) .nil (Ctx.instL ls Θ) :=
    hΘ.instLevel (Q := fun _ => True) ls fun _ => trivial
  have h := hu.instLevel ls
  exact ⟨_, hΘ'.substitution_congr hσ (by simpa using h)⟩

theorem WFTeleStrong.pi_instL_substN_congr {ℓ' a k : Nat} {P : Level ℓ' → Prop}
    {Γ₀ : Ctx ζ ℓ' 0 a} {Θ : Ctx ζ ℓ' a (a + k)}
    {σ₁ σ₂ : Subst ζ ℓ a n} {e₁ e₂ : Expr ζ ℓ (n + k)} {l : Level ℓ}
    (hΓ₀ : WFTeleStrong E P .nil Γ₀) (hΘ : WFTeleStrong E P Γ₀ Θ)
    (ls : Param ℓ' → Level ℓ) :
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ Ctx.instL ls Γ₀ →
    E[Γ ++ Ctx.substN σ₁ k (Ctx.instL ls Θ)] ⊢ₛ e₁ ≡ e₂ : .sort l →
    ∃ u : Level ℓ,
    E[Γ] ⊢ₛ Ctx.pi e₁ (Ctx.substN σ₁ k (Ctx.instL ls Θ)) ≡
      Ctx.pi e₂ (Ctx.substN σ₂ k (Ctx.instL ls Θ)) : .sort u := by
  intro hσ he
  induction Θ using Tele.addInduction generalizing l with
  | nil =>
    exact ⟨l, by simpa using he⟩
  | snoc k Θ t ih =>
    have .snoc hΘ ⟨u, _, ht⟩ := hΘ
    have hΘ : WFTeleStrong E P Γ₀ Θ := hΘ
    have hclosed : WFTeleStrong E P .nil (Γ₀ ++ Θ) :=
      hΓ₀.append (by simpa using hΘ)
    have hclosed' : WFTeleStrong E (fun _ : Level ℓ => True) .nil
        (Ctx.instL ls (Γ₀ ++ Θ)) :=
      hclosed.instLevel (Q := fun _ => True) ls fun _ => trivial
    have hlevel := ht.instLevel ls
    have hlift : E[Γ ++ Ctx.substN σ₁ k (Ctx.instL ls Θ)] ⊢ₛ σ₁.liftN k ≡ σ₂.liftN k ⊣
        Ctx.instL ls (Γ₀ ++ Θ) := by
      rw [Ctx.instL_append]
      exact SubstEqStrong.liftN
        (hΘ.instLevel (Q := fun _ : Level ℓ => True) ls fun _ => trivial) hσ
    have htype := hclosed'.substitution_congr hlift
      (by simpa using hlevel)
    have hbody : E[(Γ ++ Ctx.substN σ₁ k (Ctx.instL ls Θ)).snoc
        ((t.instL ls).subst (σ₁.liftN k))] ⊢ₛ e₁ ≡ e₂ : .sort l := by
      simpa [Ctx.instL, Ctx.substN] using he
    exact ih hΘ (.forallEDF htype hbody (htype.snocConv hbody))

theorem WFTeleStrong.weakenEnv {P : Level ℓ → Prop}
    {entry : Entry ζ sig} {T : Ctx ζ ℓ n m}
    (h : WFTeleStrong E P Γ T) :
    WFTeleStrong (E.snoc entry) P Γ.weakenEnv T.weakenEnv := by
  change WFTeleStrong (E.snoc entry) P
    (Γ.map (.step .refl)) (T.map (.step .refl))
  induction h with
  | nil => exact .nil
  | snoc hT ht ih =>
    have ⟨u, hu, ht⟩ := ht
    have ht := ht.weakenEnv entry
    exact .snoc ih ⟨u, hu,
      congr(_[$(Ctx.map_append (.step .refl) Γ _)] ⊢ₛ _ ≡ _ : _).mp ht⟩

namespace Inductive

variable {ι : IndSig} {I : Inductive ζ ι} {s : Fin ι.nsorts}
  {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n}
  {is : Fin (ι.nindices s) → Expr ζ ℓ n}

theorem paramSubstEqStrong {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ ps₁ ≡ ps₂ ⊣ Ctx.instL ls I.params := by
  intro hps v
  rw [← Ctx.get_instL, I.paramType_eq_get_subst ls ps₁ v]
  exact hps v

theorem IdxWF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t)
    (hΓ : E[Γ] ⊢ₛ ok)
    (h : I.IdxWF E Γ s ls ps is) :
    I.IdxWFStrong E Γ s ls ps is :=
  fun index => tr (h index) hΓ

theorem IdxWFStrong.instLevel {ℓ' : Nat}
    (h : I.IdxWFStrong E Γ s ls ps is)
    (levelSubst : Param ℓ → Level ℓ') :
    I.IdxWFStrong E (Γ.instL levelSubst) s (fun i => (ls i).inst levelSubst)
      (fun i => (ps i).instL levelSubst) fun i => (is i).instL levelSubst := by
  intro index
  simpa using (h index).instLevel levelSubst

theorem IdxWFStrong.weakenEnv
    {entry : Entry ζ sig}
    (h : I.IdxWFStrong E Γ s ls ps is) :
    (I.map (.step .refl)).IdxWFStrong (E.snoc entry) Γ.weakenEnv s ls
      (fun p => (ps p).weakenEnv)
      fun index => (is index).weakenEnv := by
  intro index
  simpa [Expr.weakenEnv] using
    (h index).weakenEnv entry

end Inductive

namespace Field

variable {ι : IndSig} {I : Inductive ζ ι} {nfields : Nat}
  {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)} {fd : Field ζ ι nfields}

theorem WFStrong.type {fd : Field ζ ι nfields} :
    fd.WFStrong E I Γ →
    E[Γ] ⊢ₛ fd.type typ
  | ⟨htype, _⟩ => ⟨_, htype⟩

theorem WF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t) :
    E[Γ] ⊢ₛ ok →
    fd.WF E I Γ →
    fd.WFStrong E I Γ
  | hΓ, ⟨htype, hlevel⟩ => ⟨tr htype hΓ, hlevel⟩

theorem WFStrong.weakenEnv {entry : Entry ζ sig} :
    fd.WFStrong E I Γ →
    (fd.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) Γ.weakenEnv
  | ⟨htype, hlevel⟩ =>
    ⟨by simpa [Expr.weakenEnv, Expr.map, map] using htype.weakenEnv entry, hlevel⟩

end Field

namespace RecField

variable {ι : IndSig} {I : Inductive ζ ι} {nfields arity : Nat}
  {s target : Fin ι.nsorts} {fd : RecField ζ ι nfields arity target}
  {Γ Δ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
  {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n}
  {σ : Subst ζ ℓ (ι.nparams + nfields) n}

theorem WF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t) :
    E[Γ] ⊢ₛ ok →
    fd.WF E I Γ →
    fd.WFStrong E I Γ
  | hΓ, ⟨htele, his⟩ =>
    let htele := htele.toStrong tr hΓ
    ⟨htele, his.toStrong tr (htele.appendCtxWFStrong hΓ)⟩

theorem WFStrong.weakenEnv {entry : Entry ζ sig} :
    fd.WFStrong E I Γ →
    (fd.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) Γ.weakenEnv
  | ⟨htele, his⟩ =>
    ⟨htele.weakenEnv,
      congr(Inductive.IdxWFStrong _ _ $(Ctx.map_append (.step .refl) Γ _) _ _ _ _).mp
        (his.weakenEnv (entry := entry))⟩

theorem WFStrong.instantiatedTelescope
    {fd : RecField ζ ι nfields arity s}
    (h : fd.WFStrong E I Δ)
    {Γ : Ctx ζ ℓ 0 n}
    {P : Level ℓ → Prop}
    (hls : ∀ {level}, I.LevelOK level → P (level.inst ls))
    (hσ : E[Γ] ⊢ₛ σ ⊣ Δ.instL ls) :
    WFTeleStrong E P Γ (fd.instantiatedTelescope ls σ) :=
  (h.tele.instLevel ls hls).substitution hσ

theorem WFStrong.instantiatedIndices
    {fd : RecField ζ ι nfields arity s}
    (h : fd.WFStrong E I Δ)
    {Γ : Ctx ζ ℓ 0 n}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p)
    (index) :
    E[Γ] ⊢ₛ σ ⊣ Δ.instL ls →
    E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ fd.instantiatedIndices ls σ index :
      I.indexType ls s (fun p => (ps p).wkN arity)
        (fd.instantiatedIndices ls σ) index := by
  intro hσ
  have ⟨htele, his⟩ := h
  have htele := htele.instLevel (Q := fun _ => True) ls
    fun _ => trivial
  have hσLift := SubstWFStrong.liftN htele hσ
  have his := his.instLevel ls
  rw [Ctx.instL_append] at his
  have hi := (his index).substitution hσLift
  have hpsEq :
      (fun p : Fin ι.nparams =>
        (Expr.var ⟨p.val, by omega⟩ : Expr ζ ℓ _).subst (σ.liftN arity)) =
        fun p => (ps p).wkN arity := by
    funext p
    rw [Expr.subst, show (⟨p.val, by omega⟩ :
      Fin (ι.nparams + nfields + arity)) =
        (p.castAdd nfields).castAdd arity by ext; rfl,
      Subst.liftN_castAdd, hσparams]
  simp [Expr.instL] at hi
  rwa [hpsEq] at hi

theorem WFStrong.instantiatedType
    {η : Head ζ (.inductive ι)}
    (h : fd.WFStrong E I Δ) (hhead : (E.get η).block = I)
    {Γ₁ : Ctx ζ ℓ 0 n}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ₁] ⊢ₛ ok →
    (∀ p, E[Γ₁] ⊢ₛ ps p : I.paramType ls ps p) →
    E[Γ₁] ⊢ₛ σ ⊣ Δ.instL ls →
    E[Γ₁] ⊢ₛ fd.instantiatedType η ls ps σ typ := by
  intro hΓ hps hσ
  cases hhead
  have ⟨telescope, is⟩ := fd
  have htele' := h.instantiatedTelescope (ls := ls) (P := fun _ => True)
    (fun _ => trivial) hσ
  have hΓtele := htele'.appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk p :
      E[Γ₁ ++ Ctx.substN σ arity (telescope.instL ls)] ⊢ₛ
        (ps p).wkN arity ≡ (ps p).wkN arity :
          (E.get η).block.paramType ls
            (fun p => (ps p).wkN arity) p := by
    simpa using (hps p).wkN
      (Δ := Ctx.substN σ arity (telescope.instL ls))
  exact Ctx.pi_isTypeStrong hΓtele <|
      DefeqStrong.indDF (E := E)
      (Γ := Γ₁ ++ Ctx.substN σ arity (telescope.instL ls))
      (η := η) (s := target)
      (ls := ls)
      (ps₁ := fun p => (ps p).wkN arity)
      (ps₂ := fun p => (ps p).wkN arity)
      (is₁ := fun i => ((is i).instL ls).subst (σ.liftN arity))
      (is₂ := fun i => ((is i).instL ls).subst (σ.liftN arity))
      hpsWk his

theorem WFStrong.recursiveIndex
    {telescope : Ctx ζ ι.nlevels (ι.nparams + nfields)
      (ι.nparams + nfields + arity)}
    {is : Fin (ι.nindices s) →
      Expr ζ ι.nlevels (ι.nparams + nfields + arity)}
    (h : RecField.WFStrong E I Δ ⟨telescope, is⟩)
    {ls : Fin ι.nlevels → Level ℓ} (index) :
    E[Ctx.instL ls Δ ++ Ctx.instL ls telescope] ⊢ₛ
      (is index).instL ls :
        I.indexType ls s
          (fun param => .var ⟨param.val, by omega⟩)
          (fun i => (is i).instL ls) index := by
  have hi := h.indices.instLevel ls index
  simpa [Expr.instL] using hi

end RecField

section Constructors

variable {ι : IndSig} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ ι s csig}
  {ls : Fin ι.nlevels → Level ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
  {fds fds₁ fds₂ : Fin csig.nfields → Expr ζ ℓ n}

namespace Ctor

private theorem WF.ordinaryToStrongAux
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t)
    (h : ctor.WF E I)
    (hps : WFTeleStrong E (fun _ => True) .nil I.params)
    (count : Nat) (hcount : count ≤ csig.nfields) :
    (∀ f : Fin count,
      Field.WFStrong E I
        (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
        (ctor.ordinary (f.castLE hcount))) ∧
    WFTeleStrong E (fun _ => True) I.params
      (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact ⟨fun f => Fin.elim0 f, .nil⟩
  | succ count ih =>
    have ⟨hfields, htele⟩ := ih (by omega)
    have hΓparams : E[I.params] ⊢ₛ ok := by
      simpa using hps.appendCtxWFStrong .nil
    have hΓ := htele.appendCtxWFStrong hΓparams
    have hfield := (h.ordinary ⟨count, by omega⟩).toStrong tr hΓ
    constructor
    · intro f
      cases f using Fin.lastCases with
      | last => exact hfield
      | cast f => exact hfields f
    · have ⟨u, htype⟩ := hfield.type
      exact .snoc htele ⟨u, trivial, htype⟩

theorem WF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t)
    (hps : WFTeleStrong E (fun _ => True) .nil I.params)
    (h : ctor.WF E I) :
    ctor.WFStrong E I := by
  have ⟨hfields, hfieldTele⟩ := h.ordinaryToStrongAux tr hps
    csig.nfields le_rfl
  have hΓparams : E[I.params] ⊢ₛ ok := by
    simpa using hps.appendCtxWFStrong .nil
  have hΓfields := hfieldTele.appendCtxWFStrong hΓparams
  exact {
    ordinary := hfields
    recursive := fun f => (h.recursive f).toStrong tr hΓfields
    targetIndices := h.targetIndices.toStrong tr hΓfields
  }

theorem WFStrong.weakenEnv
    {entry : Entry ζ sig} (h : ctor.WFStrong E I) :
    (ctor.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) where
  ordinary f :=
    congr(Field.WFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTeleAux_map (.step .refl) ctor f.val _))) _).mp
      ((h.ordinary f).weakenEnv (entry := entry))
  recursive f :=
    congr(RecField.WFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTele_map (.step .refl) ctor))) _).mp
      ((h.recursive f).weakenEnv (entry := entry))
  targetIndices :=
    congr(Inductive.IdxWFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTele_map (.step .refl) ctor))) _ _ _ _).mp
      (h.targetIndices.weakenEnv (entry := entry))

theorem ordinarySubstWFStrong
    {count : Nat} (hcount : count ≤ csig.nfields)
    {previous : Fin count → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f : Fin count,
      E[Γ] ⊢ₛ previous f :
        ((ctor.ordinaryType (f.castLE hcount)).instL ls).subst
          (Fin.append ps fun earlier : Fin f.val =>
            previous (earlier.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ Fin.append ps previous ⊣
      Ctx.instL ls (I.params ++
        ctor.ordinaryTeleAux count hcount) := by
  intro hps hprevious v
  rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
  cases v using Fin.addCases with
  | left param =>
    simpa [Inductive.paramType] using
      hps param
  | right f =>
    have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
      simp
    rw [Ctx.entry_append_right I.params _ (by omega) hb (by omega)]
    simpa using hprevious f

theorem targetSubstWFStrong
    {fds : Fin csig.nfields → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) :=
  ordinarySubstWFStrong le_rfl

theorem WFStrong.ordinaryFieldExprStrong (hctor : ctor.WFStrong E I)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.ordinaryFieldExpr ls ps fds f :
      .sort ((ctor.ordinary f).level.inst ls) := by
  intro hps hfields
  have hσ := ordinarySubstWFStrong (ctor := ctor) f.isLt.le hps
    (previous := fun previous : Fin f.val =>
      fds (previous.castLE f.isLt.le))
    fun prior => hfields (prior.castLE f.isLt.le)
  have htype := ((hctor.ordinary f).typeExact.instLevel ls).substitution hσ
  simpa [Ctor.ordinaryFieldExpr, Ctor.ordinaryType, Expr.instL] using htype

theorem WFStrong.recursiveFieldExprStrong (hctor : ctor.WFStrong E I)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.recursiveFieldExpr η ls ps fds f typ :=
  fun hΓ hps hfields =>
    (hctor.recursive f).instantiatedType hhead (by simp) hΓ hps
      (targetSubstWFStrong (ctor := ctor) hps hfields)

private theorem WFStrong.ordinaryTeleAux
    (h : ctor.WFStrong E I)
    (count : Nat) (hcount : count ≤ csig.nfields) :
    WFTeleStrong E I.LevelOK I.params
      (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    have hfield := h.ordinary ⟨count, by omega⟩
    exact .snoc (ih (by omega))
      ⟨_, hfield.levelOK, hfield.typeExact⟩

private theorem WFStrong.ordinaryFieldTeleAux
    (h : ctor.WFStrong E I)
    {Q : Level ℓ → Prop}
    (hls : ∀ {level}, I.LevelOK level → Q (level.inst ls))
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p)
    (count : Nat) (hcount : count ≤ csig.nfields) :
    WFTeleStrong E Q Γ
      (ctor.ordinaryFieldTeleAux η ls ps count hcount) := by
  have hσ := (Inductive.paramSubstEqStrong hps).left
  have htele := (h.ordinaryTeleAux count hcount).instLevel
    (Q := Q) ls hls
  have htele := htele.substitution hσ
  exact htele

theorem WFStrong.ordinaryFieldTele
    (h : ctor.WFStrong E I)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) :
    WFTeleStrong E (fun _ => True) Γ
      (ctor.ordinaryFieldTele η ls ps) :=
  h.ordinaryFieldTeleAux (fun _ => trivial) hps
    csig.nfields le_rfl

theorem WFStrong.boundOrdinarySubstWFStrong
    (h : ctor.WFStrong E I)
    {ps : Fin ι.nparams → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ
      Fin.append (fun p => (ps p).wkN csig.nfields)
        (Expr.boundVars n csig.nfields 0) ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) := by
  intro hps
  have hσ := (Inductive.paramSubstEqStrong hps).left
  have hfields := (h.ordinaryTeleAux csig.nfields le_rfl).instLevel
    (Q := fun _ => True) ls fun _ => trivial
  have hσ := SubstWFStrong.liftN hfields hσ
  simpa [Ctor.ordinaryFieldTele, Ctor.ordinaryFieldTeleAux, Subst.liftN_eq_append] using hσ

private theorem WFStrong.recursiveFieldType
    (h : ctor.WFStrong E I)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ
      (ctor.recursive f).instantiatedType η ls
        (fun p => (ps p).wkN csig.nfields)
        (Fin.append (fun p => (ps p).wkN csig.nfields)
          fun fds => .var ⟨n + fds.val, by omega⟩) typ :=
  fun hΓ hps =>
    have htele := h.ordinaryFieldTeleAux (Q := fun _ => True)
      (fun _ => trivial) hps
      csig.nfields le_rfl
    (h.recursive f).instantiatedType hhead (by simp)
      (htele.appendCtxWFStrong hΓ)
      (fun p => by simpa using (hps p).wkN)
      (h.boundOrdinarySubstWFStrong hps)

theorem WFStrong.fieldTele
    (h : ctor.WFStrong E I)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p)
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    WFTeleStrong E (fun _ => True) Γ
      (ctor.fieldTele η ls ps stop) := by
  refine (h.ordinaryFieldTeleAux (Q := fun _ => True) (fun _ => trivial)
    hps csig.nfields le_rfl).append ?_
  apply WFTeleStrong.ofTypes
  intro f
  have ⟨u, ht⟩ := h.recursiveFieldType hhead (f.castLE (Nat.le_of_lt_succ stop.isLt)) hΓ hps
  exact ⟨u, trivial, ht⟩

theorem WFStrong.targetIndex
    (h : ctor.WFStrong E I)
    (index : Fin (ι.nindices s)) :
    E[Γ] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) →
    E[Γ] ⊢ₛ ctor.targetIndex ls ps fds index :
      I.indexType ls s ps
        (fun i => ctor.targetIndex ls ps fds i) index := by
  intro hσ
  have hpsEq :
      (fun param : Fin ι.nparams =>
        ((Expr.var ⟨param.val, by omega⟩ :
          Expr ζ ι.nlevels (ι.nparams + csig.nfields)).instL ls).subst
            (Fin.append ps fds)) = ps :=
    funext (Fin.append_left ps fds)
  simpa [Ctor.targetIndex, hpsEq] using
    ((h.targetIndices index).instLevel ls).substitution hσ

theorem WFStrong.targetIndex_congr
    (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (index : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.targetIndex ls ps₁ fds₁ index ≡
      ctor.targetIndex ls ps₂ fds₂ index :
      I.indexType ls s ps₁
        (fun i => ctor.targetIndex ls ps₁ fds₁ i) index := by
  intro hps hfields
  have hfieldsTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params) ctor.ordinaryTele := by
    simpa using
      (h.ordinaryTeleAux csig.nfields le_rfl).mono
        fun _ => trivial
  have hsource := hBparams.append hfieldsTele
  have hsource := hsource.instLevel (Q := fun _ => True)
    ls fun _ => trivial
  have hσ : E[Γ] ⊢ₛ Fin.append ps₁ fds₁ ≡ Fin.append ps₂ fds₂ ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) := by
    intro v
    rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
    cases v using Fin.addCases with
    | left p =>
      simpa [Inductive.paramType] using hps p
    | right f =>
      have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
        simp
      rw [Ctx.entry_append_right I.params _ (by omega) hb (by omega)]
      simpa using hfields f
  have hpsEq :
      (fun param : Fin ι.nparams =>
        ((Expr.var ⟨param.val, by omega⟩ :
          Expr ζ ι.nlevels (ι.nparams + csig.nfields)).instL ls).subst
            (Fin.append ps₁ fds₁)) = ps₁ := by
    funext param
    exact Fin.append_left ps₁ fds₁ param
  simpa [Ctor.targetIndex, hpsEq] using
    hsource.substitution_congr hσ ((h.targetIndices index).instLevel ls)

end Ctor

theorem RecField.WFStrong.instantiatedType_congr
    {nfields arity : Nat} {target : Fin ι.nsorts}
    {fd : RecField ζ ι nfields arity target}
    {Θ : Ctx ζ ι.nlevels ι.nparams
      (ι.nparams + nfields)}
    (hfield : fd.WFStrong E I (I.params ++ Θ))
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (hsource : WFTeleStrong E (fun _ => True) .nil
      (I.params ++ Θ))
    (hhead : (E.get η).block = I)
    {σ₁ σ₂ : Subst ζ ℓ (ι.nparams + nfields) n}
    (hps₁ : ∀ p, σ₁ (p.castAdd nfields) = ps₁ p)
    (hps₂ : ∀ p, σ₂ (p.castAdd nfields) = ps₂ p) :
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ Ctx.instL ls (I.params ++ Θ) →
    ∃ u : Level ℓ, E[Γ] ⊢ₛ fd.instantiatedType η ls ps₁ σ₁ ≡
      fd.instantiatedType η ls ps₂ σ₂ : .sort u := by
  intro hσ
  let psId (p : Fin ι.nparams) : Expr ζ ι.nlevels (ι.nparams + nfields) :=
    .var (p.castAdd nfields)
  have hΔ : E[I.params ++ Θ] ⊢ₛ ok := by
    simpa using hsource.appendCtxWFStrong .nil
  have hpsCtx : E[I.params] ⊢ₛ ok := by
    simpa using hBparams.appendCtxWFStrong .nil
  have hpsId (p) : E[I.params ++ Θ] ⊢ₛ psId p :
      I.paramType .param psId p := by
    have hp : E[I.params] ⊢ₛ (.var p : Expr ζ ι.nlevels ι.nparams) :
        I.paramType .param (fun q => .var q) p := by
      have hp' : E[I.params] ⊢ₛ .var p :
          (I.params.get p).subst .var := by
        change E[I.params] ⊢ₛ .var p : (I.params.get p).subst Subst.id
        simpa using hpsCtx.var p
      rw [I.params.get_subst .var p p.val p.isLt rfl] at hp'
      simpa [Inductive.paramType] using hp'
    have hp := hp.wkN (Δ := Θ)
    have hterm : (Expr.var p).wkN nfields = psId p := by simp [psId]
    have hvars : (fun i => (Expr.var i).wkN nfields) = psId := by simp [psId]
    rw [hterm, Inductive.paramType_wkN, hvars] at hp
    exact hp
  have hid : E[I.params ++ Θ] ⊢ₛ Subst.id ⊣
      Ctx.instL .param (I.params ++ Θ) := fun v => by
    change E[I.params ++ Θ] ⊢ₛ .var v :
      (Ctx.get v (Ctx.instL .param (I.params ++ Θ))).subst Subst.id
    simpa using hΔ.var v
  have ⟨u, hraw⟩ := hfield.instantiatedType (Γ₁ := I.params ++ Θ)
    hhead (fun _ => rfl) hΔ hpsId hid
  have hraw := (hsource.instLevel (Q := fun _ => True) ls
    fun _ => trivial).substitution_congr hσ (hraw.instLevel ls)
  simp! [hps₁, hps₂] at hraw
  exact ⟨u.inst ls, hraw⟩

namespace Ctor

theorem targetSubstEqStrong
    {fds₁ fds₂ : Fin csig.nfields → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ Fin.append ps₁ fds₁ ≡ Fin.append ps₂ fds₂ ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) := by
  intro hps hfields v
  rw [Ctx.get_subst _ _ v v.val v.isLt rfl, ← Ctx.entry_instL]
  cases v using Fin.addCases with
  | left p =>
    simpa [Inductive.paramType] using hps p
  | right f =>
    rw [I.params.entry_append_right _ (by simp) (by simp) (by simp)]
    simpa using hfields f

theorem WFStrong.ordinarySubstEqStrong (h : ctor.WFStrong E I)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ g : Fin csig.nfields, g < f → E[Γ] ⊢ₛ fds₁ g ≡ fds₂ g :
      ((ctor.ordinaryType g).instL ls).subst
        (Fin.append ps₁ fun previous : Fin g.val =>
          fds₁ (previous.castLE g.isLt.le))) →
    E[Γ] ⊢ₛ
      Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le) ≡
      (Fin.append ps₂ fun previous : Fin f.val => fds₂ (previous.castLE f.isLt.le)) ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le) := by
  intro hps hfields
  have hpsEq := Inductive.paramSubstEqStrong hps
  have hres := SubstEqStrong.extendFamily
    ((h.ordinaryTeleAux f.val f.isLt.le).instLevel
      (Q := fun _ => True) ls fun _ => trivial) hpsEq
    (xs₁ := fun previous : Fin f.val =>
      fds₁ (previous.castLE f.isLt.le))
    (xs₂ := fun previous : Fin f.val =>
      fds₂ (previous.castLE f.isLt.le))
    fun previous => by
      rw [← Ctx.entry_instL]
      simpa using
        hfields (previous.castLE f.isLt.le) (by simp [Fin.lt_def])
  simpa using hres

theorem WFStrong.ordinaryTeleAuxStrong
    (hctor : ctor.WFStrong E I) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    WFTeleStrong E (fun _ => True) I.params
      (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    have htele := ih (by omega)
    have ⟨u, ht⟩ := (hctor.ordinary ⟨count, by omega⟩).type
    exact .snoc htele ⟨u, trivial, by simpa [ordinaryType] using ht⟩

theorem WFStrong.ordinaryFieldExpr_congr (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    ∃ u : Level ℓ, E[Γ] ⊢ₛ ctor.ordinaryFieldExpr ls ps₁ fds₁ f ≡
      ctor.ordinaryFieldExpr ls ps₂ fds₂ f : .sort u := by
  intro hps hfields
  have hfieldsTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params)
      (ctor.ordinaryTeleAux f.val f.isLt.le) := by
    simpa using (h.ordinaryTeleAux f.val f.isLt.le).mono fun _ => trivial
  refine ⟨(ctor.ordinary f).level.inst ls, ?_⟩
  simpa! [ordinaryFieldExpr, ordinaryType] using
    ((hBparams.append hfieldsTele).instLevel (Q := fun _ => True) ls
      fun _ => trivial).substitution_congr
        (h.ordinarySubstEqStrong f hps fun g _ => hfields g)
        ((h.ordinary f).typeExact.instLevel ls)

theorem WFStrong.ordinaryFieldExpr_isTypeStrong (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ g : Fin csig.nfields, g < f → E[Γ] ⊢ₛ fds g : ctor.ordinaryFieldExpr ls ps fds g) →
    E[Γ] ⊢ₛ ctor.ordinaryFieldExpr ls ps fds f typ := by
  intro hps hfields
  have hfieldsTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params)
      (ctor.ordinaryTeleAux f.val f.isLt.le) := by
    simpa using (h.ordinaryTeleAux f.val f.isLt.le).mono fun _ => trivial
  refine ⟨(ctor.ordinary f).level.inst ls, ?_⟩
  have := ((hBparams.append hfieldsTele).instLevel (Q := fun _ => True) ls
    fun _ => trivial).substitution_congr
      (h.ordinarySubstEqStrong f hps fun g hg => by
        simpa [ordinaryFieldExpr] using hfields g hg)
      ((h.ordinary f).typeExact.instLevel ls)
  simpa! [ordinaryFieldExpr, ordinaryType] using this

theorem WFStrong.recursiveFieldExpr_congr (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    ∃ u : Level ℓ, E[Γ] ⊢ₛ ctor.recursiveFieldExpr η ls ps₁ fds₁ f ≡
      ctor.recursiveFieldExpr η ls ps₂ fds₂ f : .sort u :=
  fun hps hfields =>
    (h.recursive f).instantiatedType_congr
      hBparams
      (hBparams.append <| by simpa using
        (h.ordinaryTeleAux csig.nfields le_rfl).mono fun _ => trivial)
      hhead
      (by simp)
      (by simp)
      (targetSubstEqStrong hps hfields)

end Ctor

end Constructors

namespace Inductive

variable {ι : IndSig} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
  {is is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}

-- TODO fun _ => True
structure WFStrong (E : Env ζ) (I : Inductive ζ ι) : Prop where
  params : WFTeleStrong E (fun _ => True) .nil I.params
  indices (s : Fin ι.nsorts) :
    WFTeleStrong E (fun _ => True) I.params (I.indices s)
  ctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.ctors s c).WFStrong E I

theorem WFStrong.paramClosedWF {ℓ : Nat} (hB : I.WFStrong E)
    (ls : Fin ι.nlevels → Level ℓ) :
    E[I.params.instL ls] ⊢ₛ ok := by
  simpa [Ctx.instL] using
    (hB.params.instLevel (Q := fun _ => True) ls fun _ => trivial).appendCtxWFStrong .nil

theorem WFStrong.indexTele
    (hB : I.WFStrong E)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) :
    WFTeleStrong E (fun _ => True) Γ (I.indexTele ls s ps) :=
  ((hB.indices s).instLevel ls fun _ => trivial).substitution
    (paramSubstEqStrong hps).left

theorem paramType_isTypeStrong (hB : I.WFStrong E)
    (p : Fin ι.nparams) :
    (∀ q : Fin ι.nparams, q < p → E[Γ] ⊢ₛ ps q : I.paramType ls ps q) →
    E[Γ] ⊢ₛ I.paramType ls ps p typ := by
  intro hps
  have hΘ := hB.params.instLevel (Q := fun _ : Level ℓ => True) ls fun _ => trivial
  have h := WFTeleStrong.entry_isTypeStrong_nil (Γ := Γ) hΘ (xs := ps) p.val p.isLt
    fun q hq => by
      have := hps ⟨q, by omega⟩ (by simpa [Fin.lt_def] using hq)
      simpa [Inductive.paramType] using this
  simpa [Inductive.paramType] using h

theorem indexType_isTypeStrong
    (hidx : WFTeleStrong E (fun _ => True) I.params (I.indices s))
    (i : Fin (ι.nindices s)) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ j : Fin (ι.nindices s), j < i → E[Γ] ⊢ₛ is j : I.indexType ls s ps is j) →
    E[Γ] ⊢ₛ I.indexType ls s ps is i typ := by
  intro hΓ hps his
  have hΔ : WFTeleStrong E (fun _ => True) Γ (I.indexTele ls s ps) :=
    (hidx.instLevel ls fun _ => trivial).substitution (paramSubstEqStrong hps).left
  have h := WFTeleStrong.entry_isTypeStrong hΔ (σ := Subst.id) (xs := is) i
    (fun v => by
      rw [Expr.subst_id]
      exact hΓ.var v)
    fun j hj => by simpa using his j hj
  simpa using h

theorem paramType_congr (hB : I.WFStrong E)
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ I.paramType ls ps₁ p ≡ I.paramType ls ps₂ p typ := by
  intro hps
  have ⟨u, h⟩ := hB.params.get_instL_subst_congr ls
    p (paramSubstEqStrong hps)
  rw [I.paramType_eq_get_subst ls ps₁ p,
    I.paramType_eq_get_subst ls ps₂ p] at h
  exact .ofDefEq h

theorem indexSubstEqStrong (hB : I.WFStrong E)
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ₛ Fin.append ps₁ is₁ ≡ Fin.append ps₂ is₂ ⊣ Ctx.instL ls (I.params ++ I.indices s) := by
  intro hps his
  have hindices := (hB.indices s).instLevel (Q := fun _ : Level ℓ => True)
    ls fun _ => trivial
  rw [Ctx.instL_append]
  exact SubstEqStrong.extendFamily hindices (paramSubstEqStrong hps) fun i => by
    simpa [Inductive.indexType, Ctx.proj_eq_entry] using his i

theorem indexType_congr (hB : I.WFStrong E)
    (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ₛ I.indexType ls s ps₁ is₁ i ≡ I.indexType ls s ps₂ is₂ i typ := by
  intro hps his
  have hΘ : WFTeleStrong E (fun _ : Level ι.nlevels => True) .nil
      (I.params ++ I.indices s) :=
    hB.params.append (by simpa using hB.indices s)
  have ⟨u, h⟩ := hΘ.get_instL_subst_congr ls
    (Fin.natAdd ι.nparams i) (indexSubstEqStrong hB hps his)
  rw [I.indexType_eq_get_subst ls s ps₁ is₁ i,
    I.indexType_eq_get_subst ls s ps₂ is₂ i] at h
  exact .ofDefEq h

theorem paramType_conv (hB : I.WFStrong E)
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ ps₂ p ≡ ps₂ p : I.paramType ls ps₂ p :=
  fun hps => (paramType_congr hB p hps).convStrong (hps p).right

theorem indexType_conv (hB : I.WFStrong E)
    (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ₛ is₂ i ≡ is₂ i : I.indexType ls s ps₂ is₂ i :=
  fun hps his => (indexType_congr hB i hps his).convStrong (his i).right

theorem WFStrong.motiveTele
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.motiveTele η ls ps s) := by
  have hΓindices : E[Γ ++
      (E.get η).block.indexTele ls s ps] ⊢ₛ ok :=
    (hB.indexTele hps).appendCtxWFStrong hΓ
  constructor
  · exact hB.indexTele hps
  · exact ⟨(E.get η).block.level.inst ls, trivial,
      DefeqStrong.indDF
        (fun p => by
          simpa using (hps p).wkN
            (Δ := (E.get η).block.indexTele ls s ps))
        fun index => by
          simpa [Fin.natAdd] using hΓindices.var (Fin.natAdd n index)⟩

theorem motiveType_congr
    (hB : (E.get η).block.WFStrong E)
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ (E.get η).block.motiveType η ls ps₁ l s ≡
      (E.get η).block.motiveType η ls ps₂ l s typ := by
  intro hΓ hps
  have hpsSelf (p) := (hps p).left
  have hΓindices : E[Γ ++
      (E.get η).block.indexTele ls s ps₁] ⊢ₛ ok :=
    (hB.indexTele hpsSelf).appendCtxWFStrong hΓ
  have hind : E[Γ ++ (E.get η).block.indexTele ls s ps₁] ⊢ₛ
      .ind η s ls (fun p => (ps₁ p).wkN (ι.nindices s))
        (fun index => .var (Fin.natAdd n index)) ≡
      .ind η s ls (fun p => (ps₂ p).wkN (ι.nindices s))
        (fun index => .var (Fin.natAdd n index)) :
      .sort ((E.get η).block.level.inst ls) :=
    DefeqStrong.indDF
      (fun p => by
        simpa using (hps p).wkN
          (Δ := (E.get η).block.indexTele ls s ps₁))
      fun index => by
        simpa [Fin.natAdd] using hΓindices.var (Fin.natAdd n index)
  have hsort : E[(Γ ++ (E.get η).block.indexTele ls s ps₁).snoc
      (.ind η s ls (fun p => (ps₁ p).wkN (ι.nindices s))
        fun index => .var (Fin.natAdd n index))] ⊢ₛ
      Expr.sort l ≡ .sort l : .sort l.succ :=
    .sortDF
  have hforall := DefeqStrong.forallEDF hind hsort (hind.snocConv hsort)
  have ⟨u, hpi⟩ := WFTeleStrong.pi_instL_substN_congr
    (Γ₀ := (E.get η).block.params) (Θ := (E.get η).block.indices s)
    hB.params (hB.indices s) ls (paramSubstEqStrong hps) hforall
  exact .ofDefEq hpi

end Inductive

namespace Ctor.WFStrong

variable {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
  {ctor : Ctor ζ ι s csig} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}

theorem fieldParams (ctor : Ctor ζ ι s csig)
    (param : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ csig.fieldParams ps param :
      (E.get η).block.paramType ls (csig.fieldParams ps) param := by
  intro hps
  have hp := (hps param).wkN (Δ := ctor.ordinaryFieldTele η ls ps)
  have hp := hp.wkN
    (Δ := ctor.recursiveFieldTele η ls (fun param => (ps param).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
    ((ps param).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ps param).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.paramType ls
      (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) param
  simpa [Tele.append_assoc, Ctor.fieldTele] using hp

theorem fieldParams_congr (ctor : Ctor ζ ι s csig)
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    (param : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ₛ
      csig.fieldParams ps₁ param ≡ csig.fieldParams ps₂ param :
        (E.get η).block.paramType ls (csig.fieldParams ps₁) param := by
  intro hps
  have hp := (hps param).wkN (Δ := ctor.ordinaryFieldTele η ls ps₁)
  have hp := hp.wkN
    (Δ := ctor.recursiveFieldTele η ls (fun param => (ps₁ param).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  change E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ₛ
    ((ps₁ param).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ps₂ param).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.paramType ls
      (fun p => ((ps₁ p).wkN csig.nfields).wkN csig.nrecFields) param
  simpa [Tele.append_assoc, Ctor.fieldTele] using hp

theorem fieldMotive (ctor : Ctor ζ ι s csig)
    (s₁ : Fin ι.nsorts) :
    (∀ s, E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps l s) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
      ((ms s₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.motiveType η ls (csig.fieldParams ps) l s₁ := by
  intro hms
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
    ((ms s₁).wkN csig.nfields).wkN csig.nrecFields :
      (E.get η).block.motiveType η ls
        (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) l s₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using
    (hms s₁).wkN.wkN

theorem fieldMotive_congr (ctor : Ctor ζ ι s csig)
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
    (s₁ : Fin ι.nsorts) :
    (∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps l s) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
      ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
        ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.motiveType η ls (csig.fieldParams ps) l s₁ := by
  intro hms
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
    ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) l s₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using
    (hms s₁).wkN.wkN

theorem fieldCase (ctor : Ctor ζ ι s csig)
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
    (s₁ : Fin ι.nsorts) (c₁ : Fin (ι.nctors s₁)) :
    (∀ s₁ c₁, E[Γ] ⊢ₛ mins s₁ c₁ : (E.get η).block.caseFnType η ls ps ms s₁ c₁) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
      ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.caseFnType η ls (csig.fieldParams ps)
          (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁ := by
  intro hmins
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
    ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
      (E.get η).block.caseFnType η ls
        (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields)
        (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using
    (hmins s₁ c₁).wkN.wkN

theorem fieldOrdinary (hctor : ctor.WFStrong E (E.get η).block)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ csig.fieldOrdinary f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append (csig.fieldParams ps) fun previous : Fin f.val =>
          csig.fieldOrdinary (previous.castLE f.isLt.le)) := by
  intro hps
  have hl := hctor.boundOrdinarySubstWFStrong (η := η) hps (Fin.natAdd ι.nparams f)
  rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL] at hl
  have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
    simp
  rw [(E.get η).block.params.entry_append_right _ (by omega) hb (by omega)] at hl
  have hl : E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ
      Expr.boundVars n csig.nfields 0 f :
        ((ctor.ordinaryType f).instL ls).subst
          (Fin.append (fun param => (ps param).wkN csig.nfields)
            fun previous => Expr.boundVars n csig.nfields 0
              (previous.castLE f.isLt.le)) := by
    simpa using hl
  unfold CtorSig.fieldParams CtorSig.fieldOrdinary
  have hl := hl.wkN (Δ := ctor.recursiveFieldTele η ls (fun param => (ps param).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  simpa [Tele.append_assoc, Expr.boundVars, Ctor.fieldTele] using hl

theorem fieldTargetSubst (hctor : ctor.WFStrong E (E.get η).block) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ
      Fin.append (csig.fieldParams ps) csig.fieldOrdinary ⊣
        Ctx.instL ls ((E.get η).block.params ++ ctor.ordinaryTele) :=
  fun hps =>
    Ctor.targetSubstWFStrong (Ctor.WFStrong.fieldParams ctor · hps)
      (hctor.fieldOrdinary · hps)

theorem fieldRecursive (hctor : ctor.WFStrong E (E.get η).block)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ csig.fieldRecursive f :
      (ctor.recursive f).instantiatedType η ls (csig.fieldParams ps)
        (Fin.append (csig.fieldParams ps) csig.fieldOrdinary) := by
  intro hΓ hps
  have hΓfield := (hctor.fieldTele rfl hΓ hps).appendCtxWFStrong hΓ
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

end Ctor.WFStrong

theorem DefeqStrong.nullaryCtor {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
    (hB : (E.get η).block.WFStrong E) (hf : IsEmpty (Fin (ι.ctors s c).nfields))
    (hr : IsEmpty (Fin (ι.ctors s c).nrecFields)) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ .ctor η s c ls ps fds recFds :
      .ind η s ls ps fun i => ((E.get η).block.ctors s c).targetIndex ls ps fds i := by
  intro hps
  have hσ := Ctor.targetSubstWFStrong (ctor := (E.get η).block.ctors s c) (fds := fds) hps
    fun f => hf.elim f
  exact .ctorDF (fieldLevels := fun f => hf.elim f) (recFieldLevels := fun f => hr.elim f)
    hps (fun f => hf.elim f) (fun f => hr.elim f) (fun f => hf.elim f) (fun f => hr.elim f)
    (.indDF hps fun i => (hB.ctors s c).targetIndex i hσ)

section Recursor

variable {ι : IndSig} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)}
  {nfields arity : Nat} {s target : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {csig : CtorSig ι.nsorts} {ctor : Ctor ζ ι s csig}
  {fd : RecField ζ ι nfields arity target}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
  {ms ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
  {Δ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
  {σ : Subst ζ ℓ (ι.nparams + nfields) n}
  {r : Expr ζ ℓ n}

namespace Inductive

theorem WFStrong.motiveResult_congr {η : Head ζ (.inductive ι)}
    (hB : (E.get η).block.WFStrong E)
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}
    {maj₁ maj₂ : Expr ζ ℓ n}
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ index, E[Γ] ⊢ₛ is₁ index ≡ is₂ index :
      (E.get η).block.indexType ls s ps₁ is₁ index) →
    E[Γ] ⊢ₛ maj₁ ≡ maj₂ :
      .ind η s ls ps₁ is₁ →
    E[Γ] ⊢ₛ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
      Inductive.motiveResult (ms₂ s) is₂ maj₂ :
      .sort l := by
  intro hΓ hps hms his hmaj
  have hpsSelf := fun p => (hps p).left
  have htele := hB.motiveTele (s := s) hΓ hpsSelf
  have .snoc hisTele ⟨_, _, hind⟩ := htele
  have hmotive := hms s
  change E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
    Ctx.pi (.forallE
      (.ind η s ls
        (fun p => (ps₁ p).wkN (ι.nindices s))
        fun index => .var (Fin.natAdd n index))
      (.sort l))
      ((E.get η).block.indexTele ls s ps₁) at hmotive
  have hcodomain : E[Γ ++
      (E.get η).block.indexTele ls s ps₁] ⊢ₛ
      .forallE
        (.ind η s ls
          (fun p => (ps₁ p).wkN (ι.nindices s))
          fun index => .var (Fin.natAdd n index))
        (.sort l) typ :=
    ⟨_, .forallEDF hind .sortDF .sortDF⟩
  have hisPhase (index : Fin (ι.nindices s)) : E[Γ] ⊢ₛ
      is₁ index ≡ is₂ index :
      (((E.get η).block.indexTele ls s ps₁).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          is₁ (previous.castLE index.isLt.le)) := by
    simpa using his index
  have hfun := Ctx.pi_applyFamilyStrong
    hΓ hisTele hcodomain hisPhase hmotive
  have ⟨_, hmajType⟩ := hmaj.regular
  simpa [Inductive.motiveResult] using .appDF
    hmajType .sortDF
    (by simpa! using hfun) hmaj
    (by simpa! using .sortDF)

end Inductive

theorem RecField.WFStrong.ihType
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    {ms : Fin ι.nsorts → Expr ζ ℓ n} {l : Level ℓ}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s :
      I.motiveType η ls ps l s) →
    E[Γ] ⊢ₛ σ ⊣ Δ.instL ls →
    E[Γ] ⊢ₛ r : fd.instantiatedType η ls ps σ →
    E[Γ] ⊢ₛ fd.ihType ls ms σ r typ := by
  intro hΓ hps hms hσ hr
  cases hhead
  have hΓtele := (h.instantiatedTelescope (P := fun _ => True)
    (fun _ => trivial) hσ).appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk : ∀ p,
      E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ
        (ps p).wkN arity : (E.get η).block.paramType ls
          (fun p => (ps p).wkN arity) p := fun p => by
    simpa using (hps p).wkN
  have hmsWk (s) :
      E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ
        (ms s).wkN arity :
          (E.get η).block.motiveType η ls
            (fun p => (ps p).wkN arity) l s := by
    simpa using (hms s).wkN
  exact Ctx.pi_isTypeStrong hΓtele
    (Inductive.WFStrong.motiveResult_congr
      (hB := show (E.get η).block.WFStrong E from hB)
      hΓtele
      (fun p => (hpsWk p).left)
      (fun s => (hmsWk s).left)
      (fun index => (his index).left)
      (Ctx.pi_applyBoundStrong hΓtele
        (.indDF hpsWk his) hr).left)

theorem RecField.WFStrong.ihType_congr
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    (hΔ : WFTeleStrong E (fun _ => True) .nil Δ)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n} {l : Level ℓ}
    {σ₁ σ₂ : Subst ζ ℓ (ι.nparams + nfields) n}
    (hσparams : ∀ p, σ₁ (p.castAdd nfields) = ps₁ p) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s : I.motiveType η ls ps₁ l s) →
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ Ctx.instL ls Δ →
    E[Γ] ⊢ₛ r : fd.instantiatedType η ls ps₁ σ₁ →
    ∃ u : Level ℓ,
    E[Γ] ⊢ₛ fd.ihType ls ms₁ σ₁ r ≡
      fd.ihType ls ms₂ σ₂ r : .sort u := by
  intro hΓ hps hms hσ hr
  cases hhead
  have ⟨telescope, is⟩ := fd
  have ⟨htele, his⟩ := h
  have htele : WFTeleStrong E (fun _ => True) Δ telescope :=
    htele.mono fun _ => trivial
  have hteleL := htele.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hΓtele := (hteleL.substitution hσ.left).appendCtxWFStrong hΓ
  have hsource : WFTeleStrong E (fun _ => True) .nil (Δ ++ telescope) :=
    hΔ.append (by simpa using htele)
  have hsourceL := hsource.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hlift : E[Γ ++ Ctx.substN σ₁ arity (telescope.instL ls)] ⊢ₛ
      σ₁.liftN arity ≡ σ₂.liftN arity ⊣ Ctx.instL ls (Δ ++ telescope) := by
    simpa using SubstEqStrong.liftN hteleL hσ
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
  have hpsWk (p) : E[Γ ++ Ctx.substN σ₁ arity (telescope.instL ls)] ⊢ₛ
      (ps₁ p).wkN arity ≡ (ps₂ p).wkN arity :
      (E.get η).block.paramType ls (fun p => (ps₁ p).wkN arity) p := by
    simpa using (hps p).wkN
      (Δ := Ctx.substN σ₁ arity (Ctx.instL ls telescope))
  have hisWk (index) : E[Γ ++ Ctx.substN σ₁ arity (telescope.instL ls)] ⊢ₛ
      ((is index).instL ls).subst (σ₁.liftN arity) ≡
      ((is index).instL ls).subst (σ₂.liftN arity) :
      (E.get η).block.indexType ls target
        (fun p => (ps₁ p).wkN arity)
        (fun i => ((is i).instL ls).subst (σ₁.liftN arity)) index := by
    simpa [Expr.instL, hpsEq] using
      hsourceL.substitution_congr hlift
        ((his index).instLevel ls)
  have hind := DefeqStrong.indDF (E := E) (η := η) (s := target)
    (fun p => (hpsWk p).left)
    fun index => (hisWk index).left
  have hmsWk (s₁) : E[Γ ++ Ctx.substN σ₁ arity (telescope.instL ls)] ⊢ₛ
      (ms₁ s₁).wkN arity ≡ (ms₂ s₁).wkN arity :
      (E.get η).block.motiveType η ls
        (fun p => (ps₁ p).wkN arity) l s₁ := by
    simpa using (hms s₁).wkN
  exact WFTeleStrong.pi_instL_substN_congr
    hΔ htele ls hσ
    (Inductive.WFStrong.motiveResult_congr hB hΓtele
      hpsWk hmsWk hisWk
        (Ctx.pi_applyBoundStrong hΓtele hind hr))

theorem RecField.WFStrong.iotaIH
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    {η : Head ζ (.inductive ι)} (hhead : (E.get η).block = I)
    (hallowed : I.RecAllowed l)
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s :
      I.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c :
      I.caseFnType η ls ps ms s c) →
    E[Γ] ⊢ₛ σ ⊣ Δ.instL ls →
    E[Γ] ⊢ₛ r : fd.instantiatedType η ls ps σ →
    E[Γ] ⊢ₛ fd.iotaIH η ls l ps ms mins σ r :
      fd.ihType ls ms σ r := by
  intro hΓ hps hms hmins hσ hr
  cases hhead
  have hΓtele := (h.instantiatedTelescope (P := fun _ => True)
    (fun _ => trivial) hσ).appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk : ∀ p,
      E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ
        (ps p).wkN arity : (E.get η).block.paramType ls
          (fun p => (ps p).wkN arity) p := fun p => by
    simpa using (hps p).wkN
      (Δ := fd.instantiatedTelescope ls σ)
  have hind := DefeqStrong.indDF hpsWk his
  rw [RecField.instantiatedType] at hr
  have hmaj := Ctx.pi_applyBoundStrong hΓtele hind hr
  have hmsWk (s) :
      E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ
        (ms s).wkN arity :
          (E.get η).block.motiveType η ls
            (fun p => (ps p).wkN arity) l s := by
    simpa using (hms s).wkN
  have hminsWk (s c) :
      E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ
        (mins s c).wkN arity :
          (E.get η).block.caseFnType η ls
            (fun p => (ps p).wkN arity)
            (fun s => (ms s).wkN arity) s c := by
    simpa using (hmins s c).wkN
  have hresult := Inductive.WFStrong.motiveResult_congr
    hB hΓtele
    (fun p => (hpsWk p).left)
    (fun s => (hmsWk s).left)
    (fun index => (his index).left)
    hmaj.left
  exact Ctx.lam_congrStrong hΓtele
    (.recrDF hallowed hpsWk hmsWk hminsWk his hmaj hresult)

theorem Ctor.WFStrong.iotaIH
    (hctor : ctor.WFStrong E (E.get η).block)
    (hB : (E.get η).block.WFStrong E)
    {fds : Fin csig.nfields → Expr ζ ℓ n}
    {recFds : Fin csig.nrecFields → Expr ζ ℓ n}
    (hallowed : (E.get η).block.RecAllowed l)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s :
      (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      ((ctor.ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ₛ recFds f :
      (ctor.recursive f).instantiatedType η ls ps
        (Fin.append ps fds)) →
    E[Γ] ⊢ₛ ctor.iotaIH η ls l ps ms mins fds recFds f :
      ctor.ihTypeWith ls ms ps fds recFds f :=
  fun hΓ hps hms hmins hfields hrecFields =>
    (hctor.recursive f).iotaIH hB rfl hallowed
      (by simp) hΓ hps hms hmins
      (Ctor.targetSubstWFStrong hps hfields) (hrecFields f)

namespace Inductive

theorem WFStrong.caseType_hasTypeStrong
    (hB : (E.get η).block.WFStrong E)
    {Γcase : Ctx ζ ℓ 0
      (n + (ι.ctors s c).nfields +
        (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields)} :
    E[Γcase] ⊢ₛ ok →
    (∀ p, E[Γcase] ⊢ₛ (ι.ctors s c).caseParams ps p :
      (E.get η).block.paramType ls
        ((ι.ctors s c).caseParams ps) p) →
    (∀ s₁, E[Γcase] ⊢ₛ
      (((ms s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields :
      (E.get η).block.motiveType η ls
        ((ι.ctors s c).caseParams ps) l s₁) →
    (∀ f, E[Γcase] ⊢ₛ
      (ι.ctors s c).caseOrdinary f :
        ((((E.get η).block.ctors s c).ordinaryType f).instL
          ls).subst (Fin.append
            ((ι.ctors s c).caseParams ps)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le))) →
    (∀ f, E[Γcase] ⊢ₛ
      (ι.ctors s c).caseRecursive f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType
          η ls ((ι.ctors s c).caseParams ps)
            (Fin.append
              ((ι.ctors s c).caseParams ps)
              (ι.ctors s c).caseOrdinary)) →
    E[Γcase] ⊢ₛ (E.get η).block.caseType η ls ps ms s c :
      .sort l := by
  intro hΓcase hps hms hfields hrecFields
  let I := (E.get η).block
  have hσ := Ctor.targetSubstWFStrong hps hfields
  have his := fun index => (hB.ctors s c).targetIndex index hσ
  have htarget := DefeqStrong.indDF hps his
  have hmaj := DefeqStrong.ctorDF hps hfields
    hrecFields
    (fun f => (hB.ctors s c).ordinaryFieldExprStrong f hps hfields)
    (fun f => ((hB.ctors s c).recursiveFieldExprStrong rfl f hΓcase
      hps hfields).choose_spec)
    htarget
  simpa [caseType] using
    hB.motiveResult_congr hΓcase
      (fun p => (hps p).left)
      (fun s => (hms s).left)
      (fun index => (his index).left)
      hmaj.left

theorem WFStrong.caseType_congr
    (hB : (E.get η).block.WFStrong E)
    {Γcase : Ctx ζ ℓ 0
      (n + (ι.ctors s c).nfields +
        (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields)} :
    E[Γcase] ⊢ₛ ok →
    (∀ p, E[Γcase] ⊢ₛ (ι.ctors s c).caseParams ps₁ p ≡
      (ι.ctors s c).caseParams ps₂ p :
      (E.get η).block.paramType ls
        ((ι.ctors s c).caseParams ps₁) p) →
    (∀ s₁, E[Γcase] ⊢ₛ
      (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields :
      (E.get η).block.motiveType η ls
        ((ι.ctors s c).caseParams ps₁) l s₁) →
    (∀ f, E[Γcase] ⊢ₛ
      (ι.ctors s c).caseOrdinary f :
        ((((E.get η).block.ctors s c).ordinaryType f).instL
          ls).subst (Fin.append
            ((ι.ctors s c).caseParams ps₁)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le))) →
    (∀ f, E[Γcase] ⊢ₛ
      (ι.ctors s c).caseRecursive f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType
          η ls ((ι.ctors s c).caseParams ps₁)
            (Fin.append
              ((ι.ctors s c).caseParams ps₁)
              (ι.ctors s c).caseOrdinary)) →
    E[Γcase] ⊢ₛ (E.get η).block.caseType η ls ps₁ ms₁ s c ≡
      (E.get η).block.caseType η ls ps₂ ms₂ s c : .sort l := by
  intro hΓcase hps hms hfields hrecFields
  have his := fun index =>
    (hB.ctors s c).targetIndex_congr hB.params index hps hfields
  have htarget := DefeqStrong.indDF hps his
  have hordinary := fun f =>
    (hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps hfields
  have hrecursive := fun f =>
    (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps hfields
  have hmaj := DefeqStrong.ctorDF hps hfields hrecFields
    (fun f => (hordinary f).choose_spec)
    (fun f => (hrecursive f).choose_spec)
    htarget
  simpa [caseType] using hB.motiveResult_congr hΓcase hps hms his hmaj

theorem WFStrong.motiveBinders
    {Γ : Ctx ζ ℓ 0 ι.nparams}
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ param, E[Γ] ⊢ₛ Expr.var param :
      (E.get η).block.paramType ls Expr.var param) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.motiveBinders η ls l) := by
  apply WFTeleStrong.ofTypes
  intro s
  have htele := hB.motiveTele (s := s) hΓ hps
  have ⟨v, ht⟩ := Ctx.pi_isTypeStrong (htele.appendCtxWFStrong hΓ)
    (DefeqStrong.sortDF (l := l))
  exact ⟨v, trivial, ht⟩

theorem WFStrong.motiveBinders_var
    {Γ : Ctx ζ ℓ 0 ι.nparams}
    (hB : (E.get η).block.WFStrong E)
    (s : Fin ι.nsorts) :
    E[Γ] ⊢ₛ ok →
    (∀ param, E[Γ] ⊢ₛ Expr.var param :
      (E.get η).block.paramType ls Expr.var param) →
    E[Γ ++ (E.get η).block.motiveBinders η ls l] ⊢ₛ
      Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun param => Expr.var (param.castLE (by omega))) l s := by
  intro hΓ hps
  have hv := ((hB.motiveBinders (l := l) hΓ hps).appendCtxWFStrong hΓ).var
    (Fin.natAdd ι.nparams s)
  simp [Inductive.motiveBinders] at hv
  simpa [Inductive.motiveBinders, Fin.natAdd, Fin.castAdd] using hv

end Inductive

theorem Ctor.WFStrong.ihTeleAux
    (hctor : ctor.WFStrong E (E.get η).block)
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p)
    (hms : ∀ s, E[Γ] ⊢ₛ ms s :
      (E.get η).block.motiveType η ls ps l s)
    (count : Nat) (hcount : count ≤ csig.nrecFields) :
    WFTeleStrong E (fun _ => True)
      (Γ ++ ctor.fieldTele η ls ps)
      (ctor.ihTeleAux ls ps ms count hcount) := by
  apply WFTeleStrong.ofTypes
  intro f
  have ⟨u, ht⟩ := (hctor.recursive (f.castLE hcount)).ihType hB
    rfl
    (by simp)
    ((hctor.fieldTele rfl hΓ hps).appendCtxWFStrong hΓ) (Ctor.WFStrong.fieldParams ctor · hps)
    (Ctor.WFStrong.fieldMotive ctor · hms) (hctor.fieldTargetSubst hps)
    (hctor.fieldRecursive (f.castLE hcount) hΓ hps)
  exact ⟨u, trivial, ht⟩

theorem Ctor.WFStrong.ihTele
    (hctor : ctor.WFStrong E (E.get η).block)
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p)
    (hms : ∀ s₁, E[Γ] ⊢ₛ ms s₁ :
      (E.get η).block.motiveType η ls ps l s₁) :
    WFTeleStrong E (fun _ => True)
      (Γ ++ ctor.fieldTele η ls ps)
      (ctor.ihTele ls ps ms) :=
  hctor.ihTeleAux hB hΓ hps hms csig.nrecFields le_rfl

theorem Ctor.WFStrong.ihType_congr
    (hctor : ctor.WFStrong E (E.get η).block)
    (hB : (E.get η).block.WFStrong E)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps₁ l s₁) →
    ∃ u : Level ℓ,
    E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ₛ
      ctor.ihType ls ps₁ ms₁ f ≡ ctor.ihType ls ps₂ ms₂ f : .sort u := by
  intro hΓ hps hms
  have hpsSelf (p) := (hps p).left
  have hΓfield := (hctor.fieldTele rfl hΓ hpsSelf).appendCtxWFStrong hΓ
  have hordinaryTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ (E.get η).block.params)
      ctor.ordinaryTele := by
    simpa using
      hctor.ordinaryTeleAuxStrong csig.nfields le_rfl
  have hΔ := hB.params.append hordinaryTele
  have ⟨u, hih⟩ := (hctor.recursive f).ihType_congr hB hΔ
    rfl (by simp) hΓfield
    (Ctor.WFStrong.fieldParams_congr ctor · hps)
    (Ctor.WFStrong.fieldMotive_congr ctor · hms)
    (Ctor.targetSubstEqStrong
      (Ctor.WFStrong.fieldParams_congr ctor · hps)
      (hctor.fieldOrdinary · hpsSelf))
    (hctor.fieldRecursive f hΓ hpsSelf)
  exact ⟨u, by
    simpa [Ctor.ihType, Ctor.ihTypeWith] using hih⟩

namespace Inductive

theorem WFStrong.caseTele
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p)
    (hms : ∀ s, E[Γ] ⊢ₛ ms s :
      (E.get η).block.motiveType η ls ps l s) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.caseTele η ls ps ms s c) := by
  have hfields := (hB.ctors s c).fieldTele rfl hΓ hps
  have hihs := (hB.ctors s c).ihTele hB hΓ hps hms
  simpa [Inductive.caseTele] using hfields.append hihs

theorem caseParams_typed
    (param : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      (ι.ctors s c).caseParams ps param :
        (E.get η).block.paramType ls
          ((ι.ctors s c).caseParams ps) param := by
  intro hps
  have caseParams_eq : (ι.ctors s c).caseParams ps = fun p =>
      (((ps p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields := rfl
  have hp := (hps param).wkN
    (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
      (fun p => (ps p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars n (ι.ctors s c).nfields 0))
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms)
  rw [caseParams_eq]
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hp

theorem caseMotives_typed
    (s₁ : Fin ι.nsorts) :
    (∀ s, E[Γ] ⊢ₛ ms s :
      (E.get η).block.motiveType η ls ps l s) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      (((ms s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
        (E.get η).block.motiveType η ls
          ((ι.ctors s c).caseParams ps) l s₁ := by
  intro hms
  have caseParams_eq : (ι.ctors s c).caseParams ps = fun p =>
      (((ps p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields := rfl
  have hm := (hms s₁).wkN (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
  have hm := hm.wkN (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
      (fun p => (ps p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars n (ι.ctors s c).nfields 0))
  have hm := hm.wkN (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms)
  rw [caseParams_eq]
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hm

theorem caseParams_congr
    (param : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢ₛ
      (ι.ctors s c).caseParams ps₁ param ≡
        (ι.ctors s c).caseParams ps₂ param :
        (E.get η).block.paramType ls
          ((ι.ctors s c).caseParams ps₁) param := by
  intro hps
  have hp := (hps param).wkN
    (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps₁)
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
      (fun p => (ps₁ p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars n (ι.ctors s c).nfields 0))
  have hp := hp.wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps₁ ms)
  change E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢ₛ
    (((ps₁ param).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ps₂ param).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.paramType ls
      (fun p => (((ps₁ p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) param
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hp

theorem caseMotives_congr
    {l : Level ℓ} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
    (s₁ : Fin ι.nsorts) :
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps l s₁) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢ₛ
      (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
        (E.get η).block.motiveType η ls
          ((ι.ctors s c).caseParams ps) l s₁ := by
  intro hms
  have hm := (hms s₁).wkN
    (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
  have hm := hm.wkN
    (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
      (fun p => (ps p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars n (ι.ctors s c).nfields 0))
  have hm := hm.wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms₁)
  change E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢ₛ
    (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => (((ps p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) l s₁
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hm

theorem WFStrong.caseOrdinary_typed
    (hB : (E.get η).block.WFStrong E)
    (f : Fin (ι.ctors s c).nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      (ι.ctors s c).caseOrdinary f :
        ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append ((ι.ctors s c).caseParams ps)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le)) := by
  intro hps
  have hv := ((hB.ctors s c).fieldOrdinary f hps).wkN
    (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms)
  unfold CtorSig.caseOrdinary CtorSig.caseParams
  simpa [Inductive.caseTele, Tele.append_assoc] using hv

theorem WFStrong.caseRecursive_typed
    (hB : (E.get η).block.WFStrong E)
    (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ
      (ι.ctors s c).caseRecursive f :
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
        (ι.ctors s c).nrecFields) =
        (ι.ctors s c).caseParams ps := rfl
  have hsubstEq :
      (fun v => (Fin.append
        ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary v).wkN (ι.ctors s c).nrecFields) =
        Fin.append
          ((ι.ctors s c).caseParams ps)
          (ι.ctors s c).caseOrdinary := by
    funext v
    cases v using Fin.addCases with
    | left param => simp [CtorSig.caseParams]
    | right fds => simp [CtorSig.caseOrdinary]
  rw [hpsEq, hsubstEq] at hv
  simpa [Tele.append_assoc, Inductive.caseTele, CtorSig.caseRecursive] using hv

theorem WFStrong.caseFnType
    (hB : (E.get η).block.WFStrong E)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p :
      (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s :
      (E.get η).block.motiveType η ls ps l s) →
    E[Γ] ⊢ₛ (E.get η).block.caseFnType η ls ps ms s c typ := by
  intro hΓ hps hms
  have hcaseTele := hB.caseTele (s := s) (c := c) hΓ hps hms
  have hΓcase := hcaseTele.appendCtxWFStrong hΓ
  have hcaseType := hB.caseType_hasTypeStrong hΓcase
    (Inductive.caseParams_typed (ms := ms) (c := c) · hps)
    (Inductive.caseMotives_typed (c := c) · hms)
    (hB.caseOrdinary_typed (ms := ms) · hps)
    (hB.caseRecursive_typed (ms := ms) · hΓ hps)
  exact Ctx.pi_isTypeStrong hΓcase hcaseType

theorem caseFnType_congr {η : Head ζ (.inductive ι)}
    (hB : (E.get η).block.WFStrong E) {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps₁ l s₁) →
    E[Γ] ⊢ₛ (E.get η).block.caseFnType η ls ps₁ ms₁ s c ≡
      (E.get η).block.caseFnType η ls ps₂ ms₂ s c typ := by
  intro hΓ hps hms
  have hpsSelf (p) := (hps p).left
  have hmsSelf (s₁) := (hms s₁).left
  have hΓcase := (hB.caseTele (s := s) (c := c) hΓ hpsSelf
    hmsSelf).appendCtxWFStrong hΓ
  have hcaseType := hB.caseType_congr hΓcase
    (fun p => caseParams_congr (ms := ms₁) (c := c) p hps)
    (fun s₁ => caseMotives_congr (c := c) s₁ hms)
    (hB.caseOrdinary_typed (ms := ms₁) · hpsSelf)
    (hB.caseRecursive_typed (ms := ms₁) · hΓ hpsSelf)
  rw [caseTele, ← Tele.append_assoc] at hcaseType
  have ⟨u, hihs⟩ := Ctx.pi_ofTypes_congrStrong
    (fun f => (hB.ctors s c).ihType_congr hB f hΓ hps hms) hcaseType
  have hpsWk (p) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ₛ
      (ps₁ p).wkN (ι.ctors s c).nfields ≡
        (ps₂ p).wkN (ι.ctors s c).nfields :
      (E.get η).block.paramType ls
        (fun i => (ps₁ i).wkN (ι.ctors s c).nfields) p := by
    simpa using (hps p).wkN
      (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps₁)
  have hfields (f) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ₛ
      Expr.boundVars n (ι.ctors s c).nfields 0 f :
        ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append
            (fun p => (ps₁ p).wkN (ι.ctors s c).nfields)
            fun previous => Expr.boundVars n (ι.ctors s c).nfields 0
              (previous.castLE f.isLt.le)) := by
    have hv := (hB.ctors s c).boundOrdinarySubstWFStrong
      (η := η) hpsSelf (Fin.natAdd ι.nparams f)
    rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL] at hv
    have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
      simp
    rw [Ctx.entry_append_right (E.get η).block.params _
      (by omega) hb (by omega)] at hv
    simpa using hv
  rw [Ctor.fieldTele, ← Tele.append_assoc] at hihs
  have ⟨v, hrec⟩ := Ctx.pi_ofTypes_congrStrong
    (fun f => (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hpsWk hfields) hihs
  have ⟨_, hpi⟩ := WFTeleStrong.pi_instL_substN_congr hB.params
    ((hB.ctors s c).ordinaryTeleAuxStrong (ι.ctors s c).nfields le_rfl)
    ls (paramSubstEqStrong hps) hrec
  exact IsTypeEq.ofDefEq <| by
    simpa [caseFnType, caseTele, Ctor.fieldTele, Ctx.pi, Tele.foldr_append]

theorem caseFnType_conv {η : Head ζ (.inductive ι)}
    (hB : (E.get η).block.WFStrong E) {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
    {mins₁ mins₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps₁ l s₁) →
    E[Γ] ⊢ₛ mins₁ ≡ mins₂ :
      (E.get η).block.caseFnType η ls ps₁ ms₁ s c →
    E[Γ] ⊢ₛ mins₂ ≡ mins₂ :
      (E.get η).block.caseFnType η ls ps₂ ms₂ s c :=
  fun hΓ hps hms hmin => (caseFnType_congr hB hΓ hps hms).convStrong hmin.right

theorem WFStrong.caseBinders
    {Γ : Ctx ζ ℓ 0 (ι.nparams + ι.nsorts)}
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ param, E[Γ] ⊢ₛ Expr.var (param.castLE (by omega)) :
      (E.get η).block.paramType ls
        (fun param => Expr.var (param.castLE (by omega))) param)
    (hms : ∀ s, E[Γ] ⊢ₛ
      Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun param => Expr.var (param.castLE (by omega))) l s) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.caseBinders η ls) := by
  apply WFTeleStrong.ofTypes
  intro tag
  obtain ⟨⟨s, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
    ⟨_, Fin.encodeSigma_decodeSigma ..⟩
  have ⟨v, ht⟩ := hB.caseFnType (s := s) (c := c) hΓ hps hms
  rw [Fin.decodeSigma_encodeSigma]
  exact ⟨v, trivial, ht⟩

theorem WFStrong.recrTele
    {s : Fin ι.nsorts}
    (hB : (E.get η).block.WFStrong E) :
    WFTeleStrong E (fun _ => True) .nil
      ((E.get η).block.recrTele η s ls l) := by
  have hps := hB.params.instLevel (Q := fun _ => True) ls
    fun _ => trivial
  have hpsTele : WFTeleStrong E (fun _ => True) .nil
      (Ctx.instL ls (E.get η).block.params) := by
    simpa [Ctx.instL] using hps
  have hΓparams : E[Ctx.instL ls (E.get η).block.params] ⊢ₛ ok := by
    simpa using hpsTele.appendCtxWFStrong .nil
  have hparamVars (param : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params] ⊢ₛ Expr.var param :
        (E.get η).block.paramType ls Expr.var param := by
    simpa using hΓparams.var param
  have hms := hB.motiveBinders (l := l) hΓparams hparamVars
  have hΓmotives := hms.appendCtxWFStrong hΓparams
  have hparamMotives (param : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l] ⊢ₛ
        Expr.var (param.castLE (by omega)) :
          (E.get η).block.paramType ls
            (fun param => Expr.var (param.castLE (by omega))) param := by
    simpa [Fin.castAdd] using (hparamVars param).wkN
      (Δ := (E.get η).block.motiveBinders η ls l)
  have hmins := hB.caseBinders hΓmotives hparamMotives
    (hB.motiveBinders_var · hΓparams hparamVars)
  have hΓcases := hmins.appendCtxWFStrong hΓmotives
  let casesEnd := ι.nparams + ι.nsorts + Fin.sum ι.nctors
  let ps : Fin ι.nparams → Expr ζ ℓ casesEnd :=
    fun param => .var (param.castLE (by omega))
  have hparamCases (param : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls] ⊢ₛ
        ps param :
          (E.get η).block.paramType ls ps param := by
    simpa [Fin.castAdd] using (hparamMotives param).wkN
      (Δ := (E.get η).block.caseBinders η ls)
  have his := hB.indexTele (s := s) hparamCases
  have hΓindices := his.appendCtxWFStrong hΓcases
  have hparamIndices (param : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ₛ
        (ps param).wkN (ι.nindices s) :
          (E.get η).block.paramType ls
            (fun param => (ps param).wkN (ι.nindices s)) param := by
    simpa using (hparamCases param).wkN
      (Δ := (E.get η).block.indexTele ls s ps)
  have hindexVars (index : Fin (ι.nindices s)) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ₛ
        Expr.var ⟨casesEnd + index.val, by omega⟩ :
          (E.get η).block.indexType ls s
            (fun param => (ps param).wkN (ι.nindices s))
            (fun index => Expr.var ⟨casesEnd + index.val, by omega⟩) index := by
    have hv := hΓindices.var ⟨casesEnd + index.val, by omega⟩
    rw [Inductive.indexTele_get] at hv
    simpa using hv
  have hmaj := DefeqStrong.indDF
    hparamIndices hindexVars
  have hpsMotives : WFTeleStrong E (fun _ => True) .nil
      (Ctx.instL ls (E.get η).block.params ++
        (E.get η).block.motiveBinders η ls l) := by
    have hmsTele : WFTeleStrong E (fun _ => True)
        ((#t[] : Ctx ζ ℓ 0 0) ++
          Ctx.instL ls (E.get η).block.params)
        ((E.get η).block.motiveBinders η ls l) := by
      simpa using hms
    exact hpsTele.append hmsTele
  have hminsTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ℓ 0 0) ++
        (Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l))
      ((E.get η).block.caseBinders η ls) := by
    simpa using hmins
  have hpsMotivesCases := hpsMotives.append hminsTele
  have hisTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ℓ 0 0) ++
        (Ctx.instL ls (E.get η).block.params ++
        (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls))
      ((E.get η).block.indexTele ls s ps) := by
    simpa using his
  have htele := hpsMotivesCases.append hisTele
  exact .snoc htele ⟨(E.get η).block.level.inst ls, trivial, by
    simpa [casesEnd, ps] using hmaj⟩

theorem WF.toStrong
    (tr : ∀ {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e t : Expr ζ ℓ n},
      E[Γ] ⊢ e : t →
      E[Γ] ⊢ₛ ok →
      E[Γ] ⊢ₛ e : t)
    (h : I.WF E) :
    I.WFStrong E := by
  have hps := h.params.toStrong tr .nil
  have hΓparams : E[I.params] ⊢ₛ ok := by
    simpa using hps.appendCtxWFStrong .nil
  exact {
    params := hps
    indices := fun s => (h.indices s).toStrong tr hΓparams
    ctors := fun s c => (h.ctors s c).toStrong tr hps
  }

theorem WFStrong.weakenEnv
    {entry : Entry ζ sig} (h : I.WFStrong E) :
    (I.map (.step .refl)).WFStrong (E.snoc entry) := by
  have his (s : Fin ι.nsorts) :
      WFTeleStrong (E.snoc entry) (fun _ => True)
        (I.map (.step .refl)).params
        ((I.map (.step .refl)).indices s) := by
    simpa [Inductive.map, Ctx.weakenEnv] using
      (h.indices s).weakenEnv (entry := entry)
  have hctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
      ((I.map (.step .refl)).ctors s c).WFStrong (E.snoc entry)
        (I.map (.step .refl)) := by
    simpa [Inductive.map] using
      (h.ctors s c).weakenEnv (entry := entry)
  exact {
    params := by
      simpa [Inductive.map, Ctx.weakenEnv] using
        h.params.weakenEnv (entry := entry)
    indices := his
    ctors := hctors
  }

theorem iotaLhs_hasTypeStrong
    {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ}
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Expr ζ ℓ n}
    (hctor : ((E.get η).block.ctors s c).WFStrong E (E.get η).block)
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p ≡ ps p :
      (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s ≡ ms s :
      (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c ≡ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ₛ fds f ≡ fds f :
      ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ₛ recFds f ≡ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls ((E.get η).block.params ++
        ((E.get η).block.ctors s c).ordinaryTele) →
    E[Γ] ⊢ₛ
      (E.get η).block.iotaType η ls ps ms s c fds recFds ≡
      (E.get η).block.iotaType η ls ps ms s c fds recFds :
        .sort l →
    E[Γ] ⊢ₛ
      (E.get η).block.iotaLhs η ls l ps ms mins s c fds
        recFds ≡
      (E.get η).block.iotaLhs η ls l ps ms mins s c fds
        recFds :
        (E.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hΓ hps hms hmins hfields hrecFields hσ hresult
  have his := fun index => hctor.targetIndex index hσ
  have htarget := DefeqStrong.indDF hps his
  have hmaj := DefeqStrong.ctorDF hps hfields hrecFields
    (fun f => hctor.ordinaryFieldExprStrong f hps hfields)
    (fun f => (hctor.recursiveFieldExprStrong rfl f hΓ hps hfields).choose_spec)
    htarget
  exact .recrDF hallowed hps hms hmins
    his hmaj hresult

theorem WFStrong.iotaRhs_hasTypeStrong
    {η : Head ζ (.inductive ι)} (hB : (E.get η).block.WFStrong E)
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Expr ζ ℓ n}
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p ≡ ps p :
      (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s ≡ ms s :
      (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c ≡ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ₛ fds f ≡ fds f :
      ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ₛ recFds f ≡ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ₛ
      (E.get η).block.iotaRhs η ls l ps ms mins s c fds
        recFds ≡
      (E.get η).block.iotaRhs η ls l ps ms mins s c fds
        recFds :
        (E.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hΓ hps hms hmins hfields hrecFields
  have hfn : (E.get η).block.caseFnType η ls ps ms s c =
      Ctx.pi (Ctx.pi (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
          (((E.get η).block.ctors s c).ihTele ls ps ms))
        (((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0)))
        (((E.get η).block.ctors s c).ordinaryFieldTele η ls ps) := by
    unfold Inductive.caseFnType Inductive.caseTele Ctor.fieldTele
    unfold Ctx.pi
    rw [Tele.foldr_append, Tele.foldr_append]
  have hΔord := (hB.ctors s c).ordinaryFieldTele (η := η) hps
  have hΓord := hΔord.appendCtxWFStrong hΓ
  have hΔrec : WFTeleStrong E (fun _ => True)
      (Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps)
      (((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0)) :=
    WFTeleStrong.ofTypes fun f =>
      let ⟨u, ht⟩ := (hB.ctors s c).recursiveFieldType rfl f hΓ hps
      ⟨u, trivial, ht⟩
  have hΓrec := hΔrec.appendCtxWFStrong hΓord
  have hΔih : WFTeleStrong E (fun _ => True)
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
  have hΓcase := hΔih.appendCtxWFStrong hΓrec
  have hcaseType : E[Γ ++
      ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) ++
        ((E.get η).block.ctors s c).ihTele ls ps ms] ⊢ₛ
      (E.get η).block.caseType η ls ps ms s c ≡
      (E.get η).block.caseType η ls ps ms s c : .sort l := by
    have h := hB.caseType_hasTypeStrong
      ((hB.caseTele (s := s) (c := c) hΓ hps hms).appendCtxWFStrong hΓ)
      (Inductive.caseParams_typed (ms := ms) (c := c) · hps)
      (Inductive.caseMotives_typed (c := c) · hms)
      (hB.caseOrdinary_typed (ms := ms) · hps)
      (hB.caseRecursive_typed (ms := ms) · hΓ hps)
    rwa [show Γ ++ (E.get η).block.caseTele η ls ps ms s c =
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) ++
        ((E.get η).block.ctors s c).ihTele ls ps ms by
      unfold Inductive.caseTele Ctor.fieldTele
      simp only [Tele.append_assoc]] at h
  have htA : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps] ⊢ₛ
      Ctx.pi (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
          (((E.get η).block.ctors s c).ihTele ls ps ms))
        (((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0)) typ := by
    have h := Ctx.pi_isTypeStrong
      (Δ := ((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0) ++
          ((E.get η).block.ctors s c).ihTele ls ps ms)
      (by rw [← Tele.append_assoc]; exact hΓcase)
      (by rw [← Tele.append_assoc]; exact hcaseType)
    unfold Ctx.pi at h ⊢
    rwa [Tele.foldr_append] at h
  have hxsA : ∀ p : Fin (ι.ctors s c).nfields, E[Γ] ⊢ₛ fds p ≡ fds p :
      ((((E.get η).block.ctors s c).ordinaryFieldTele η ls ps).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          fds (previous.castLE p.isLt.le)) := by
    intro p
    rw [Ctor.ordinaryFieldTele]
    simpa [Expr.boundVars, Expr.subst] using hfields p
  have hA := Ctx.pi_applyFamilyStrong (P := fun _ => True) hΓ hΔord htA hxsA
    (hfn ▸ hmins s c)
  have hΔrecSubst : Ctx.substN (Fin.append Subst.id fds)
      (ι.ctors s c).nrecFields
      (((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun i => (ps i).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0)) =
      ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds := by
    simp [Expr.boundVars, Expr.subst]
  rw [Ctx.pi_subst, hΔrecSubst] at hA
  have hσA : E[Γ] ⊢ₛ Fin.append Subst.id fds ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps :=
    WFTeleStrong.extendFamily hΔord (fun v => by rw [Expr.subst_id]; exact hΓ.var v) hxsA
  have hΔrecWF : WFTeleStrong E (fun _ => True) Γ
      (((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds) := by
    have h := hΔrec.substitution hσA
    rwa [hΔrecSubst] at h
  have hσAlift : E[Γ ++ ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds] ⊢ₛ
      Subst.liftN (Fin.append Subst.id fds) (ι.ctors s c).nrecFields ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) := by
    have h := SubstWFStrong.liftN hΔrec hσA
    rwa [hΔrecSubst] at h
  have htB : E[Γ ++ ((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds] ⊢ₛ
      (Ctx.pi ((E.get η).block.caseType η ls ps ms s c)
        (((E.get η).block.ctors s c).ihTele ls ps ms)).subst
        (Subst.liftN (Fin.append Subst.id fds) (ι.ctors s c).nrecFields) typ := by
    have ⟨u, h⟩ := Ctx.pi_isTypeStrong
      (Δ := ((E.get η).block.ctors s c).ihTele ls ps ms) hΓcase hcaseType
    exact ⟨u, h.substitution hσAlift⟩
  have hxsB : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ₛ recFds f ≡ recFds f :
      ((((E.get η).block.ctors s c).recursiveFieldTele η ls ps fds).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          recFds (previous.castLE f.isLt.le)) := by
    intro f
    rw [Ctor.recursiveFieldTele, Ctor.recursiveFieldTeleAux, Ctx.entry_ofTypes,
      Expr.wkN_subst_id_append]
    exact hrecFields f
  have hB' := Ctx.pi_applyFamilyStrong (P := fun _ => True) hΓ hΔrecWF htB hxsB hA
  rw [Expr.subst_subst, Subst.liftN_comp_append, Subst.comp_id, Ctx.pi_subst] at hB'
  have hxsB' : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ₛ recFds f ≡ recFds f :
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
  have hσAB : E[Γ] ⊢ₛ Fin.append (Fin.append Subst.id fds) recFds ⊣
      Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E.get η).block.ctors s c).recursiveFieldTele η ls
          (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars n (ι.ctors s c).nfields 0) :=
    WFTeleStrong.extendFamily hΔrec hσA hxsB'
  have hxsC : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ₛ
      (E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds f ≡
      (E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds f :
      ((Ctx.substN (Fin.append (Fin.append Subst.id fds) recFds) (ι.ctors s c).nrecFields
            (((E.get η).block.ctors s c).ihTele ls ps ms)).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          (E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds
            (previous.castLE f.isLt.le)) := by
    intro f
    rw [Ctx.entry_substN _ _ _ f.val (by omega) (by omega) (by omega) (by omega), Ctor.ihTele,
      Ctor.ihTeleAux, Ctx.entry_ofTypes, Ctor.ihType]
    simpa [Inductive.iotaIHs, CtorSig.fieldParams, CtorSig.fieldOrdinary,
      CtorSig.fieldRecursive, Expr.subst] using
      (hB.ctors s c).iotaIH hB hallowed f hΓ hps hms hmins hfields hrecFields
  have hC := Ctx.pi_applyFamilyStrong (P := fun _ => True) hΓ (hΔih.substitution hσAB)
    ⟨l, hcaseType.substitution (SubstWFStrong.liftN hΔih hσAB)⟩ hxsC hB'
  rw [Expr.subst_subst, Subst.liftN_comp_append, Subst.comp_id] at hC
  change E[Γ] ⊢ₛ
    (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds ≡
    (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
    ((E.get η).block.caseType η ls ps ms s c).subst
      ((ι.ctors s c).caseSubst fds recFds
        ((E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds)) at hC
  simpa [Inductive.caseType, Inductive.iotaType, Expr.subst] using hC

end Inductive

end Recursor

section CtorTypeFn

variable {ζ₁ ζ₂ : Sigs} {ι : IndSig}

def Inductive.ctorTypeFn (I : Inductive ζ ι) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Expr ζ ι.nlevels 0 :=
  I.params.lam ((I.ctors s c).ordinaryTele.pi (.sort I.level))

@[simp] theorem Inductive.ctorTypeFn_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.ctorTypeFn s c).map pre = (I.map pre).ctorTypeFn s c := by
  simp [ctorTypeFn, Expr.map, map]

theorem Inductive.WFStrong.ctorTypeFn {I : Inductive ζ ι} (hI : I.WFStrong E)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    ∃ u, E[(#t[] : Ctx ζ ι.nlevels 0 0)] ⊢ₛ I.ctorTypeFn s c : I.params.pi (.sort u) := by
  have hparams : E[I.params] ⊢ₛ ok := by
    simpa using WFTeleStrong.appendCtxWFStrong hI.params .nil
  have hfields := WFTeleStrong.appendCtxWFStrong
    ((hI.ctors s c).ordinaryTeleAuxStrong _ le_rfl) hparams
  have ⟨u, ht⟩ := Ctx.pi_isTypeStrong hfields (.sortDF (l := I.level))
  exact ⟨u, Ctx.lam_congrStrong (by simpa using hparams)
    (by simpa using ht)⟩

end CtorTypeFn

end Metalean
