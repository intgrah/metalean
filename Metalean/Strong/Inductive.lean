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

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {sig : Sig} {E : Env ζ} {ℓ n m : Nat}
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

theorem WFTeleStrong.mono {P Q : Level ℓ → Prop}
    (hPQ : ∀ {u}, P u → Q u) (hΔ : WFTeleStrong E P Γ Δ) :
    WFTeleStrong E Q Γ Δ := by
  induction hΔ with
  | nil => exact .nil
  | snoc _ ht ih =>
    have ⟨u, hu, ht⟩ := ht
    exact .snoc ih ⟨u, hPQ hu, ht⟩

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
  induction h with
  | nil => exact .nil
  | snoc hT ht ih =>
    have ⟨u, hu, ht⟩ := ht
    have ht := ht.weakenEnv entry
    exact .snoc ih ⟨u, hu,
      congr(_[$(Ctx.map_append (.step .refl) Γ _)] ⊢ₛ _ : _).mp ht⟩

namespace Inductive

theorem paramSubstEqStrong :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    E[Γ] ⊢ₛ ps₁ ≡ ps₂ ⊣ Ctx.instL ls I.params := by
  intro hps v
  rw [← Ctx.get_instL, I.paramType_eq_get_subst ls ps₁ v]
  exact hps v

theorem IdxWFStrong.instLevel {ℓ' : Nat}
    (h : I.IdxWFStrong E Γ s ls ps is)
    (levelSubst : Param ℓ → Level ℓ') :
    I.IdxWFStrong E (Γ.instL levelSubst) s (fun i => (ls i).inst levelSubst)
      (fun i => (ps i).instL levelSubst) fun i => (is i).instL levelSubst := by
  intro i
  simpa using (h i).instLevel levelSubst

theorem IdxWFStrong.weakenEnv
    {entry : Entry ζ sig}
    (h : I.IdxWFStrong E Γ s ls ps is) :
    (I.map (.step .refl)).IdxWFStrong (E.snoc entry) Γ.weakenEnv s ls
      (fun p => (ps p).weakenEnv)
      fun i => (is i).weakenEnv := by
  intro i
  simpa [Expr.weakenEnv] using
    (h i).weakenEnv entry

end Inductive

namespace Field

variable {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)} {fd : Field ζ ι nfields}

theorem WFStrong.type :
    fd.WFStrong E I Γ →
    E[Γ] ⊢ₛ fd.type typ
  | ⟨htype, _⟩ => ⟨_, htype⟩

theorem WFStrong.weakenEnv {entry : Entry ζ sig} :
    fd.WFStrong E I Γ →
    (fd.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) Γ.weakenEnv
  | ⟨htype, hlevel⟩ =>
    ⟨by simpa [Expr.weakenEnv, Expr.map, map] using htype.weakenEnv entry, hlevel⟩

end Field

namespace RecField

variable {Γ Δ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}

theorem WFStrong.weakenEnv {entry : Entry ζ sig} :
    fd.WFStrong E I Γ →
    (fd.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) Γ.weakenEnv
  | ⟨htele, his⟩ =>
    ⟨htele.weakenEnv,
      congr(Inductive.IdxWFStrong _ _ $(Ctx.map_append (.step .refl) Γ _) _ _ _ _).mp
        his.weakenEnv⟩

section

variable {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
variable {arity : Nat} {s : Fin ι.nsorts}
  {Θ : Ctx ζ ι.nlevels (ι.nparams + nfields) (ι.nparams + nfields + arity)}
  {is : Fin (ι.nindices s) → Expr ζ ι.nlevels (ι.nparams + nfields + arity)}

theorem WFStrong.teleAt (h : RecField.WFStrong E I Γ ⟨Θ, is⟩)
    {ls : Fin ι.nlevels → Level 0} {bound : Nat}
    (hblock : (I.level.inst ls).eval zeroNs = bound + 1) :
    WFTeleStrong E (fun l => l.eval zeroNs ≤ bound + 1)
      (Ctx.instL ls Γ) (Ctx.instL ls Θ) := by
  have hnz : I.level.eval (Level.eval zeroNs ∘ ls) ≠ 0 := by
    rw [← Level.eval_inst]
    omega
  apply h.tele.instLevel ls
  intro l hl
  rw [Level.eval_inst, ← hblock, Level.eval_inst]
  exact Level.eval_le_of_imax_le hl hnz

theorem WFStrong.recursiveIndex (h : RecField.WFStrong E I Γ ⟨Θ, is⟩)
    {ls : Fin ι.nlevels → Level ℓ} (index : Fin (ι.nindices s)) :
    E[Ctx.instL ls Γ ++ Ctx.instL ls Θ] ⊢ₛ
      (is index).instL ls :
        I.indexType ls s
          (fun param => .var ⟨param.val, by omega⟩)
          (fun i => (is i).instL ls) index := by
  simpa! using h.indices.instLevel ls index

end

theorem WFStrong.instantiatedIndices
    {fd : RecField ζ ι nfields arity s}
    (h : fd.WFStrong E I Δ)
    {Γ : Ctx ζ ℓ 0 n}
    (hσparams : ∀ p, σ (p.castAdd nfields) = ps p)
    (i) :
    E[Γ] ⊢ₛ σ ⊣ Δ.instL ls →
    E[Γ ++ fd.instantiatedTelescope ls σ] ⊢ₛ fd.instantiatedIndices ls σ i :
      I.indexType ls s (fun p => (ps p).wkN arity)
        (fd.instantiatedIndices ls σ) i := by
  intro hσ
  have ⟨htele, his⟩ := h
  have htele := htele.instLevel (Q := fun _ => True) ls
    fun _ => trivial
  have hσLift := SubstWFStrong.liftN htele hσ
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
  simp [Expr.instL] at hi
  rwa [hpsEq] at hi

theorem WFStrong.instantiatedType
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
  have htele' := (h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ
  have hΓtele := htele'.appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk p :
      E[Γ₁ ++ Ctx.substN σ arity (telescope.instL ls)] ⊢ₛ (ps p).wkN arity :
          (E.get η).block.paramType ls
            (fun p => (ps p).wkN arity) p := by
    simpa using (hps p).wkN
  exact Ctx.pi_isTypeStrong hΓtele <| DefeqStrong.indDF hpsWk his

end RecField

variable {fds fds₁ fds₂ : Fin csig.nfields → Expr ζ ℓ n}

namespace Ctor

theorem WFStrong.weakenEnv
    {entry : Entry ζ sig} (h : ctor.WFStrong E I) :
    (ctor.map (.step .refl)).WFStrong (E.snoc entry)
      (I.map (.step .refl)) where
  ordinary f :=
    congr(Field.WFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTeleAux_map (.step .refl) ctor f.val _))) _).mp
      (h.ordinary f).weakenEnv
  recursive f :=
    congr(RecField.WFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTeleAux_map (.step .refl) ctor _ _))) _).mp
      (h.recursive f).weakenEnv
  targetIndices :=
    congr(Inductive.IdxWFStrong _ _ $((Ctx.map_append (.step .refl) I.params _).trans
      congr(_ ++ $(Ctor.ordinaryTeleAux_map (.step .refl) ctor _ _))) _ _ _ _).mp
      h.targetIndices.weakenEnv

theorem WFStrong.ordinaryFieldExprStrong (hctor : ctor.WFStrong E I)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      (((ctor.ordinary f).type).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.ordinaryFieldExpr ls ps fds f :
      .sort ((ctor.ordinary f).level.inst ls) := by
  intro hps hfields
  have hσ := Ctor.forall_ordinarySubst f.isLt.le hps
    fun prior => hfields (prior.castLE f.isLt.le)
  have htype := ((hctor.ordinary f).typeExact.instLevel ls).substitution hσ
  simpa! [ordinaryFieldExpr] using htype

theorem WFStrong.recursiveFieldExprStrong (hctor : ctor.WFStrong E I)
    (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      (((ctor.ordinary f).type).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.recursiveFieldExpr η ls ps fds f typ :=
  fun hΓ hps hfields =>
    (hctor.recursive f).instantiatedType hhead (by simp) hΓ hps
      (Ctor.forall_ordinarySubst le_rfl hps hfields)

theorem wfOrdinaryTeleAux (count : Nat) (hcount : count ≤ csig.nfields)
    (h : ∀ f : Fin count,
      Field.WFStrong E I (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
        (ctor.ordinary (f.castLE hcount))) :
    WFTeleStrong E I.LevelOK I.params (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    have ⟨htype, hlevel⟩ := h ⟨count, by omega⟩
    exact .snoc (ih (by omega) fun f => h (f.castSucc)) ⟨_, hlevel, htype⟩

theorem WFStrong.ordinaryTeleAux
    (h : ctor.WFStrong E I)
    (count : Nat) (hcount : count ≤ csig.nfields) :
    WFTeleStrong E I.LevelOK I.params
      (ctor.ordinaryTeleAux count hcount) :=
  wfOrdinaryTeleAux count hcount fun f => h.ordinary (f.castLE hcount)

private theorem WFStrong.ordinaryTeleAux_get (h : ctor.WFStrong E I) (count : Nat)
    (hcount : count ≤ csig.nfields) (f : Fin count) :
    E[I.params ++ ctor.ordinaryTeleAux count hcount] ⊢ₛ
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

theorem WFStrong.ordinaryTele_get (h : ctor.WFStrong E I) (f : Fin csig.nfields) :
    E[I.params ++ ctor.ordinaryTele] ⊢ₛ
      Ctx.get (Fin.natAdd ι.nparams f)
        (I.params ++ ctor.ordinaryTele) :
      .sort (ctor.ordinary f).level :=
  h.ordinaryTeleAux_get csig.nfields le_rfl f

theorem WFStrong.ordinaryFieldTele
    (h : ctor.WFStrong E I)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) :
    WFTeleStrong E (fun _ => True) Γ
      (ctor.ordinaryFieldTele η ls ps) :=
  (((h.ordinaryTeleAux csig.nfields le_rfl).instLevel ls fun _ => trivial).substitution
    (Inductive.paramSubstEqStrong hps).left)

theorem WFStrong.boundOrdinarySubstWFStrong
    (h : ctor.WFStrong E I) :
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ Fin.append (fun p => (ps p).wkN csig.nfields)
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
    (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p) →
    E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ (ctor.recursive f).instantiatedType η ls
        (fun p => (ps p).wkN csig.nfields)
        (Fin.append (fun p => (ps p).wkN csig.nfields)
          fun fds => .var ⟨n + fds.val, by omega⟩) typ :=
  fun hΓ hps =>
    have htele := h.ordinaryFieldTele (η := η) hps
    (h.recursive f).instantiatedType hhead (by simp)
      (htele.appendCtxWFStrong hΓ)
      (fun p => by simpa using (hps p).wkN)
      (h.boundOrdinarySubstWFStrong hps)

theorem WFStrong.fieldTele
    (h : ctor.WFStrong E I)
    (hhead : (E.get η).block = I)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : I.paramType ls ps p)
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    WFTeleStrong E (fun _ => True) Γ
      (ctor.fieldTele η ls ps stop) := by
  refine (h.ordinaryFieldTele (η := η) hps).append ?_
  apply WFTeleStrong.ofTypes
  intro f
  have ⟨u, ht⟩ := h.recursiveFieldType hhead (f.castLE (Nat.le_of_lt_succ stop.isLt)) hΓ hps
  exact ⟨u, trivial, ht⟩

theorem WFStrong.targetIndex
    (h : ctor.WFStrong E I)
    (i : Fin (ι.nindices s)) :
    E[Γ] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls (I.params ++ ctor.ordinaryTele) →
    E[Γ] ⊢ₛ ctor.targetIndex ls ps fds i :
      I.indexType ls s ps
        (fun i => ctor.targetIndex ls ps fds i) i := by
  intro hσ
  have hpsEq :
      (fun p : Fin ι.nparams =>
        ((Expr.var ⟨p.val, by omega⟩ :
          Expr ζ ι.nlevels (ι.nparams + csig.nfields)).instL ls).subst
            (Fin.append ps fds)) = ps :=
    funext (Fin.append_left ps fds)
  simpa [Ctor.targetIndex, hpsEq] using
    ((h.targetIndices i).instLevel ls).substitution hσ

theorem WFStrong.targetIndex_congr
    (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      (((ctor.ordinary f).type).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ ctor.targetIndex ls ps₁ fds₁ i ≡
      ctor.targetIndex ls ps₂ fds₂ i :
      I.indexType ls s ps₁
        (fun i => ctor.targetIndex ls ps₁ fds₁ i) i := by
  intro hps hfields
  have hfieldsTele : WFTeleStrong E (fun _ => True)
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
          Expr ζ ι.nlevels (ι.nparams + csig.nfields)).instL ls).subst
            (Fin.append ps₁ fds₁)) = ps₁ :=
    funext (Fin.append_left ps₁ fds₁)
  simpa [Ctor.targetIndex, hpsEq] using
    hsource.substitution_congr hσ ((h.targetIndices i).instLevel ls)

end Ctor

theorem RecField.WFStrong.instantiatedType_congr
    {Θ : Ctx ζ ι.nlevels ι.nparams
      (ι.nparams + nfields)}
    (hfield : fd.WFStrong E I (I.params ++ Θ))
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (hsource : WFTeleStrong E (fun _ => True) .nil (I.params ++ Θ))
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
  have ⟨u, hraw⟩ := hfield.instantiatedType hhead (fun _ => rfl) hΔ hpsId hid
  have hraw := (hsource.instLevel (Q := fun _ => True) ls
    fun _ => trivial).substitution_congr hσ (hraw.instLevel ls)
  simp! [hps₁, hps₂] at hraw
  exact ⟨u.inst ls, hraw⟩

namespace Ctor

theorem WFStrong.ordinaryFieldExpr_congr (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (f : Fin csig.nfields)
    (hps : ∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p)
    (hfields : ∀ g : Fin csig.nfields, g < f → E[Γ] ⊢ₛ fds₁ g ≡ fds₂ g :
      (((ctor.ordinary g).type).instL ls).subst
        (Fin.append ps₁ fun previous : Fin g.val =>
          fds₁ (previous.castLE g.isLt.le))) :
    E[Γ] ⊢ₛ ctor.ordinaryFieldExpr ls ps₁ fds₁ f ≡
      ctor.ordinaryFieldExpr ls ps₂ fds₂ f :
        .sort ((ctor.ordinary f).level.inst ls) := by
  have hfieldsTele : WFTeleStrong E (fun _ => True)
      ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params)
      (ctor.ordinaryTeleAux f.val f.isLt.le) := by
    simpa using (h.ordinaryTeleAux f.val f.isLt.le).mono fun _ => trivial
  simpa! [ordinaryFieldExpr] using
    ((hBparams.append hfieldsTele).instLevel (Q := fun _ => True) ls
      fun _ => trivial).substitution_congr
        (Ctor.forall_ordinarySubst f.isLt.le hps fun g =>
          hfields (g.castLE f.isLt.le) g.isLt)
        ((h.ordinary f).typeExact.instLevel ls)

theorem WFStrong.recursiveFieldExpr_congr (h : ctor.WFStrong E I)
    (hBparams : WFTeleStrong E (fun _ => True) .nil I.params)
    (hhead : (E.get η).block = I)
    (f : Fin csig.nrecFields) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      I.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      (((ctor.ordinary f).type).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    ∃ u : Level ℓ, E[Γ] ⊢ₛ ctor.recursiveFieldExpr η ls ps₁ fds₁ f ≡
      ctor.recursiveFieldExpr η ls ps₂ fds₂ f : .sort u :=
  fun hps hfields =>
    (h.recursive f).instantiatedType_congr
      hBparams
      (hBparams.append <| by simpa using
        (h.ordinaryTeleAux csig.nfields le_rfl).mono fun _ => trivial)
      hhead (by simp) (by simp)
      (Ctor.forall_ordinarySubst le_rfl hps hfields)

end Ctor

namespace Inductive

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
  simpa [Inductive.paramType] using
    WFTeleStrong.entry_isTypeStrong_nil hΘ p.val p.isLt
      fun q hq => by
        simpa [Inductive.paramType] using
          hps ⟨q, by omega⟩ (by simpa [Fin.lt_def] using hq)

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
  have h := WFTeleStrong.entry_isTypeStrong hΔ i
    (fun v => by rw [Expr.subst_id]; exact hΓ.var v)
    (by simpa using his)
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

theorem indexSubstEqStrong (hB : I.WFStrong E) :
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
    E[Γ] ⊢ₛ ps₂ p : I.paramType ls ps₂ p :=
  fun hps => (paramType_congr hB p hps).convStrong (hps p).right

theorem indexType_conv (hB : I.WFStrong E)
    (i : Fin (ι.nindices s)) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : I.paramType ls ps₁ p) →
    (∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : I.indexType ls s ps₁ is₁ i) →
    E[Γ] ⊢ₛ is₂ i : I.indexType ls s ps₂ is₂ i :=
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
        (fun p => by simpa using (hps p).wkN)
        fun i => by
          have hv := hΓindices.var (Fin.natAdd n i)
          rw [Inductive.indexTele_get] at hv
          simpa [Fin.natAdd] using hv⟩

theorem motiveType_congr
    (hB : (E.get η).block.WFStrong E) :
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
        (fun i => .var (Fin.natAdd n i)) ≡
      .ind η s ls (fun p => (ps₂ p).wkN (ι.nindices s))
        (fun i => .var (Fin.natAdd n i)) :
      .sort ((E.get η).block.level.inst ls) :=
    DefeqStrong.indDF
      (fun p => by simpa using (hps p).wkN)
      fun i => by
        have hv := hΓindices.var (Fin.natAdd n i)
        rw [Inductive.indexTele_get] at hv
        exact hv
  have hsort : E[(Γ ++ (E.get η).block.indexTele ls s ps₁).snoc
      (.ind η s ls (fun p => (ps₁ p).wkN (ι.nindices s))
        fun i => .var (Fin.natAdd n i))] ⊢ₛ Expr.sort l ≡ .sort l : .sort l.succ :=
    .sortDF
  have hforall := DefeqStrong.forallEDF hind hsort (hind.snocConv hsort)
  have ⟨u, hpi⟩ := WFTeleStrong.pi_instL_substN_congr
    hB.params (hB.indices s) ls (paramSubstEqStrong hps) hforall
  exact .ofDefEq hpi

end Inductive

namespace Ctor.WFStrong

theorem fieldParams (ctor : Ctor ζ ι s csig)
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ₛ csig.fieldParams ps₁ p ≡ csig.fieldParams ps₂ p :
        (E.get η).block.paramType ls (csig.fieldParams ps₁) p := by
  intro hps
  have hp := ((hps p).wkN (Δ := ctor.ordinaryFieldTele η ls ps₁)).wkN
    (Δ := ctor.recursiveFieldTele η ls (fun p => (ps₁ p).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  change E[Γ ++ ctor.fieldTele η ls ps₁] ⊢ₛ ((ps₁ p).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ps₂ p).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.paramType ls
      (fun p => ((ps₁ p).wkN csig.nfields).wkN csig.nrecFields) p
  simpa [Tele.append_assoc, Ctor.fieldTele] using hp

theorem fieldMotive (ctor : Ctor ζ ι s csig)
    (s₁ : Fin ι.nsorts) :
    (∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps l s) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
        ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.motiveType η ls (csig.fieldParams ps) l s₁ := by
  intro hms
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ ((ms₁ s₁).wkN csig.nfields).wkN csig.nrecFields ≡
      ((ms₂ s₁).wkN csig.nfields).wkN csig.nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields) l s₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using (hms s₁).wkN.wkN

theorem fieldCase (ctor : Ctor ζ ι s csig)
    (s₁ : Fin ι.nsorts) (c₁ : Fin (ι.nctors s₁)) :
    (∀ s₁ c₁, E[Γ] ⊢ₛ mins s₁ c₁ : (E.get η).block.caseFnType η ls ps ms s₁ c₁) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
        (E.get η).block.caseFnType η ls (csig.fieldParams ps)
          (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁ := by
  intro hmins
  change E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ ((mins s₁ c₁).wkN csig.nfields).wkN csig.nrecFields :
      (E.get η).block.caseFnType η ls
        (fun p => ((ps p).wkN csig.nfields).wkN csig.nrecFields)
        (fun s₂ => ((ms s₂).wkN csig.nfields).wkN csig.nrecFields) s₁ c₁
  simpa [Tele.append_assoc, Ctor.fieldTele] using
    (hmins s₁ c₁).wkN.wkN

theorem fieldOrdinary (hctor : ctor.WFStrong E (E.get η).block)
    (f : Fin csig.nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ csig.fieldOrdinary f :
      (((ctor.ordinary f).type).instL ls).subst
        (Fin.append (csig.fieldParams ps) fun previous : Fin f.val =>
          csig.fieldOrdinary (previous.castLE f.isLt.le)) := by
  intro hps
  have hl := hctor.boundOrdinarySubstWFStrong (η := η) hps (Fin.natAdd ι.nparams f)
  rw [Ctx.get_subst _ _ _ _ (by omega) rfl, ← Ctx.entry_instL] at hl
  have hb : ι.nparams ≤ (Fin.natAdd ι.nparams f).val := by
    simp
  rw [(E.get η).block.params.entry_append_right _ (by omega) hb (by omega)] at hl
  have hl : E[Γ ++ ctor.ordinaryFieldTele η ls ps] ⊢ₛ Expr.boundVars n csig.nfields 0 f :
        (((ctor.ordinary f).type).instL ls).subst
          (Fin.append (fun p => (ps p).wkN csig.nfields)
            fun previous => Expr.boundVars n csig.nfields 0
              (previous.castLE f.isLt.le)) := by
    simpa using hl
  unfold CtorSig.fieldParams CtorSig.fieldOrdinary
  have hl := hl.wkN (Δ := ctor.recursiveFieldTele η ls (fun p => (ps p).wkN csig.nfields)
      (Expr.boundVars n csig.nfields 0))
  simpa [Tele.append_assoc, Expr.boundVars, Ctor.fieldTele] using hl

theorem fieldTargetSubst (hctor : ctor.WFStrong E (E.get η).block) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ ctor.fieldTele η ls ps] ⊢ₛ Fin.append (csig.fieldParams ps) csig.fieldOrdinary ⊣
        Ctx.instL ls ((E.get η).block.params ++ ctor.ordinaryTele) :=
  fun hps =>
    Ctor.forall_ordinarySubst le_rfl (Ctor.WFStrong.fieldParams ctor · hps)
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

theorem DefeqStrong.nullaryCtor
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
    (hB : (E.get η).block.WFStrong E) (hf : IsEmpty (Fin (ι.ctors s c).nfields))
    (hr : IsEmpty (Fin (ι.ctors s c).nrecFields)) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ] ⊢ₛ .ctor η s c ls ps fds recFds :
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

namespace Inductive

theorem WFStrong.motiveResult_congr
    (hB : (E.get η).block.WFStrong E)
    {maj₁ maj₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps₁ l s) →
    (∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i :
      (E.get η).block.indexType ls s ps₁ is₁ i) →
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
        fun i => .var (Fin.natAdd n i))
      (.sort l))
      ((E.get η).block.indexTele ls s ps₁) at hmotive
  have hcodomain : E[Γ ++
      (E.get η).block.indexTele ls s ps₁] ⊢ₛ .forallE
        (.ind η s ls
          (fun p => (ps₁ p).wkN (ι.nindices s))
          fun i => .var (Fin.natAdd n i))
        (.sort l) typ :=
    ⟨_, .forallEDF hind .sortDF .sortDF⟩
  have hisPhase (i : Fin (ι.nindices s)) : E[Γ] ⊢ₛ is₁ i ≡ is₂ i :
      (((E.get η).block.indexTele ls s ps₁).entry
        (by omega) (by omega)).subst
        (Fin.append (Subst.id : Subst ζ ℓ n n) fun previous =>
          is₁ (previous.castLE i.isLt.le)) := by
    simpa using his i
  have hfun := Ctx.pi_applyFamilyStrong
    hΓ hisTele hcodomain hisPhase hmotive
  have ⟨_, hmajType⟩ := hmaj.regular
  simpa [Inductive.motiveResult] using .appDF
    hmajType .sortDF
    (by simpa! using hfun) hmaj
    (by simpa! using .sortDF)

theorem paramsWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hps : ∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) (p) :
    E[Γ ++ Θ] ⊢ₛ (ps₁ p).wkN arity ≡ (ps₂ p).wkN arity :
      (E.get η).block.paramType ls (fun p => (ps₁ p).wkN arity) p := by
  simpa using (hps p).wkN

theorem motivesWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hms : ∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s :
      (E.get η).block.motiveType η ls ps₁ l s) (s) :
    E[Γ ++ Θ] ⊢ₛ (ms₁ s).wkN arity ≡ (ms₂ s).wkN arity :
      (E.get η).block.motiveType η ls (fun p => (ps₁ p).wkN arity) l s := by
  simpa using (hms s).wkN

theorem casesWkN {Θ : Ctx ζ ℓ n (n + arity)}
    (hmins : ∀ s c, E[Γ] ⊢ₛ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) (s c) :
    E[Γ ++ Θ] ⊢ₛ (mins s c).wkN arity :
      (E.get η).block.caseFnType η ls (fun p => (ps p).wkN arity)
        (fun s => (ms s).wkN arity) s c := by
  simpa using (hmins s c).wkN

end Inductive

theorem RecField.WFStrong.ihType
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    (hhead : (E.get η).block = I)
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
  have hΓtele := ((h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ).appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk := Inductive.paramsWkN (Θ := fd.instantiatedTelescope ls σ) hps
  have hmsWk := Inductive.motivesWkN (Θ := fd.instantiatedTelescope ls σ) hms
  exact Ctx.pi_isTypeStrong hΓtele
    (Inductive.WFStrong.motiveResult_congr (hB := hB)
      hΓtele
      (fun p => (hpsWk p).left)
      (fun s => (hmsWk s).left)
      (fun i => (his i).left)
      (Ctx.pi_applyBoundStrong hΓtele
        (.indDF hpsWk his) hr).left)

theorem RecField.WFStrong.ihType_congr
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    (hΔ : WFTeleStrong E (fun _ => True) .nil Δ)
    (hhead : (E.get η).block = I)
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
  have hpsWk := Inductive.paramsWkN
    (Θ := Ctx.substN σ₁ arity (telescope.instL ls)) hps
  have hisWk (i) : E[Γ ++ Ctx.substN σ₁ arity (telescope.instL ls)] ⊢ₛ
      ((is i).instL ls).subst (σ₁.liftN arity) ≡
      ((is i).instL ls).subst (σ₂.liftN arity) :
      (E.get η).block.indexType ls target
        (fun p => (ps₁ p).wkN arity)
        (fun i => ((is i).instL ls).subst (σ₁.liftN arity)) i := by
    simpa [Expr.instL, hpsEq] using
      hsourceL.substitution_congr hlift
        ((his i).instLevel ls)
  have hind := DefeqStrong.indDF
    (fun p => (hpsWk p).left)
    fun i => (hisWk i).left
  have hmsWk := Inductive.motivesWkN
    (Θ := Ctx.substN σ₁ arity (telescope.instL ls)) hms
  exact WFTeleStrong.pi_instL_substN_congr
    hΔ htele ls hσ
    (Inductive.WFStrong.motiveResult_congr hB hΓtele
      hpsWk hmsWk hisWk
        (Ctx.pi_applyBoundStrong hΓtele hind hr))

theorem RecField.WFStrong.iotaIH
    (h : fd.WFStrong E I Δ) (hB : I.WFStrong E)
    (hhead : (E.get η).block = I)
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
  have hΓtele := ((h.tele.instLevel (Q := fun _ => True) ls fun _ => trivial).substitution hσ).appendCtxWFStrong hΓ
  have his := (h.instantiatedIndices hσparams · hσ)
  have hpsWk := Inductive.paramsWkN (Θ := fd.instantiatedTelescope ls σ) hps
  have hind := DefeqStrong.indDF hpsWk his
  rw [RecField.instantiatedType] at hr
  have hmaj := Ctx.pi_applyBoundStrong hΓtele hind hr
  have hmsWk := Inductive.motivesWkN (Θ := fd.instantiatedTelescope ls σ) hms
  have hminsWk := Inductive.casesWkN (Θ := fd.instantiatedTelescope ls σ) hmins
  have hresult := Inductive.WFStrong.motiveResult_congr
    hB hΓtele
    (fun p => (hpsWk p).left)
    (fun s => (hmsWk s).left)
    (fun i => (his i).left)
    hmaj.left
  exact Ctx.lam_congrStrong hΓtele
    (.recrDF hallowed hpsWk hmsWk hminsWk his hmaj hresult)

namespace Inductive

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
    (∀ s₁, E[Γcase] ⊢ₛ (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
          (ι.ctors s c).nrecFields).wkN
        (ι.ctors s c).nrecFields :
      (E.get η).block.motiveType η ls
        ((ι.ctors s c).caseParams ps₁) l s₁) →
    (∀ f, E[Γcase] ⊢ₛ (ι.ctors s c).caseOrdinary f :
        (((((E.get η).block.ctors s c).ordinary f).type).instL
          ls).subst (Fin.append
            ((ι.ctors s c).caseParams ps₁)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le))) →
    (∀ f, E[Γcase] ⊢ₛ (ι.ctors s c).caseRecursive f :
        (((E.get η).block.ctors s c).recursive f).instantiatedType
          η ls ((ι.ctors s c).caseParams ps₁)
            (Fin.append
              ((ι.ctors s c).caseParams ps₁)
              (ι.ctors s c).caseOrdinary)) →
    E[Γcase] ⊢ₛ (E.get η).block.caseType η ls ps₁ ms₁ s c ≡
      (E.get η).block.caseType η ls ps₂ ms₂ s c : .sort l := by
  intro hΓcase hps hms hfields hrecFields
  have his := fun i =>
    (hB.ctors s c).targetIndex_congr hB.params i hps hfields
  have htarget := DefeqStrong.indDF hps his
  have hordinary := fun f =>
    (hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps (fun g _ => hfields g)
  have hrecursive := fun f =>
    (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps hfields
  have hmaj := DefeqStrong.ctorDF hps hfields hrecFields
    hordinary
    (fun f => (hrecursive f).choose_spec)
    htarget
  simpa [caseType] using hB.motiveResult_congr hΓcase hps hms his hmaj

theorem WFStrong.motiveBinders
    {Γ : Ctx ζ ℓ 0 ι.nparams}
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ Expr.var p :
      (E.get η).block.paramType ls Expr.var p) :
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
    (∀ p, E[Γ] ⊢ₛ Expr.var p :
      (E.get η).block.paramType ls Expr.var p) →
    E[Γ ++ (E.get η).block.motiveBinders η ls l] ⊢ₛ Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun p => Expr.var (p.castLE (by omega))) l s := by
  intro hΓ hps
  have hv := ((hB.motiveBinders (l := l) hΓ hps).appendCtxWFStrong hΓ).var
    (Fin.natAdd ι.nparams s)
  simp [Inductive.motiveBinders] at hv
  simpa [Inductive.motiveBinders, Fin.natAdd, Fin.castAdd] using hv

end Inductive

theorem Ctor.WFStrong.ihTele
    (hctor : ctor.WFStrong E (E.get η).block)
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (hms : ∀ s₁, E[Γ] ⊢ₛ ms s₁ : (E.get η).block.motiveType η ls ps l s₁) :
    WFTeleStrong E (fun _ => True)
      (Γ ++ ctor.fieldTele η ls ps)
      (ctor.ihTele ls ps ms) := by
  apply WFTeleStrong.ofTypes
  intro f
  have ⟨u, ht⟩ := (hctor.recursive f).ihType hB
    rfl
    (by simp)
    ((hctor.fieldTele rfl hΓ hps).appendCtxWFStrong hΓ) (Ctor.WFStrong.fieldParams ctor · hps)
    (Ctor.WFStrong.fieldMotive ctor · hms) (hctor.fieldTargetSubst hps)
    (hctor.fieldRecursive f hΓ hps)
  exact ⟨u, trivial, ht⟩

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
      (hctor.ordinaryTeleAux csig.nfields le_rfl).mono fun _ => trivial
  have hΔ := hB.params.append hordinaryTele
  have ⟨u, hih⟩ := (hctor.recursive f).ihType_congr hB hΔ
    rfl (by simp) hΓfield
    (Ctor.WFStrong.fieldParams ctor · hps)
    (Ctor.WFStrong.fieldMotive ctor · hms)
    (Ctor.forall_ordinarySubst le_rfl
      (Ctor.WFStrong.fieldParams ctor · hps)
      (hctor.fieldOrdinary · hpsSelf))
    (hctor.fieldRecursive f hΓ hpsSelf)
  exact ⟨u, by simpa [Ctor.ihType, Ctor.ihTypeWith] using hih⟩

namespace Inductive

theorem WFStrong.caseTele
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (hms : ∀ s, E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps l s) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.caseTele η ls ps ms s c) := by
  simpa [Inductive.caseTele] using
    ((hB.ctors s c).fieldTele rfl hΓ hps).append ((hB.ctors s c).ihTele hB hΓ hps hms)

theorem caseParams_congr
    (p : Fin ι.nparams) :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢ₛ (ι.ctors s c).caseParams ps₁ p ≡
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
  change E[Γ ++ (E.get η).block.caseTele η ls ps₁ ms s c] ⊢ₛ
    (((ps₁ p).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ps₂ p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.paramType ls
      (fun p => (((ps₁ p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) p
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using hp

theorem caseMotives_congr
    (s₁ : Fin ι.nsorts) :
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ :
      (E.get η).block.motiveType η ls ps l s₁) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢ₛ (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
        (E.get η).block.motiveType η ls
          ((ι.ctors s c).caseParams ps) l s₁ := by
  intro hms
  change E[Γ ++ (E.get η).block.caseTele η ls ps ms₁ s c] ⊢ₛ
    (((ms₁ s₁).wkN (ι.ctors s c).nfields).wkN
      (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields ≡
      (((ms₂ s₁).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields :
    (E.get η).block.motiveType η ls
      (fun p => (((ps p).wkN (ι.ctors s c).nfields).wkN
        (ι.ctors s c).nrecFields).wkN (ι.ctors s c).nrecFields) l s₁
  simpa [Tele.append_assoc, Inductive.caseTele, Ctor.fieldTele] using (hms s₁).wkN.wkN.wkN

theorem WFStrong.caseOrdinary_typed
    (hB : (E.get η).block.WFStrong E)
    (f : Fin (ι.ctors s c).nfields) :
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ (ι.ctors s c).caseOrdinary f :
        (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
          (Fin.append ((ι.ctors s c).caseParams ps)
            fun previous : Fin f.val =>
              (ι.ctors s c).caseOrdinary
                (previous.castLE f.isLt.le)) := by
  intro hps
  unfold CtorSig.caseOrdinary CtorSig.caseParams
  simpa [Inductive.caseTele, Tele.append_assoc] using
    ((hB.ctors s c).fieldOrdinary f hps).wkN

theorem WFStrong.caseRecursive_typed
    (hB : (E.get η).block.WFStrong E)
    (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    E[Γ ++ (E.get η).block.caseTele η ls ps ms s c] ⊢ₛ (ι.ctors s c).caseRecursive f :
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

theorem caseFnType_congr (hB : (E.get η).block.WFStrong E) :
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
  have hΓcase := (hB.caseTele (c := c) hΓ hpsSelf hmsSelf).appendCtxWFStrong hΓ
  have hcaseType := hB.caseType_congr hΓcase
    (fun p => caseParams_congr p hps)
    (fun s₁ => caseMotives_congr s₁ hms)
    (hB.caseOrdinary_typed · hpsSelf)
    (hB.caseRecursive_typed · hΓ hpsSelf)
  rw [caseTele, ← Tele.append_assoc] at hcaseType
  have ⟨u, hihs⟩ := Ctx.pi_ofTypes_congrStrong
    (fun f => (hB.ctors s c).ihType_congr hB f hΓ hps hms) hcaseType
  have hpsWk (p) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ₛ (ps₁ p).wkN (ι.ctors s c).nfields ≡
        (ps₂ p).wkN (ι.ctors s c).nfields :
      (E.get η).block.paramType ls
        (fun i => (ps₁ i).wkN (ι.ctors s c).nfields) p := by
    simpa using (hps p).wkN
      (Δ := ((E.get η).block.ctors s c).ordinaryFieldTele η ls ps₁)
  have hfields (f) : E[Γ ++ ((E.get η).block.ctors s c).ordinaryFieldTele
      η ls ps₁] ⊢ₛ Expr.boundVars n (ι.ctors s c).nfields 0 f :
        (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
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
    (((hB.ctors s c).ordinaryTeleAux (ι.ctors s c).nfields le_rfl).mono fun _ => trivial)
    ls (paramSubstEqStrong hps) hrec
  exact IsTypeEq.ofDefEq <| by
    simpa [caseFnType, caseTele, Ctor.fieldTele, Ctx.pi, Tele.foldr_append]

theorem caseFnType_conv
    (hB : (E.get η).block.WFStrong E) {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ n}
    {mins₁ mins₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p) →
    (∀ s₁, E[Γ] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁) →
    E[Γ] ⊢ₛ mins₁ ≡ mins₂ : (E.get η).block.caseFnType η ls ps₁ ms₁ s c →
    E[Γ] ⊢ₛ mins₂ : (E.get η).block.caseFnType η ls ps₂ ms₂ s c :=
  fun hΓ hps hms hmin => (caseFnType_congr hB hΓ hps hms).convStrong hmin.right

theorem WFStrong.caseBinders
    {Γ : Ctx ζ ℓ 0 (ι.nparams + ι.nsorts)}
    (hB : (E.get η).block.WFStrong E)
    (hΓ : E[Γ] ⊢ₛ ok)
    (hps : ∀ p, E[Γ] ⊢ₛ Expr.var (p.castLE (by omega)) :
      (E.get η).block.paramType ls
        (fun p => Expr.var (p.castLE (by omega))) p)
    (hms : ∀ s, E[Γ] ⊢ₛ Expr.var ⟨ι.nparams + s.val, by omega⟩ :
        (E.get η).block.motiveType η ls
          (fun p => Expr.var (p.castLE (by omega))) l s) :
    WFTeleStrong E (fun _ => True) Γ
      ((E.get η).block.caseBinders η ls) := by
  apply WFTeleStrong.ofTypes
  intro tag
  obtain ⟨⟨s, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
    ⟨_, Fin.encodeSigma_decodeSigma ..⟩
  have ⟨v, ht⟩ := (caseFnType_congr hB (c := c) hΓ hps hms).isType.1
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
  have hparamVars (p : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params] ⊢ₛ Expr.var p :
        (E.get η).block.paramType ls Expr.var p := by
    simpa using hΓparams.var p
  have hms := hB.motiveBinders (l := l) hΓparams hparamVars
  have hΓmotives := hms.appendCtxWFStrong hΓparams
  have hparamMotives (p : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l] ⊢ₛ Expr.var (p.castLE (by omega)) :
          (E.get η).block.paramType ls
            (fun p => Expr.var (p.castLE (by omega))) p := by
    simpa [Fin.castAdd] using (hparamVars p).wkN
      (Δ := (E.get η).block.motiveBinders η ls l)
  have hmins := hB.caseBinders hΓmotives hparamMotives
    (hB.motiveBinders_var · hΓparams hparamVars)
  have hΓcases := hmins.appendCtxWFStrong hΓmotives
  let casesEnd := ι.nparams + ι.nsorts + Fin.sum ι.nctors
  let ps : Fin ι.nparams → Expr ζ ℓ casesEnd :=
    fun p => .var (p.castLE (by omega))
  have hparamCases (p : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls] ⊢ₛ ps p : (E.get η).block.paramType ls ps p := by
    simpa [Fin.castAdd] using (hparamMotives p).wkN
      (Δ := (E.get η).block.caseBinders η ls)
  have his := hB.indexTele (s := s) hparamCases
  have hΓindices := his.appendCtxWFStrong hΓcases
  have hparamIndices (p : Fin ι.nparams) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ₛ (ps p).wkN (ι.nindices s) :
          (E.get η).block.paramType ls
            (fun p => (ps p).wkN (ι.nindices s)) p := by
    simpa using (hparamCases p).wkN
  have hindexVars (i : Fin (ι.nindices s)) :
      E[Ctx.instL ls (E.get η).block.params ++
          (E.get η).block.motiveBinders η ls l ++
          (E.get η).block.caseBinders η ls ++
          (E.get η).block.indexTele ls s ps] ⊢ₛ Expr.var ⟨casesEnd + i.val, by omega⟩ :
          (E.get η).block.indexType ls s
            (fun p => (ps p).wkN (ι.nindices s))
            (fun i => Expr.var ⟨casesEnd + i.val, by omega⟩) i := by
    have hv := hΓindices.var (Fin.natAdd casesEnd i)
    rw [Inductive.indexTele_get] at hv
    simpa [Fin.natAdd] using hv
  have hmaj := DefeqStrong.indDF hparamIndices hindexVars
  have hpsMotives : WFTeleStrong E (fun _ => True) .nil
      (Ctx.instL ls (E.get η).block.params ++
        (E.get η).block.motiveBinders η ls l) :=
    hpsTele.append <| by simpa using hms
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
  exact .snoc (hpsMotivesCases.append hisTele)
    ⟨(E.get η).block.level.inst ls, trivial, by
      simpa [casesEnd, ps] using hmaj⟩

theorem WFStrong.weakenEnv
    {entry : Entry ζ sig} (h : I.WFStrong E) :
    (I.map (.step .refl)).WFStrong (E.snoc entry) where
  params := by simpa [map, Ctx.weakenEnv] using h.params.weakenEnv
  indices s := by simpa [map, Ctx.weakenEnv] using (h.indices s).weakenEnv
  ctors s c := by simpa [map] using (h.ctors s c).weakenEnv

theorem iotaLhs_hasTypeStrong
    {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ}
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Expr ζ ℓ n}
    (hctor : ((E.get η).block.ctors s c).WFStrong E (E.get η).block)
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c : (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ₛ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls ((E.get η).block.params ++
        ((E.get η).block.ctors s c).ordinaryTele) →
    E[Γ] ⊢ₛ (E.get η).block.iotaType η ls ps ms s c fds recFds : .sort l →
    E[Γ] ⊢ₛ (E.get η).block.iotaLhs η ls l ps ms mins s c fds recFds :
        (E.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hΓ hps hms hmins hfields hrecFields hσ hresult
  have his := fun i => hctor.targetIndex i hσ
  have hmaj := DefeqStrong.ctorDF hps hfields hrecFields
    (fun f => hctor.ordinaryFieldExprStrong f hps hfields)
    (fun f => (hctor.recursiveFieldExprStrong rfl f hΓ hps hfields).choose_spec)
    (DefeqStrong.indDF hps his)
  exact .recrDF hallowed hps hms hmins his hmaj hresult

theorem WFStrong.iotaRhs_hasTypeStrong
    {η : Head ζ (.inductive ι)} (hB : (E.get η).block.WFStrong E)
    {mins : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) → Expr ζ ℓ n}
    (hallowed : (E.get η).block.RecAllowed l) :
    E[Γ] ⊢ₛ ok →
    (∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p) →
    (∀ s, E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps l s) →
    (∀ s c, E[Γ] ⊢ₛ mins s c :
      (E.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, E[Γ] ⊢ₛ fds f :
      (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, E[Γ] ⊢ₛ recFds f :
      (((E.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    E[Γ] ⊢ₛ (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
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
      (E.get η).block.caseType η ls ps ms s c : .sort l := by
    have h := hB.caseType_congr
      ((hB.caseTele hΓ hps hms).appendCtxWFStrong hΓ)
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
  have hxsA : ∀ p : Fin (ι.ctors s c).nfields, E[Γ] ⊢ₛ fds p :
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
        (Subst.liftN (Fin.append Subst.id fds) (ι.ctors s c).nrecFields) typ :=
    have ⟨u, h⟩ := Ctx.pi_isTypeStrong hΓcase hcaseType
    ⟨u, h.substitution hσAlift⟩
  have hxsB : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ₛ recFds f :
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
  have hxsB' : ∀ f : Fin (ι.ctors s c).nrecFields, E[Γ] ⊢ₛ recFds f :
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
  have hC := Ctx.pi_applyFamilyStrong (P := fun _ => True) hΓ (hΔih.substitution hσAB)
    ⟨l, hcaseType.substitution (SubstWFStrong.liftN hΔih hσAB)⟩ hxsC hB'
  simp at hC
  change E[Γ] ⊢ₛ (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
    ((E.get η).block.caseType η ls ps ms s c).subst
      ((ι.ctors s c).caseSubst fds recFds
        ((E.get η).block.iotaIHs η ls l ps ms mins s c fds recFds)) at hC
  simpa! [caseType, iotaType] using hC

end Inductive

end Recursor

variable {ζ₁ ζ₂ : Sigs} {ι : IndSig}

def Inductive.ctorTypeFn (I : Inductive ζ ι) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Expr ζ ι.nlevels 0 :=
  I.params.lam ((I.ctors s c).ordinaryTele.pi (.sort I.level))

@[simp] theorem Inductive.ctorTypeFn_map (I : Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.ctorTypeFn s c).map pre = (I.map pre).ctorTypeFn s c := by
  simp! [ctorTypeFn, map]

theorem Inductive.WFStrong.ctorTypeFn {I : Inductive ζ ι} (hI : I.WFStrong E)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    ∃ u, E[(#t[] : Ctx ζ ι.nlevels 0 0)] ⊢ₛ I.ctorTypeFn s c : I.params.pi (.sort u) :=
  have hparams : E[I.params] ⊢ₛ ok := by
    simpa using hI.params.appendCtxWFStrong .nil
  have hfields :=
    ((hI.ctors s c).ordinaryTeleAux _ le_rfl).appendCtxWFStrong hparams
  have ⟨u, ht⟩ := Ctx.pi_isTypeStrong hfields (.sortDF (l := I.level))
  ⟨u, Ctx.lam_congrStrong (by simpa using hparams) (by simpa using ht)⟩

end Metalean
