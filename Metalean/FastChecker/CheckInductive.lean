/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Infer
public import Metalean.FastChecker.WF
public import Metalean.Level.Quot.Order
public import Metalean.Typing.Inductive
import Metalean.Typing.Env
import Metalean.Typing.Telescope
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable {ζ : Sigs} (L : Literals) (F : FEnv) (ℓ : Nat) (hints : Array Export.Hints)
  (accel : Accel L F)

def TeleWFSpec (G : FCtx) (P : Level ℓ → Prop) (ts : FCtx) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃b : Nat⦄ ⦃Δ₀ : Ctx ζ ℓ n b⦄,
  Sem L F G E Γ →
  FCtx.Denotes L ⟨ζ, E⟩ ts Δ₀ →
  ∃ Δ : Ctx ζ ℓ n b, FCtx.Denotes L ⟨ζ, E⟩ ts Δ ∧ Metalean.TeleWF E P Γ Δ

def TeleEntriesSpec (G : FCtx) (Q : FLevel → Bool) (ts : FCtx) : Prop :=
  ∀ j (hj : j < ts.size),
  ∃ l, SortedAtSpec L F ℓ (G ++ ts.extract 0 j) ts[j] l ∧ Q l = true

variable {L F ℓ hints accel}

theorem TeleWFSpec.ofSigma {G : FCtx} {P : Level ℓ → Prop} {Q : FLevel → Bool}
    {ts : FCtx}
    (hQ : ∀ {l : FLevel} {l' : RawLevel ℓ}, FLevel.Denotes l l' → Q l = true → P ⟦l'⟧) :
    TeleEntriesSpec L F ℓ G Q ts →
    ∀ {E : Σ ζ, Env ζ} {n : Nat} {Γ : Ctx E.1 ℓ 0 n} {b : Nat} {Δ₀ : Ctx E.1 ℓ n b},
    Sem L F G E.2 Γ →
    FCtx.Denotes L E ts Δ₀ →
    ∃ Δ : Ctx E.1 ℓ n b, FCtx.Denotes L E ts Δ ∧ Metalean.TeleWF E.2 P Γ Δ := by
  intro h E _ _ _ _ hS hΔ₀
  induction hΔ₀ with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | @snoc ts₀ b Δ₀ ft t hΔ₀ ht ih =>
    have hpre : ∀ j, j ≤ ts₀.size → (ts₀.push ft).extract 0 j = ts₀.extract 0 j := by
      intro j hj
      rw [Array.extract_push_of_le hj]
    have h₀ : TeleEntriesSpec L F ℓ G Q ts₀ := by
      intro j hj
      have ⟨l, hl, hQl⟩ := h j (by simp; omega)
      rw [hpre j (by omega)] at hl
      have hidx : (ts₀.push ft)[j]'(by simp; omega) = ts₀[j] := Array.getElem_push_lt hj
      rw [hidx] at hl
      exact ⟨l, hl, hQl⟩
    have ⟨Δ, hΔ, hwf⟩ := ih h₀
    have ⟨l, hl, hQl⟩ := h ts₀.size (by simp)
    rw [hpre ts₀.size le_rfl, Array.extract_size] at hl
    have ⟨t', l', ht', hl', hty⟩ := hl (hS.append hΔ hwf) (by simpa using ht)
    exact ⟨Δ.snoc t', hΔ.snoc (by simpa using ht'), .snoc hwf ⟨⟦l'⟧, hQ hl' hQl, hty⟩⟩

theorem TeleWFSpec.of {G : FCtx} {P : Level ℓ → Prop} {Q : FLevel → Bool}
    {ts : FCtx}
    (hQ : ∀ {l : FLevel} {l' : RawLevel ℓ}, FLevel.Denotes l l' → Q l = true → P ⟦l'⟧) :
    TeleEntriesSpec L F ℓ G Q ts →
    TeleWFSpec L F ℓ G P ts := fun h {ζ E} _ _ _ _ hS hΔ =>
  TeleWFSpec.ofSigma hQ h (E := ⟨ζ, E⟩) hS hΔ

variable (L F ℓ hints accel)

def checkTeleEntries (G : FCtx) (Q : FLevel → Bool) (ts : FCtx) :
    CheckM L F ℓ (PLift (TeleEntriesSpec L F ℓ G Q ts)) :=
  Array.forallM ts
    (fun j hj => ∃ l, SortedAtSpec L F ℓ (G ++ ts.extract 0 j) ts[j] l ∧ Q l = true)
    fun j hj => do
      let r ← inferSortedLevel L F ℓ hints accel (G ++ ts.extract 0 j) ts[j]
      let hQ ← guardProofOr (Q r.1 = true) (Failure.reject .fieldLevel)
      pure ⟨r.1, r.2.down, hQ.down⟩

def checkTele (G : FCtx) (P : Level ℓ → Prop) (Q : FLevel → Bool)
    (hQ : ∀ {l : FLevel} {l' : RawLevel ℓ}, FLevel.Denotes l l' → Q l = true → P ⟦l'⟧)
    (ts : FCtx) : CheckM L F ℓ (PLift (TeleWFSpec L F ℓ G P ts)) := do
  let ⟨h⟩ ← checkTeleEntries L F ℓ hints accel G Q ts
  pure ⟨TeleWFSpec.of hQ h⟩

def IdxSpec (G : FCtx) (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts)
    (us : Array FLevel) (ps is : FCtx) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃I : Inductive ζ ι⦄
    ⦃ls' : Fin ι.nlevels → RawLevel ℓ⦄ ⦃σ : Subst ζ ℓ ι.nparams n⦄
    ⦃is₀ : Fin (ι.nindices s) → Expr ζ ℓ n⦄ (hus : us.size = ι.nlevels),
  Sem L F G E Γ →
  (hI : FInductive.Denotes L ⟨ζ, E⟩ fI I) →
  Metalean.TeleWF E (fun _ => True) I.params (I.indices s) →
  (∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (ls' i)) →
  ArgsDenote L ⟨ζ, E⟩ ps σ →
  (∀ p, E[Γ] ⊢ σ p : I.paramType (⟦ls' ·⟧) σ p) →
  ArgsDenote L ⟨ζ, E⟩ is is₀ →
  ∃ is' : Fin (ι.nindices s) → Expr ζ ℓ n,
    ArgsDenote L ⟨ζ, E⟩ is is' ∧ I.IdxWF E Γ s (⟦ls' ·⟧) σ is'

def checkIdx (G : FCtx) (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts)
    (us : Array FLevel) (ps is : FCtx) (hsI : s.val < fI.indices.size)
    (his : ∀ i : Fin (ι.nindices s), i.val < is.size)
    (hrow : ∀ i : Fin (ι.nindices s), i.val < fI.indices[s.val].size) :
    CheckM L F ℓ (PLift (IdxSpec L F ℓ G ι fI s us ps is)) := do
  let ⟨h⟩ ← Fin.sequenceM fun i : Fin (ι.nindices s) =>
    checkTyped L F ℓ hints accel G (is[i.val]'(his i))
      (fI.indexType us ps s.val hsI is i.val (hrow i))
  pure ⟨fun {_ _ _ _ I ls' σ _} hus hS hI hidx hus' hps hσ his₀ =>
    have ⟨is', hisD, hisT⟩ := TypedSpec.fixArgs hS his₀.size
      (fun e i => I.indexType (⟦ls' ·⟧) s σ e i) his₀.denotes
      (fun _ he i => hI.indexType hus hus' hps s ⟨his₀.size, he⟩ i)
      (fun _ i he => Inductive.indexType_isType hidx i hS.ctxWF hσ he)
      h
    ⟨is', ⟨his₀.size, hisD⟩, hisT⟩⟩

def levelOKB (ι : IndSig) (fI : FInductive) (l : FLevel) : Bool :=
  match l.toRaw ι.nlevels, fI.level.toRaw ι.nlevels with
  | some a, some b => decide (Level.imax ⟦a⟧ ⟦b⟧ ≤ (⟦b⟧ : Level ι.nlevels))
  | _, _ => false

theorem levelOK_of_levelOKB {E : Env ζ} {L : Literals} {ι : IndSig} {fI : FInductive}
    {I : Inductive ζ ι}
    {l : FLevel}
    {l' : RawLevel ι.nlevels} (h : levelOKB ι fI l = true) :
    FInductive.Denotes L ⟨ζ, E⟩ fI I →
    FLevel.Denotes l l' →
    I.LevelOK ⟦l'⟧ := by
  intro hI hl
  have ⟨lv, hlv, hlv'⟩ := hI.level
  unfold levelOKB at h
  simp only [FLevel.toRaw_eq_of_denotes hl, FLevel.toRaw_eq_of_denotes hlv, decide_eq_true_eq] at h
  change Level.imax ⟦l'⟧ I.level ≤ I.level
  rw [← hlv']
  exact h

theorem Ctor.ordinaryTeleAux_congr {ι : IndSig} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
    {ctor₁ ctor₂ : Ctor ζ ι s csig} (count : Nat) (hcount : count ≤ csig.nfields)
    (h : ∀ f : Fin csig.nfields, f.val < count → ctor₁.ordinary f = ctor₂.ordinary f) :
    ctor₁.ordinaryTeleAux count hcount = ctor₂.ordinaryTeleAux count hcount := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Ctor.ordinaryTeleAux]
    rw [ih (by omega) fun f hf => h f (by omega), h ⟨count, by omega⟩ (Nat.lt_succ_self count)]

theorem Inductive.paramVars_typed {E : Env ζ} {ι : IndSig} {I : Inductive ζ ι} {k : Nat}
    {Δ : Ctx ζ ι.nlevels ι.nparams (ι.nparams + k)} (hΓ : E[I.params] ⊢ ok)
    (p : Fin ι.nparams) :
    E[I.params ++ Δ] ⊢ (.var ⟨p.val, by omega⟩ : Expr ζ ι.nlevels (ι.nparams + k)) :
      I.paramType Level.param (fun q => .var ⟨q.val, by omega⟩) p := by
  have h : E[I.params] ⊢ Expr.var p : I.paramType Level.param Expr.var p := by
    rw [← Inductive.paramType_eq_get_subst]
    simpa [show (Expr.var : Subst ζ ι.nlevels ι.nparams ι.nparams) = Subst.id from rfl] using hΓ.var p
  simpa [Fin.castAdd, Fin.castLE] using h.wkN (Δ := Δ)

theorem Inductive.paramArgs_wkN {E : Env ζ} {ι : IndSig} {I : Inductive ζ ι} {ℓ n k : Nat}
    {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n (n + k)} {ls : Fin ι.nlevels → Level ℓ}
    {σ : Fin ι.nparams → Expr ζ ℓ n}
    (h : ∀ p, E[Γ] ⊢ σ p : I.paramType ls σ p) (p : Fin ι.nparams) :
    E[Γ ++ Δ] ⊢ (σ p).wkN k : I.paramType ls (fun q => (σ q).wkN k) p := by
  simpa using (h p).wkN (Δ := Δ)

def OrdFieldSpec (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (f : Fin (ι.ctors s c).nfields) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃I : Inductive ζ ι⦄ ⦃ctor : Ctor ζ ι s (ι.ctors s c)⦄,
  Sem L F fI.params E I.params →
  FInductive.Denotes L ⟨ζ, E⟩ fI I →
  (hc : FCtor.Denotes L ⟨ζ, E⟩ fctor ctor) →
  Metalean.TeleWF E I.LevelOK I.params (ctor.ordinaryTeleAux f.val f.isLt.le) →
  ∃ fd : Field ζ ι f.val,
    FField.Denotes L ⟨ζ, E⟩ (fctor.ordinary[f.val]'(hc.ordinarySize.symm ▸ f.isLt)) fd ∧
    Metalean.FieldWF E I (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le) fd

def OrdFieldsSpec (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃I : Inductive ζ ι⦄ ⦃ctor₀ : Ctor ζ ι s (ι.ctors s c)⦄,
  Sem L F fI.params E I.params →
  FInductive.Denotes L ⟨ζ, E⟩ fI I →
  FCtor.Denotes L ⟨ζ, E⟩ fctor ctor₀ →
  ∃ ctor : Ctor ζ ι s (ι.ctors s c), FCtor.Denotes L ⟨ζ, E⟩ fctor ctor ∧
    ∀ f : Fin (ι.ctors s c).nfields,
    Metalean.FieldWF E I (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le) (ctor.ordinary f)

variable {L F ℓ hints accel}

theorem OrdFieldsSpec.of {ι : IndSig} {fI : FInductive} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {fctor : FCtor} :
    (∀ f, OrdFieldSpec L F ι fI s c fctor f) →
    OrdFieldsSpec L F ι fI s c fctor := by
  intro h ζ E I ctor₀ hS hI hc₀
  suffices this : ∀ count, count ≤ (ι.ctors s c).nfields →
      ∃ ctor : Ctor ζ ι s (ι.ctors s c), FCtor.Denotes L ⟨ζ, E⟩ fctor ctor ∧
        ∀ f : Fin (ι.ctors s c).nfields, f.val < count →
        Metalean.FieldWF E I (I.params ++ ctor.ordinaryTeleAux f.val f.isLt.le) (ctor.ordinary f) by
    have ⟨ctor, hc, hf⟩ := this _ le_rfl
    exact ⟨ctor, hc, fun f => hf f f.isLt⟩
  intro count
  induction count with
  | zero => exact fun _ => ⟨ctor₀, hc₀, fun f hf => absurd hf (Nat.not_lt_zero _)⟩
  | succ count ih =>
    intro hcount
    have ⟨ctor, hc, hf⟩ := ih (by omega)
    have hwf : Metalean.TeleWF E I.LevelOK I.params (ctor.ordinaryTeleAux count (by omega)) :=
      Ctor.wfOrdinaryTeleAux count (by omega) fun g => hf (g.castLE (by omega)) g.isLt
    have ⟨fd, hfdD, hfdWF⟩ := h ⟨count, by omega⟩ hS hI hc hwf
    have hne (f : Fin (ι.ctors s c).nfields) (hne : f ≠ ⟨count, by omega⟩) :
        Function.update ctor.ordinary ⟨count, by omega⟩ fd f = ctor.ordinary f :=
      Function.update_of_ne hne _ _
    have htele (k : Nat) (hk : k ≤ count) :
        ({ ctor with ordinary := Function.update ctor.ordinary ⟨count, by omega⟩ fd } :
          Ctor ζ ι s (ι.ctors s c)).ordinaryTeleAux k (by omega) =
        ctor.ordinaryTeleAux k (by omega) :=
      Ctor.ordinaryTeleAux_congr k _ fun f hfk => hne f (by
        intro heq
        rw [heq] at hfk
        exact absurd hfk (by simp; omega))
    refine ⟨{ ctor with ordinary := Function.update ctor.ordinary ⟨count, by omega⟩ fd },
      ⟨hc.ordinarySize, ?_, hc.recursiveSize, hc.recursive, hc.targetSize, hc.targetIndices⟩, ?_⟩
    · intro f
      by_cases hff : f = ⟨count, by omega⟩
      · rw [hff]
        simpa using hfdD
      · simpa [hne f hff] using hc.ordinary f
    · intro f hfl
      by_cases hff : f = ⟨count, by omega⟩
      · rw [hff]
        simpa [htele count le_rfl] using hfdWF
      · have hlt : f.val < count := by
          have : f.val ≠ count := fun he => hff (Fin.ext he)
          omega
        simpa [hne f hff, htele f.val hlt.le] using hf f hlt

variable (L F ℓ hints accel)

def checkOrdField (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (hord : ∀ f : Fin (ι.ctors s c).nfields, f.val < fctor.ordinary.size)
    (f : Fin (ι.ctors s c).nfields) :
    CheckM L F ι.nlevels (PLift (OrdFieldSpec L F ι fI s c fctor f)) := do
  let ⟨ht⟩ ← checkTyped L F ι.nlevels hints accel (fI.params ++ fctor.ordinaryTemplates f.val)
    (fctor.ordinary[f.val]'(hord f)).type (.sort (fctor.ordinary[f.val]'(hord f)).level)
  let ⟨hOK⟩ ← guardProofOr (levelOKB ι fI (fctor.ordinary[f.val]'(hord f)).level = true)
    (Failure.reject .fieldLevel)
  pure ⟨fun {_ E I ctor} hS hI hc hwf => by
    have ⟨l', hl', hlevel⟩ := (hc.ordinary f).level
    have ⟨e, t, he, htd, hty⟩ := ht (hS.append (hc.ordinaryTele f.val f.isLt.le) hwf)
      (hc.ordinary f).type (.sort hl')
    have .sort hl'' := htd
    obtain rfl := hl''.unique hl'
    refine ⟨⟨e, (ctor.ordinary f).level⟩, ⟨he, _, hl', hlevel⟩, ⟨?_, ?_⟩⟩
    · have h : E[_] ⊢ e : .sort (ctor.ordinary f).level := hlevel ▸ hty
      exact h
    · change I.LevelOK (ctor.ordinary f).level
      rw [← hlevel]
      exact levelOK_of_levelOKB hOK hI hl'⟩

def checkOrdFields (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (hord : ∀ f : Fin (ι.ctors s c).nfields, f.val < fctor.ordinary.size) :
    CheckM L F ι.nlevels (PLift (OrdFieldsSpec L F ι fI s c fctor)) := do
  let ⟨h⟩ ← Fin.sequenceM fun f => checkOrdField L F hints accel ι fI s c fctor hord f
  pure ⟨OrdFieldsSpec.of h⟩

def FCtor.ordinaryContext (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) : FCtx :=
  fI.params ++ fctor.ordinaryTemplates (ι.ctors s c).nfields

def HeaderWF {ζ : Sigs} (E : Env ζ) {ι : IndSig} (I : Inductive ζ ι) : Prop :=
  E[I.params] ⊢ ok ∧ ∀ t, Metalean.TeleWF E (fun _ => True) I.params (I.indices t)

def RecFieldSpec (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (r : Fin (ι.ctors s c).nrecFields) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃I : Inductive ζ ι⦄ ⦃ctor : Ctor ζ ι s (ι.ctors s c)⦄,
  Sem L F fI.params E I.params →
  FInductive.Denotes L ⟨ζ, E⟩ fI I →
  HeaderWF E I →
  (hc : FCtor.Denotes L ⟨ζ, E⟩ fctor ctor) →
  Metalean.TeleWF E I.LevelOK I.params ctor.ordinaryTele →
  ∃ fd : RecField ζ ι (ι.ctors s c).nfields ((ι.ctors s c).recursiveArity r)
      ((ι.ctors s c).recursiveTarget r),
    FRecField.Denotes L ⟨ζ, E⟩ (fctor.recursive[r.val]'(hc.recursiveSize.symm ▸ r.isLt)) fd ∧
    Metalean.RecFieldWF E I (I.params ++ ctor.ordinaryTele) fd

def checkRecField (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (hrec : ∀ r : Fin (ι.ctors s c).nrecFields, r.val < fctor.recursive.size)
    (hindicesLt : ∀ t : Fin ι.nsorts, t.val < fI.indices.size)
    (hindexLt : ∀ (t : Fin ι.nsorts) (i : Fin (ι.nindices t)),
      i.val < (fI.indices[t.val]'(hindicesLt t)).size)
    (r : Fin (ι.ctors s c).nrecFields) :
    CheckM L F ι.nlevels (PLift (RecFieldSpec L F ι fI s c fctor r)) := do
  let target := (ι.ctors s c).recursiveTarget r
  let ⟨htele⟩ ← checkTeleEntries L F ι.nlevels hints accel (fctor.ordinaryContext ι fI s c)
    (levelOKB ι fI) (fctor.recursive[r.val]'(hrec r)).tele
  let ⟨hsize⟩ ← guardProofOr
    ((fctor.recursive[r.val]'(hrec r)).indices.size = ι.nindices target) (Failure.reject .arity)
  let ⟨hidx⟩ ← checkIdx L F ι.nlevels hints accel
    (fctor.ordinaryContext ι fI s c ++ (fctor.recursive[r.val]'(hrec r)).tele) ι fI target
    (FLevel.params ι.nlevels) (FExpr.fvars 0 ι.nparams)
    (fctor.recursive[r.val]'(hrec r)).indices (hindicesLt target)
    (fun i => Nat.lt_of_lt_of_eq i.isLt hsize.symm) (hindexLt target)
  pure ⟨fun {_ E I ctor} hS hI hH hc hwf => by
    have hfd := hc.recursive r
    have hS₀ := hS.append (hc.ordinaryTele (ι.ctors s c).nfields le_rfl) hwf
    have ⟨Δ, hΔ, hΔwf⟩ :=
      TeleWFSpec.of (fun hl hQ => levelOK_of_levelOKB hQ hI hl) htele hS₀ hfd.tele
    have hσ (p : Fin ι.nparams) :
        E[I.params ++ ctor.ordinaryTele ++ Δ] ⊢ (.var ⟨p.val, by omega⟩ : Expr _ ι.nlevels _) :
          I.paramType Level.param (fun q => .var ⟨q.val, by omega⟩) p := by
      simpa using Inductive.paramArgs_wkN (Δ := Δ) (Inductive.paramVars_typed hH.1) p
    have ⟨is', hisD, hisT⟩ := hidx (ls' := fun i => RawLevel.param i) (by simp)
      (hS₀.append hΔ hΔwf) hI (hH.2 _)
      (fun i => FLevel.denotes_params i) (ArgsDenote.params (by omega)) hσ
      ⟨hfd.size, hfd.indices⟩
    exact ⟨⟨Δ, is'⟩, ⟨hΔ, hfd.size, hisD.denotes⟩, ⟨hΔwf, hisT⟩⟩⟩

def CtorDeclSpec (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃I : Inductive ζ ι⦄ ⦃ctor₀ : Ctor ζ ι s (ι.ctors s c)⦄,
  Sem L F fI.params E I.params →
  FInductive.Denotes L ⟨ζ, E⟩ fI I →
  HeaderWF E I →
  FCtor.Denotes L ⟨ζ, E⟩ fctor ctor₀ →
  ∃ ctor : Ctor ζ ι s (ι.ctors s c), FCtor.Denotes L ⟨ζ, E⟩ fctor ctor ∧ Metalean.CtorWF E I ctor

def checkCtorDecl (ι : IndSig) (fI : FInductive) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fctor : FCtor) (hindicesLt : ∀ t : Fin ι.nsorts, t.val < fI.indices.size)
    (hindexLt : ∀ (t : Fin ι.nsorts) (i : Fin (ι.nindices t)),
      i.val < (fI.indices[t.val]'(hindicesLt t)).size) :
    CheckM L F ι.nlevels (PLift (CtorDeclSpec L F ι fI s c fctor)) := do
  let ⟨hordSize⟩ ← guardProofOr (fctor.ordinary.size = (ι.ctors s c).nfields) (Failure.reject .arity)
  let ⟨hrecSize⟩ ← guardProofOr (fctor.recursive.size = (ι.ctors s c).nrecFields)
    (Failure.reject .arity)
  let ⟨htgtSize⟩ ← guardProofOr (fctor.targetIndices.size = ι.nindices s) (Failure.reject .arity)
  let ⟨hord⟩ ← checkOrdFields L F hints accel ι fI s c fctor
    fun f => Nat.lt_of_lt_of_eq f.isLt hordSize.symm
  let ⟨hrec⟩ ← Fin.sequenceM fun r =>
    checkRecField L F hints accel ι fI s c fctor
      (fun r => Nat.lt_of_lt_of_eq r.isLt hrecSize.symm) hindicesLt hindexLt r
  let ⟨htgt⟩ ← checkIdx L F ι.nlevels hints accel (fctor.ordinaryContext ι fI s c) ι fI s
    (FLevel.params ι.nlevels) (FExpr.fvars 0 ι.nparams) fctor.targetIndices (hindicesLt s)
    (fun i => Nat.lt_of_lt_of_eq i.isLt htgtSize.symm) (hindexLt s)
  pure ⟨fun {_ _ _ _} hS hI hH hc₀ => by
    have ⟨ctor, hc, hfields⟩ := hord hS hI hc₀
    have hwf : Metalean.TeleWF _ _ _ ctor.ordinaryTele :=
      Ctor.wfOrdinaryTeleAux (ι.ctors s c).nfields le_rfl fun f => hfields (f.castLE le_rfl)
    have hrecs := fun r => hrec r hS hI hH hc hwf
    choose rfs hrfD hrfWF using hrecs
    have ⟨is', hisD, hisT⟩ := htgt (ls' := fun i => RawLevel.param i) (by simp)
      (hS.append (hc.ordinaryTele (ι.ctors s c).nfields le_rfl) hwf) hI (hH.2 s)
      (fun i => FLevel.denotes_params i) (ArgsDenote.params (by omega))
      (fun p => Inductive.paramVars_typed hH.1 p) ⟨hc.targetSize, hc.targetIndices⟩
    have hEq (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) :
        ({ ctor with recursive := rfs, targetIndices := is' } :
          Ctor _ ι s (ι.ctors s c)).ordinaryTeleAux k hk = ctor.ordinaryTeleAux k hk :=
      Ctor.ordinaryTeleAux_congr k hk fun _ _ => rfl
    have hEq' :
        ({ ctor with recursive := rfs, targetIndices := is' } :
          Ctor _ ι s (ι.ctors s c)).ordinaryTele = ctor.ordinaryTele := hEq _ le_rfl
    refine ⟨{ ctor with recursive := rfs, targetIndices := is' },
      ⟨hc.ordinarySize, hc.ordinary, hc.recursiveSize, hrfD, hc.targetSize, hisD.denotes⟩,
      ⟨fun f => ?_, fun r => ?_, ?_⟩⟩
    · rw [hEq]
      exact hfields f
    · rw [hEq']
      exact hrfWF r
    · rw [hEq']
      exact hisT⟩

def InductiveWFSpec (ι : IndSig) (fI : FInductive) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃I₀ : Inductive ζ ι⦄,
  FEnv.Denotes L F E →
  EnvWF E →
  L.NatTrust E →
  FInductive.Denotes L ⟨ζ, E⟩ fI I₀ →
  ∃ I : Inductive ζ ι, FInductive.Denotes L ⟨ζ, E⟩ fI I ∧ Metalean.InductiveWF E I

def checkInductive (ι : IndSig) (fI : FInductive) :
    CheckM L F ι.nlevels (PLift (InductiveWFSpec L F ι fI)) := do
  let ⟨hparams⟩ ← checkTele L F ι.nlevels hints accel #[] (fun _ => True) (fun _ => true)
    (fun _ _ => trivial) fI.params
  let ⟨hindicesSize⟩ ← guardProofOr (fI.indices.size = ι.nsorts) (Failure.reject .arity)
  have hindicesLt : ∀ t : Fin ι.nsorts, t.val < fI.indices.size :=
    fun t => Nat.lt_of_lt_of_eq t.isLt hindicesSize.symm
  let ⟨hrows⟩ ← Fin.sequenceM fun t : Fin ι.nsorts =>
    guardProofOr ((fI.indices[t.val]'(hindicesLt t)).size = ι.nindices t) (Failure.reject .arity)
  have hindexLt : ∀ (t : Fin ι.nsorts) (i : Fin (ι.nindices t)),
      i.val < (fI.indices[t.val]'(hindicesLt t)).size :=
    fun t i => Nat.lt_of_lt_of_eq i.isLt (hrows t).symm
  let ⟨hindices⟩ ← Fin.sequenceM fun t : Fin ι.nsorts =>
    checkTele L F ι.nlevels hints accel fI.params
      (fun _ => True)
      (fun _ => true)
      (fun _ _ => trivial)
      (fI.indices[t.val]'(hindicesLt t))
  let ⟨hctorsSize⟩ ← guardProofOr (fI.ctors.size = ι.nsorts) (Failure.reject .arity)
  have hctorsLt : ∀ t : Fin ι.nsorts, t.val < fI.ctors.size :=
    fun t => Nat.lt_of_lt_of_eq t.isLt hctorsSize.symm
  let ⟨hctorRows⟩ ← Fin.sequenceM fun t : Fin ι.nsorts =>
    guardProofOr ((fI.ctors[t.val]'(hctorsLt t)).size = ι.nctors t) (Failure.reject .arity)
  have hctorLt : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
      c.val < (fI.ctors[t.val]'(hctorsLt t)).size :=
    fun t c => Nat.lt_of_lt_of_eq c.isLt (hctorRows t).symm
  let ⟨hctors⟩ ← Fin.sequenceM fun t : Fin ι.nsorts =>
    Fin.sequenceM fun c : Fin (ι.nctors t) =>
      checkCtorDecl L F hints accel ι fI t c ((fI.ctors[t.val]'(hctorsLt t))[c.val]'(hctorLt t c))
        hindicesLt hindexLt
  pure ⟨fun {ζ E I₀} hF hE htr hI₀ => by
    have hSnil := Sem.nil (ℓ := ι.nlevels) hF hE htr
    have ⟨Δp, hΔp, hwfp⟩ := hparams hSnil hI₀.params
    have hSp : Sem L F fI.params E Δp := by
      simpa using hSnil.append hΔp hwfp
    have hidx := fun t => hindices t hSp (hI₀.indices t)
    choose Δi hΔi hwfi using hidx
    have hI₁ : FInductive.Denotes L ⟨ζ, E⟩ fI { I₀ with params := Δp, indices := Δi } :=
      ⟨hΔp, hI₀.indicesSize, hΔi, hI₀.level, hI₀.ctorsSize, hI₀.ctorsRow, hI₀.ctors⟩
    have hH : HeaderWF E ({ I₀ with params := Δp, indices := Δi } : Inductive ζ ι) :=
      ⟨hSp.ctxWF, hwfi⟩
    have hcs := fun t c => hctors t c hSp hI₁ hH (hI₀.ctors t c)
    choose cs hcsD hcsWF using hcs
    exact ⟨{ I₀ with params := Δp, indices := Δi, ctors := cs },
      ⟨hΔp, hI₀.indicesSize, hΔi, hI₀.level, hI₀.ctorsSize, hI₀.ctorsRow, hcsD⟩,
      ⟨hwfp, hwfi, fun t c =>
        have h := hcsWF t c
        ⟨fun f => ⟨(h.ordinary f).typeExact, (h.ordinary f).levelOK⟩,
          fun r => ⟨(h.recursive r).tele, (h.recursive r).indices⟩, h.targetIndices⟩⟩⟩⟩

end Metalean.FastChecker
