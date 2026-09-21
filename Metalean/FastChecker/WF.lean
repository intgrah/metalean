/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Control
public import Metalean.FastChecker.CheckLevel
public import Metalean.FastChecker.Inductive
public import Metalean.Frontend.Failure
import Metalean.Meta.IfRfl

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable (L : Literals) (F : FEnv)

def WFSpec (ℓ n k : Nat) (fe : FExpr) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ e : Expr E.1 ℓ n, FExpr.Denotes L E k fe e

def ArrWF (ℓ n k : Nat) (es : FCtx) : Prop :=
  ∀ i (h : i < es.size), WFSpec L F ℓ n k es[i]

def TeleWF (ℓ a : Nat) (ts : FCtx) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄ ⦃b : Nat⦄,
  FEnv.Denotes L F E.2 →
  a + ts.size = b →
  ∃ Δ : Ctx E.1 ℓ a b, FCtx.Denotes L E ts Δ

def EntryWF (fe : FEntry) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ entry : Entry E.1 fe.sig, FEntry.Denotes L E fe entry

def InductiveWF (ι : IndSig) (fI : FInductive) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ I : Inductive E.1 ι, FInductive.Denotes L E fI I

def CtorWF (ι : IndSig) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (fctor : FCtor) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ ctor : Ctor E.1 ι s (ι.ctors s c), FCtor.Denotes L E fctor ctor

def RecFieldWF (ι : IndSig) (nfields arity : Nat) (target : Fin ι.nsorts) (ffd : FRecField) :
    Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ fd : RecField E.1 ι nfields arity target, FRecField.Denotes L E ffd fd

def FieldWF (ι : IndSig) (nfields : Nat) (ffd : FField) : Prop :=
  ∀ ⦃E : Σ ζ, Env ζ⦄,
  FEnv.Denotes L F E.2 →
  ∃ fd : Field E.1 ι nfields, FField.Denotes L E ffd fd

variable {L F}

theorem ArrWF.choose {ℓ n k m : Nat} {es : FCtx} (hes : es.size = m) {E : Σ ζ, Env ζ} :
    ArrWF L F ℓ n k es →
    FEnv.Denotes L F E.2 →
    ∃ es' : Fin m → Expr E.1 ℓ n,
      ∀ i, FExpr.Denotes L E k (es[i.val]'(hes.symm ▸ i.isLt)) (es' i) :=
  fun h hE => Classical.axiomOfChoice fun i : Fin m => h i.val (hes.symm ▸ i.isLt) hE

theorem ArrWF.chooseMinors {ℓ n k : Nat} {ι : IndSig} {es : FCtx}
    (hes : es.size = Fin.sum ι.nctors) {E : Σ ζ, Env ζ} :
    ArrWF L F ℓ n k es →
    FEnv.Denotes L F E.2 →
    ∃ es' : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr E.1 ℓ n, ∀ t c,
      FExpr.Denotes L E k
        (es[(Fin.encodeSigma ι.nctors ⟨t, c⟩).val]'
          (hes.symm ▸ (Fin.encodeSigma ι.nctors ⟨t, c⟩).isLt))
        (es' t c) :=
  fun h hE => Classical.axiomOfChoice fun t => Classical.axiomOfChoice fun c =>
    h (Fin.encodeSigma ι.nctors ⟨t, c⟩).val _ hE

theorem TeleWF.of {ℓ a : Nat} {ts : FCtx} :
    (∀ j (hj : j < ts.size), WFSpec L F ℓ (a + j) 0 ts[j]) →
    TeleWF L F ℓ a ts := by
  intro h E b hE hb
  subst hb
  suffices this : ∀ j (hj : j ≤ ts.size),
      ∃ Δ : Ctx E.1 ℓ a (a + j), FCtx.Denotes L E (ts.extract 0 j) Δ by
    have ⟨Δ, hΔ⟩ := this ts.size le_rfl
    exact ⟨Δ, by simpa using hΔ⟩
  intro j hj
  induction j with
  | zero => exact ⟨.nil, by simpa using FCtx.Denotes.nil⟩
  | succ j ih =>
    have ⟨Δ, hΔ⟩ := ih (by omega)
    have ⟨e, he'⟩ := h j (by omega) hE
    refine ⟨Δ.snoc e, ?_⟩
    have hpush := Array.push_extract_getElem (as := ts) (i := 0) (show j < ts.size by omega)
    rw [Nat.zero_min] at hpush
    rw [← hpush]
    exact .snoc hΔ he'

theorem FieldWF.of {ι : IndSig} {nfields : Nat} {ffd : FField} :
    WFSpec L F ι.nlevels (ι.nparams + nfields) 0 ffd.type →
    LevelWF ι.nlevels ffd.level →
    FieldWF L F ι nfields ffd := by
  intro ht ⟨l', hl'⟩ _ hE
  have ⟨t, ht'⟩ := ht hE
  exact ⟨⟨t, ⟦l'⟧⟩, ht', l', hl', rfl⟩

theorem RecFieldWF.of {ι : IndSig} {nfields arity : Nat} {target : Fin ι.nsorts}
    {ffd : FRecField} (harity : ffd.tele.size = arity)
    (hsize : ffd.indices.size = ι.nindices target) :
    TeleWF L F ι.nlevels (ι.nparams + nfields) ffd.tele →
    ArrWF L F ι.nlevels (ι.nparams + nfields + arity) 0 ffd.indices →
    RecFieldWF L F ι nfields arity target ffd := by
  intro htele hindices _ hE
  have ⟨Δ, hΔ⟩ := htele hE (b := ι.nparams + nfields + arity) (by omega)
  have ⟨is', his'⟩ := hindices.choose hsize hE
  exact ⟨⟨Δ, is'⟩, hΔ, hsize, his'⟩

theorem CtorWF.of {ι : IndSig} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {fctor : FCtor}
    (hord : fctor.ordinary.size = (ι.ctors s c).nfields)
    (hrec : fctor.recursive.size = (ι.ctors s c).nrecFields)
    (htarget : fctor.targetIndices.size = ι.nindices s) :
    (∀ f (hf : f < fctor.ordinary.size), FieldWF L F ι f fctor.ordinary[f]) →
    (∀ r (hr : r < fctor.recursive.size),
      RecFieldWF L F ι (ι.ctors s c).nfields ((ι.ctors s c).recursiveArity ⟨r, hrec ▸ hr⟩)
        ((ι.ctors s c).recursiveTarget ⟨r, hrec ▸ hr⟩) fctor.recursive[r]) →
    ArrWF L F ι.nlevels (ι.nparams + (ι.ctors s c).nfields) 0 fctor.targetIndices →
    CtorWF L F ι s c fctor := by
  intro hord' hrec' htarget' _ hE
  have ⟨ordinary, hordinary⟩ := Classical.axiomOfChoice fun f : Fin (ι.ctors s c).nfields =>
    hord' f.val (hord.symm ▸ f.isLt) hE
  have ⟨recursive, hrecursive⟩ := Classical.axiomOfChoice fun r : Fin (ι.ctors s c).nrecFields =>
    hrec' r.val (hrec.symm ▸ r.isLt) hE
  have ⟨targetIndices, htargetIndices⟩ := htarget'.choose htarget hE
  exact ⟨⟨ordinary, recursive, targetIndices⟩, hord, hordinary, hrec, hrecursive, htarget,
    htargetIndices⟩

theorem InductiveWF.of {ι : IndSig} {fI : FInductive} (hparams : fI.params.size = ι.nparams)
    (hindices : fI.indices.size = ι.nsorts)
    (hrows : ∀ s (hs : s < fI.indices.size), fI.indices[s].size = ι.nindices ⟨s, hindices ▸ hs⟩)
    (hctors : fI.ctors.size = ι.nsorts)
    (hctorRows : ∀ s (hs : s < fI.ctors.size), fI.ctors[s].size = ι.nctors ⟨s, hctors ▸ hs⟩) :
    TeleWF L F ι.nlevels 0 fI.params →
    (∀ s (hs : s < fI.indices.size), TeleWF L F ι.nlevels ι.nparams fI.indices[s]) →
    LevelWF ι.nlevels fI.level →
    (∀ s (hs : s < fI.ctors.size) c (hc : c < fI.ctors[s].size),
      CtorWF L F ι ⟨s, hctors ▸ hs⟩ ⟨c, hctorRows s hs ▸ hc⟩ fI.ctors[s][c]) →
    InductiveWF L F ι fI := by
  intro hparams' hindices' ⟨l', hl'⟩ hctors' _ hE
  have ⟨params, hparams'⟩ := hparams' hE (b := ι.nparams) (by omega)
  have ⟨indices, hindices'⟩ := Classical.axiomOfChoice fun s : Fin ι.nsorts =>
    hindices' s.val (hindices.symm ▸ s.isLt) hE (b := ι.nparams + ι.nindices s)
      (by rw [hrows s.val (hindices.symm ▸ s.isLt)])
  have ⟨ctors, hctors'⟩ := Classical.axiomOfChoice fun s : Fin ι.nsorts =>
    Classical.axiomOfChoice fun c : Fin (ι.nctors s) =>
      hctors' s.val (hctors.symm ▸ s.isLt) c.val
        ((hctorRows s.val (hctors.symm ▸ s.isLt)).symm ▸ c.isLt) hE
  exact ⟨⟨params, indices, ⟦l'⟧, ctors⟩, hparams', hindices, hindices', ⟨l', hl', rfl⟩, hctors,
    fun s => hctorRows s.val (hctors.symm ▸ s.isLt), hctors'⟩

theorem WFSpec.bvar {ℓ n k j : Nat} (hj : j < k) (hn : j < n) : WFSpec L F ℓ n k (.bvar j) :=
  fun {_} _ => ⟨_, .bvar (i := n - j - 1) (by omega) hj⟩

theorem WFSpec.fvar {ℓ n k i : Nat} (hi : i + k < n) : WFSpec L F ℓ n k (.fvar i) :=
  fun {_} _ => ⟨_, .fvar hi⟩

theorem WFSpec.sort {ℓ n k : Nat} {l : FLevel} :
    LevelWF ℓ l →
    WFSpec L F ℓ n k (.sort l) :=
  fun ⟨_, hl⟩ {_} _ => ⟨_, .sort hl⟩

theorem WFSpec.const {ℓ n k pos : Nat} {fe : FEntry} {kind : ConstKind} {nlevels : Nat}
    {ls : Array FLevel} (hfe : F[pos]? = some fe) (hsig : fe.sig = .const kind nlevels)
    (hls : ls.size = nlevels) :
    (∀ i (h : i < ls.size), LevelWF ℓ ls[i]) →
    WFSpec L F ℓ n k (.const pos ls) := by
  intro hls' _ hE
  have ⟨_, hη⟩ := hE.lookup hfe hsig
  have ⟨_, hls'⟩ := LevelWF.choose hls hls'
  exact ⟨_, .const hls hη hls'⟩

theorem WFSpec.ind {ℓ n k pos s : Nat} {ι : IndSig} {fI : FInductive} {ls : Array FLevel}
    {ps is : FCtx} (hfe : F[pos]? = some (.inductive ι fI)) (hs : s < ι.nsorts)
    (hls : ls.size = ι.nlevels) (hps : ps.size = ι.nparams) (his : is.size = ι.nindices ⟨s, hs⟩) :
    (∀ i (h : i < ls.size), LevelWF ℓ ls[i]) →
    ArrWF L F ℓ n k ps →
    ArrWF L F ℓ n k is →
    WFSpec L F ℓ n k (.ind pos s ls ps is) := by
  intro hls' hps' his' _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hls'⟩ := LevelWF.choose hls hls'
  have ⟨_, hps'⟩ := hps'.choose hps hE
  have ⟨_, his'⟩ := his'.choose his hE
  exact ⟨_, .ind (η := η) (s' := ⟨s, hs⟩) hls hps his hη rfl hls' hps' his'⟩

theorem WFSpec.ctor {ℓ n k pos s c : Nat} {ι : IndSig} {fI : FInductive} {ls : Array FLevel}
    {ps fds recFds : FCtx} (hfe : F[pos]? = some (.inductive ι fI)) (hs : s < ι.nsorts)
    (hc : c < ι.nctors ⟨s, hs⟩) (hls : ls.size = ι.nlevels) (hps : ps.size = ι.nparams)
    (hfds : fds.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields)
    (hrecFds : recFds.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields) :
    (∀ i (h : i < ls.size), LevelWF ℓ ls[i]) →
    ArrWF L F ℓ n k ps →
    ArrWF L F ℓ n k fds →
    ArrWF L F ℓ n k recFds →
    WFSpec L F ℓ n k (.ctor pos s c ls ps fds recFds) := by
  intro hls' hps' hfds' hrecFds' _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hls'⟩ := LevelWF.choose hls hls'
  have ⟨_, hps'⟩ := hps'.choose hps hE
  have ⟨_, hfds'⟩ := hfds'.choose hfds hE
  have ⟨_, hrecFds'⟩ := hrecFds'.choose hrecFds hE
  exact ⟨_, .ctor (η := η) (s' := ⟨s, hs⟩) (c' := ⟨c, hc⟩) hls hps hfds hrecFds hη rfl rfl hls'
    hps' hfds' hrecFds'⟩

theorem WFSpec.recr {ℓ n k pos s : Nat} {ι : IndSig} {fI : FInductive} {ls : Array FLevel}
    {l : FLevel} {ps ms mins is : FCtx} {maj : FExpr}
    (hfe : F[pos]? = some (.inductive ι fI)) (hs : s < ι.nsorts) (hls : ls.size = ι.nlevels)
    (hps : ps.size = ι.nparams) (hms : ms.size = ι.nsorts) (hmins : mins.size = Fin.sum ι.nctors)
    (his : is.size = ι.nindices ⟨s, hs⟩) :
    (∀ i (h : i < ls.size), LevelWF ℓ ls[i]) →
    LevelWF ℓ l →
    ArrWF L F ℓ n k ps →
    ArrWF L F ℓ n k ms →
    ArrWF L F ℓ n k mins →
    ArrWF L F ℓ n k is →
    WFSpec L F ℓ n k maj →
    WFSpec L F ℓ n k (.recr pos s ls l ps ms mins is maj) := by
  intro hls' ⟨_, hl⟩ hps' hms' hmins' his' hmaj _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hls'⟩ := LevelWF.choose hls hls'
  have ⟨_, hps'⟩ := hps'.choose hps hE
  have ⟨_, hms'⟩ := hms'.choose hms hE
  have ⟨_, hmins'⟩ := hmins'.chooseMinors hmins hE
  have ⟨_, his'⟩ := his'.choose his hE
  have ⟨_, hmaj⟩ := hmaj hE
  exact ⟨_, .recr (η := η) (s' := ⟨s, hs⟩) hls hps hms hmins his hη rfl hls' hl hps' hms' hmins'
    his' hmaj⟩

theorem WFSpec.quot {ℓ n k pos eqPos : Nat} {l : FLevel} {α r : FExpr}
    (hfe : F[pos]? = some (.quot eqPos)) :
    LevelWF ℓ l →
    WFSpec L F ℓ n k α →
    WFSpec L F ℓ n k r →
    WFSpec L F ℓ n k (.quot pos l α r) := by
  intro ⟨_, hl⟩ hα hr _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hα⟩ := hα hE
  have ⟨_, hr⟩ := hr hE
  exact ⟨_, .quot (η := η) hη hl hα hr⟩

theorem WFSpec.quotMk {ℓ n k pos eqPos : Nat} {l : FLevel} {α r a : FExpr}
    (hfe : F[pos]? = some (.quot eqPos)) :
    LevelWF ℓ l →
    WFSpec L F ℓ n k α →
    WFSpec L F ℓ n k r →
    WFSpec L F ℓ n k a →
    WFSpec L F ℓ n k (.quotMk pos l α r a) := by
  intro ⟨_, hl⟩ hα hr ha _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hα⟩ := hα hE
  have ⟨_, hr⟩ := hr hE
  have ⟨_, ha⟩ := ha hE
  exact ⟨_, .quotMk (η := η) hη hl hα hr ha⟩

theorem WFSpec.quotLift {ℓ n k pos eqPos : Nat} {l₁ l₂ : FLevel} {α r β f h a : FExpr}
    (hfe : F[pos]? = some (.quot eqPos)) :
    LevelWF ℓ l₁ →
    LevelWF ℓ l₂ →
    WFSpec L F ℓ n k α →
    WFSpec L F ℓ n k r →
    WFSpec L F ℓ n k β →
    WFSpec L F ℓ n k f →
    WFSpec L F ℓ n k h →
    WFSpec L F ℓ n k a →
    WFSpec L F ℓ n k (.quotLift pos l₁ l₂ α r β f h a) := by
  intro ⟨_, hl₁⟩ ⟨_, hl₂⟩ hα hr hβ hf hh ha _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hα⟩ := hα hE
  have ⟨_, hr⟩ := hr hE
  have ⟨_, hβ⟩ := hβ hE
  have ⟨_, hf⟩ := hf hE
  have ⟨_, hh⟩ := hh hE
  have ⟨_, ha⟩ := ha hE
  exact ⟨_, .quotLift (η := η) hη hl₁ hl₂ hα hr hβ hf hh ha⟩

theorem WFSpec.quotInd {ℓ n k pos eqPos : Nat} {l : FLevel} {α r β f a : FExpr}
    (hfe : F[pos]? = some (.quot eqPos)) :
    LevelWF ℓ l →
    WFSpec L F ℓ n k α →
    WFSpec L F ℓ n k r →
    WFSpec L F ℓ n k β →
    WFSpec L F ℓ n k f →
    WFSpec L F ℓ n k a →
    WFSpec L F ℓ n k (.quotInd pos l α r β f a) := by
  intro ⟨_, hl⟩ hα hr hβ hf ha _ hE
  have ⟨η, hη, _⟩ := hE.get hfe
  have ⟨_, hα⟩ := hα hE
  have ⟨_, hr⟩ := hr hE
  have ⟨_, hβ⟩ := hβ hE
  have ⟨_, hf⟩ := hf hE
  have ⟨_, ha⟩ := ha hE
  exact ⟨_, .quotInd (η := η) hη hl hα hr hβ hf ha⟩

theorem WFSpec.proj {ℓ n k pos s idx : Nat} {ι : IndSig} {fI : FInductive} {e : FExpr}
    (hfe : F[pos]? = some (.inductive ι fI)) (hs : s < ι.nsorts)
    (hc : 0 < ι.nctors ⟨s, hs⟩) (hstruct : fI.isStructure s 0 = true)
    (hidx : idx < (ι.ctors ⟨s, hs⟩ ⟨0, hc⟩).nfields) :
    WFSpec L F ℓ n k e →
    WFSpec L F ℓ n k (.proj pos s idx e) := fun he {E} hE => by
  have ⟨η, hη, hentry⟩ := hE.get hfe
  generalize hentryEq : E.2.get η = entry at hentry
  cases hentry with
  | «inductive» hI =>
    have hstruct' : (E.2.get η).block.IsStructure ⟨s, hs⟩ ⟨0, hc⟩ := by
      rw [hentryEq]
      exact hI.isStructure ⟨s, hs⟩ ⟨0, hc⟩ hstruct
    have ⟨_, he⟩ := he hE
    exact ⟨_, .proj (η := η) (s' := ⟨s, hs⟩) (c' := ⟨0, hc⟩) (f' := ⟨idx, hidx⟩)
      (ls' := fun _ => .zero) (ps' := fun _ => .sort ⟦.zero⟧) hstruct' hη rfl rfl he⟩

theorem WFSpec.app {ℓ n k : Nat} {f a : FExpr} :
    WFSpec L F ℓ n k f →
    WFSpec L F ℓ n k a →
    WFSpec L F ℓ n k (.app f a) := by
  intro hf ha _ hE
  have ⟨_, hf⟩ := hf hE
  have ⟨_, ha⟩ := ha hE
  exact ⟨_, .app hf ha⟩

theorem WFSpec.lam {ℓ n k : Nat} {ft b : FExpr} :
    WFSpec L F ℓ n k ft →
    WFSpec L F ℓ (n + 1) (k + 1) b →
    WFSpec L F ℓ n k (.lam ft b) := by
  intro ht hb _ hE
  have ⟨_, ht⟩ := ht hE
  have ⟨_, hb⟩ := hb hE
  exact ⟨_, .lam ht hb⟩

theorem WFSpec.forallE {ℓ n k : Nat} {ft b : FExpr} :
    WFSpec L F ℓ n k ft →
    WFSpec L F ℓ (n + 1) (k + 1) b →
    WFSpec L F ℓ n k (.forallE ft b) := by
  intro ht hb _ hE
  have ⟨_, ht⟩ := ht hE
  have ⟨_, hb⟩ := hb hE
  exact ⟨_, .forallE ht hb⟩

theorem WFSpec.letE {ℓ n k : Nat} {ft v b : FExpr} :
    WFSpec L F ℓ n k ft →
    WFSpec L F ℓ n k v →
    WFSpec L F ℓ (n + 1) (k + 1) b →
    WFSpec L F ℓ n k (.letE ft v b) := by
  intro ht hv hb _ hE
  have ⟨_, ht⟩ := ht hE
  have ⟨_, hv⟩ := hv hE
  have ⟨_, hb⟩ := hb hE
  exact ⟨_, .letE ht hv hb⟩

theorem WFSpec.natLit {ℓ n k num : Nat} {fI : FInductive}
    (hNat : F[L.nat]? = some (.inductive Literals.Nat.sig fI)) :
    WFSpec L F ℓ n k (.natLit num) := by
  intro _ hE
  have ⟨η, hη, _⟩ := hE.get hNat
  exact ⟨_, .natLit (ηNat := η) hη⟩

theorem WFSpec.strLit {ℓ n k : Nat} {str : String} {INat IList IChar : FInductive}
    {tOfNat vOfNat tOfList vOfList : FExpr}
    (hNat : F[L.nat]? = some (.inductive Literals.Nat.sig INat))
    (hList : F[L.list]? = some (.inductive Literals.List.sig IList))
    (hChar : F[L.char]? = some (.inductive Literals.Char.sig IChar))
    (hOfNat : F[L.charOfNat]? = some (.def 0 tOfNat vOfNat))
    (hOfList : F[L.stringOfList]? = some (.def 0 tOfList vOfList)) :
    WFSpec L F ℓ n k (.strLit str) := by
  intro _ hE
  have ⟨ηNat, hηNat, _⟩ := hE.get hNat
  have ⟨ηList, hηList, _⟩ := hE.get hList
  have ⟨ηChar, hηChar, _⟩ := hE.get hChar
  have ⟨ηOfNat, hηOfNat, _⟩ := hE.get hOfNat
  have ⟨ηOfList, hηOfList, _⟩ := hE.get hOfList
  exact ⟨_, .strLit (ηNat := ηNat) (ηList := ηList) (ηChar := ηChar) (ηOfNat := ηOfNat)
    (ηOfList := ηOfList) hηNat hηList hηChar hηOfNat hηOfList⟩

theorem EntryWF.axiom {nlevels : Nat} {ft : FExpr} :
    WFSpec L F nlevels 0 0 ft →
    EntryWF L F (.axiom nlevels ft) := by
  intro ht _ hE
  have ⟨_, ht⟩ := ht hE
  exact ⟨.axiom _, .axiom ht⟩

theorem EntryWF.opaque {nlevels : Nat} {ft : FExpr} :
    WFSpec L F nlevels 0 0 ft →
    EntryWF L F (.opaque nlevels ft) := by
  intro ht _ hE
  have ⟨_, ht⟩ := ht hE
  exact ⟨.opaque _, .opaque ht⟩

theorem EntryWF.def {nlevels : Nat} {ft v : FExpr} :
    WFSpec L F nlevels 0 0 ft →
    WFSpec L F nlevels 0 0 v →
    EntryWF L F (.def nlevels ft v) := by
  intro ht hv _ hE
  have ⟨_, ht⟩ := ht hE
  have ⟨_, hv⟩ := hv hE
  exact ⟨.def _ _, .def ht hv⟩

theorem EntryWF.inductive {ι : IndSig} {fI : FInductive} :
    InductiveWF L F ι fI →
    EntryWF L F (.inductive ι fI) := by
  intro hI _ hE
  have ⟨_, hI⟩ := hI hE
  exact ⟨.inductive _, .inductive hI⟩

theorem WFSpec.wkNOpen {ℓ n : Nat} {ft : FExpr} (k : Nat) :
    WFSpec L F ℓ n 0 ft →
    WFSpec L F ℓ (n + k) k ft := by
  intro h _ hE
  have ⟨_, h⟩ := h hE
  exact ⟨_, h.wkNOpen k⟩

theorem WFSpec.ofClosed {ℓ n k : Nat} {ft : FExpr}
    (hr : ft.fvarRange ≤ n) (hc : ft.data.looseBVarRange.toNat = 0) :
    WFSpec L F ℓ (n + k) k ft →
    WFSpec L F ℓ n 0 ft := by
  intro h _ hE
  have ⟨_, h⟩ := h hE
  exact (h.unbind (by omega) hc).strengthenN hr hc

theorem WFSpec.appList {ℓ n k : Nat} {f : FExpr} :
    (args : List FExpr) →
    WFSpec L F ℓ n k f →
    (∀ a ∈ args, WFSpec L F ℓ n k a) →
    WFSpec L F ℓ n k (f.appList args)
  | [], hf, _ => hf
  | a :: rest, hf, hargs =>
    WFSpec.appList rest (hf.app (hargs a (List.mem_cons_self ..)))
      fun b hb => hargs b (List.mem_cons_of_mem a hb)

variable (L F)

abbrev WFCache (ℓ : Nat) :=
  Std.HashMap (Nat × Nat × FExpr)
    ((key : Nat × Nat × FExpr) × PLift (WFSpec L F ℓ key.1 key.2.1 key.2.2))

abbrev WFM (ℓ : Nat) := StateT (WFCache L F ℓ) (Except Failure)

mutual

partial def FExpr.wfM (ℓ n k : Nat) (fe : FExpr) : WFM L F ℓ (PLift (WFSpec L F ℓ n k fe)) := do
  if fe matches .bvar _ | .fvar _ | .sort _ | .const .. | .natLit _ | .strLit _ then
    return ← FExpr.wfCore ℓ n k fe
  match (← get).get? (n, k, fe) with
  | some ⟨key, h⟩ =>
    if hk : key = (n, k, fe) then return by subst hk; exact h
  | none => pure ()
  let h ← FExpr.wfCore ℓ n k fe
  modify (·.insert (n, k, fe) ⟨(n, k, fe), h⟩)
  pure h

partial def FExpr.wfArrM (ℓ n k : Nat) (es : FCtx) : WFM L F ℓ (PLift (ArrWF L F ℓ n k es)) :=
  Array.forallM es (fun i h => WFSpec L F ℓ n k es[i]) fun i _ => FExpr.wfM ℓ n k es[i]

partial def FExpr.wfCore (ℓ n k : Nat) : (fe : FExpr) → WFM L F ℓ (PLift (WFSpec L F ℓ n k fe))
  | .bvar j => do
    let ⟨hj⟩ ← guardProofOr (j < k) (.reject .unboundVariable)
    let ⟨hn⟩ ← guardProofOr (j < n) (.reject .unboundVariable)
    pure ⟨WFSpec.bvar hj hn⟩
  | .fvar i => do
    let ⟨hi⟩ ← guardProofOr (i + k < n) (.reject .unboundVariable)
    pure ⟨WFSpec.fvar hi⟩
  | .sort l => do
    let ⟨_, hl⟩ ← checkLevel ℓ l
    pure ⟨WFSpec.sort ⟨_, hl⟩⟩
  | .const pos ls =>
    match hfe : F[pos]? with
    | some (.axiom nlevels _) | some (.opaque nlevels _) | some (.def nlevels _ _) => do
      let ⟨hls⟩ ← guardProofOr (ls.size = nlevels) (.reject .arity)
      let ⟨hls'⟩ ← checkLevels ℓ ls
      pure ⟨WFSpec.const hfe rfl hls hls'⟩
    | _ => throw .internal
  | .ind pos s ls ps is =>
    match hfe : F[pos]? with
    | some (.inductive ι _) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .arity)
      let ⟨hls⟩ ← guardProofOr (ls.size = ι.nlevels) (.reject .arity)
      let ⟨hps⟩ ← guardProofOr (ps.size = ι.nparams) (.reject .arity)
      let ⟨his⟩ ← guardProofOr (is.size = ι.nindices ⟨s, hs⟩) (.reject .arity)
      let ⟨hls'⟩ ← checkLevels ℓ ls
      let ⟨hps'⟩ ← wfArrM ℓ n k ps
      let ⟨his'⟩ ← wfArrM ℓ n k is
      pure ⟨WFSpec.ind hfe hs hls hps his hls' hps' his'⟩
    | _ => throw .internal
  | .ctor pos s c ls ps fds recFds =>
    match hfe : F[pos]? with
    | some (.inductive ι _) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .arity)
      let ⟨hc⟩ ← guardProofOr (c < ι.nctors ⟨s, hs⟩) (.reject .arity)
      let ⟨hls⟩ ← guardProofOr (ls.size = ι.nlevels) (.reject .arity)
      let ⟨hps⟩ ← guardProofOr (ps.size = ι.nparams) (.reject .arity)
      let ⟨hfds⟩ ← guardProofOr (fds.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields) (.reject .arity)
      let ⟨hrecFds⟩ ← guardProofOr (recFds.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields)
        (.reject .arity)
      let ⟨hls'⟩ ← checkLevels ℓ ls
      let ⟨hps'⟩ ← wfArrM ℓ n k ps
      let ⟨hfds'⟩ ← wfArrM ℓ n k fds
      let ⟨hrecFds'⟩ ← wfArrM ℓ n k recFds
      pure ⟨WFSpec.ctor hfe hs hc hls hps hfds hrecFds hls' hps' hfds' hrecFds'⟩
    | _ => throw .internal
  | .recr pos s ls l ps ms mins is maj =>
    match hfe : F[pos]? with
    | some (.inductive ι _) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .arity)
      let ⟨hls⟩ ← guardProofOr (ls.size = ι.nlevels) (.reject .arity)
      let ⟨hps⟩ ← guardProofOr (ps.size = ι.nparams) (.reject .arity)
      let ⟨hms⟩ ← guardProofOr (ms.size = ι.nsorts) (.reject .arity)
      let ⟨hmins⟩ ← guardProofOr (mins.size = Fin.sum ι.nctors) (.reject .arity)
      let ⟨his⟩ ← guardProofOr (is.size = ι.nindices ⟨s, hs⟩) (.reject .arity)
      let ⟨hls'⟩ ← checkLevels ℓ ls
      let ⟨_, hl⟩ ← checkLevel ℓ l
      let ⟨hps'⟩ ← wfArrM ℓ n k ps
      let ⟨hms'⟩ ← wfArrM ℓ n k ms
      let ⟨hmins'⟩ ← wfArrM ℓ n k mins
      let ⟨his'⟩ ← wfArrM ℓ n k is
      let ⟨hmaj⟩ ← wfM ℓ n k maj
      pure ⟨WFSpec.recr hfe hs hls hps hms hmins his hls' ⟨_, hl⟩ hps' hms' hmins' his' hmaj⟩
    | _ => throw .internal
  | .quot pos l α r =>
    match hfe : F[pos]? with
    | some (.quot _) => do
      let ⟨_, hl⟩ ← checkLevel ℓ l
      let ⟨hα⟩ ← wfM ℓ n k α
      let ⟨hr⟩ ← wfM ℓ n k r
      pure ⟨WFSpec.quot hfe ⟨_, hl⟩ hα hr⟩
    | _ => throw .internal
  | .quotMk pos l α r a =>
    match hfe : F[pos]? with
    | some (.quot _) => do
      let ⟨_, hl⟩ ← checkLevel ℓ l
      let ⟨hα⟩ ← wfM ℓ n k α
      let ⟨hr⟩ ← wfM ℓ n k r
      let ⟨ha⟩ ← wfM ℓ n k a
      pure ⟨WFSpec.quotMk hfe ⟨_, hl⟩ hα hr ha⟩
    | _ => throw .internal
  | .quotLift pos l₁ l₂ α r β f h a =>
    match hfe : F[pos]? with
    | some (.quot _) => do
      let ⟨_, hl₁⟩ ← checkLevel ℓ l₁
      let ⟨_, hl₂⟩ ← checkLevel ℓ l₂
      let ⟨hα⟩ ← wfM ℓ n k α
      let ⟨hr⟩ ← wfM ℓ n k r
      let ⟨hβ⟩ ← wfM ℓ n k β
      let ⟨hf⟩ ← wfM ℓ n k f
      let ⟨hh⟩ ← wfM ℓ n k h
      let ⟨ha⟩ ← wfM ℓ n k a
      pure ⟨WFSpec.quotLift hfe ⟨_, hl₁⟩ ⟨_, hl₂⟩ hα hr hβ hf hh ha⟩
    | _ => throw .internal
  | .quotInd pos l α r β f a =>
    match hfe : F[pos]? with
    | some (.quot _) => do
      let ⟨_, hl⟩ ← checkLevel ℓ l
      let ⟨hα⟩ ← wfM ℓ n k α
      let ⟨hr⟩ ← wfM ℓ n k r
      let ⟨hβ⟩ ← wfM ℓ n k β
      let ⟨hf⟩ ← wfM ℓ n k f
      let ⟨ha⟩ ← wfM ℓ n k a
      pure ⟨WFSpec.quotInd hfe ⟨_, hl⟩ hα hr hβ hf ha⟩
    | _ => throw .internal
  | .proj pos s idx e =>
    match hfe : F[pos]? with
    | some (.inductive ι fI) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .arity)
      let ⟨hc⟩ ← guardProofOr (0 < ι.nctors ⟨s, hs⟩) (.reject .shape)
      let ⟨hstruct⟩ ← guardProofOr (fI.isStructure s 0 = true) (.reject .shape)
      let ⟨hidx⟩ ← guardProofOr (idx < (ι.ctors ⟨s, hs⟩ ⟨0, hc⟩).nfields) (.reject .arity)
      let ⟨he⟩ ← wfM ℓ n k e
      pure ⟨WFSpec.proj hfe hs hc hstruct hidx he⟩
    | _ => throw .internal
  | .app f a => do
    let ⟨hf⟩ ← wfM ℓ n k f
    let ⟨ha⟩ ← wfM ℓ n k a
    pure ⟨WFSpec.app hf ha⟩
  | .lam ft b => do
    let ⟨ht⟩ ← wfM ℓ n k ft
    let ⟨hb⟩ ← wfM ℓ (n + 1) (k + 1) b
    pure ⟨WFSpec.lam ht hb⟩
  | .forallE ft b => do
    let ⟨ht⟩ ← wfM ℓ n k ft
    let ⟨hb⟩ ← wfM ℓ (n + 1) (k + 1) b
    pure ⟨WFSpec.forallE ht hb⟩
  | .letE ft v b => do
    let ⟨ht⟩ ← wfM ℓ n k ft
    let ⟨hv⟩ ← wfM ℓ n k v
    let ⟨hb⟩ ← wfM ℓ (n + 1) (k + 1) b
    pure ⟨WFSpec.letE ht hv hb⟩
  | .natLit _ =>
    match hNat : F[L.nat]? with
    | some (.inductive ι _) => do
      let ⟨rfl⟩ ← guardProofOr (ι = Literals.Nat.sig) (.decline .literal)
      pure ⟨WFSpec.natLit hNat⟩
    | _ => throw (.decline .literal)
  | .strLit _ =>
    match hNat : F[L.nat]?, hList : F[L.list]?, hChar : F[L.char]?,
        hOfNat : F[L.charOfNat]?, hOfList : F[L.stringOfList]? with
    | some (.inductive ιNat _), some (.inductive ιList _), some (.inductive ιChar _),
        some (.def 0 _ _), some (.def 0 _ _) => do
      let ⟨rfl⟩ ← guardProofOr (ιNat = Literals.Nat.sig) (.decline .literal)
      let ⟨rfl⟩ ← guardProofOr (ιList = Literals.List.sig) (.decline .literal)
      let ⟨rfl⟩ ← guardProofOr (ιChar = Literals.Char.sig) (.decline .literal)
      pure ⟨WFSpec.strLit hNat hList hChar hOfNat hOfList⟩
    | _, _, _, _, _ => throw (.decline .literal)

end

def FExpr.wf (ℓ n k : Nat) (fe : FExpr) : Except Failure (PLift (WFSpec L F ℓ n k fe)) :=
  (FExpr.wfM L F ℓ n k fe).run' ∅

def FExpr.wfArr (ℓ n k : Nat) (es : FCtx) : Except Failure (PLift (ArrWF L F ℓ n k es)) :=
  (FExpr.wfArrM L F ℓ n k es).run' ∅

def FExpr.wfTele (ℓ a : Nat) (ts : FCtx) : Except Failure (PLift (TeleWF L F ℓ a ts)) := do
  let ⟨h⟩ ← Array.forallM ts (fun j h => WFSpec L F ℓ (a + j) 0 (ts[j]'h)) fun j _ =>
    FExpr.wf L F ℓ (a + j) 0 ts[j]
  pure ⟨TeleWF.of h⟩

def FField.wf (ι : IndSig) (nfields : Nat) (ffd : FField) :
    Except Failure (PLift (FieldWF L F ι nfields ffd)) := do
  let ⟨ht⟩ ← FExpr.wf L F ι.nlevels (ι.nparams + nfields) 0 ffd.type
  let ⟨_, hl⟩ ← checkLevel ι.nlevels ffd.level
  pure ⟨FieldWF.of ht ⟨_, hl⟩⟩

def FRecField.wf (ι : IndSig) (nfields arity : Nat) (target : Fin ι.nsorts) (ffd : FRecField) :
    Except Failure (PLift (RecFieldWF L F ι nfields arity target ffd)) := do
  let ⟨harity⟩ ← guardProofOr (ffd.tele.size = arity) (.reject .arity)
  let ⟨htele⟩ ← FExpr.wfTele L F ι.nlevels (ι.nparams + nfields) ffd.tele
  let ⟨hsize⟩ ← guardProofOr (ffd.indices.size = ι.nindices target) (.reject .arity)
  let ⟨hindices⟩ ← FExpr.wfArr L F ι.nlevels (ι.nparams + nfields + arity) 0 ffd.indices
  pure ⟨RecFieldWF.of harity hsize htele hindices⟩

def FCtor.wf (ι : IndSig) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (fctor : FCtor) :
    Except Failure (PLift (CtorWF L F ι s c fctor)) := do
  let ⟨hord⟩ ← guardProofOr (fctor.ordinary.size = (ι.ctors s c).nfields) (.reject .arity)
  let ⟨hord'⟩ ← Array.forallM fctor.ordinary (fun f h => FieldWF L F ι f (fctor.ordinary[f]'h))
    fun f _ => FField.wf L F ι f fctor.ordinary[f]
  let ⟨hrec⟩ ← guardProofOr (fctor.recursive.size = (ι.ctors s c).nrecFields) (.reject .arity)
  let ⟨hrec'⟩ ← Array.forallM fctor.recursive
    (fun r hr => RecFieldWF L F ι (ι.ctors s c).nfields
      ((ι.ctors s c).recursiveArity ⟨r, hrec ▸ hr⟩) ((ι.ctors s c).recursiveTarget ⟨r, hrec ▸ hr⟩)
      (fctor.recursive[r]'hr))
    fun r hr => FRecField.wf L F ι (ι.ctors s c).nfields
      ((ι.ctors s c).recursiveArity ⟨r, hrec ▸ hr⟩) ((ι.ctors s c).recursiveTarget ⟨r, hrec ▸ hr⟩)
      fctor.recursive[r]
  let ⟨htarget⟩ ← guardProofOr (fctor.targetIndices.size = ι.nindices s) (.reject .arity)
  let ⟨htarget'⟩ ← FExpr.wfArr L F ι.nlevels (ι.nparams + (ι.ctors s c).nfields) 0
    fctor.targetIndices
  pure ⟨CtorWF.of hord hrec htarget hord' hrec' htarget'⟩

def FInductive.wf (ι : IndSig) (fI : FInductive) : Except Failure (PLift (InductiveWF L F ι fI)) := do
  let ⟨hparams⟩ ← guardProofOr (fI.params.size = ι.nparams) (Failure.reject .arity)
  let ⟨hparams'⟩ ← FExpr.wfTele L F ι.nlevels 0 fI.params
  let ⟨hindices⟩ ← guardProofOr (fI.indices.size = ι.nsorts) (Failure.reject .arity)
  let hrows ← Array.forallM fI.indices
    (fun s hs => fI.indices[s].size = ι.nindices ⟨s, hindices ▸ hs⟩)
    fun s hs => guardProofOr (fI.indices[s].size = ι.nindices ⟨s, hindices ▸ hs⟩) (Failure.reject .arity)
  let hindices' ← Array.forallM fI.indices (fun s _ => TeleWF L F ι.nlevels ι.nparams fI.indices[s])
    fun s _ => FExpr.wfTele L F ι.nlevels ι.nparams fI.indices[s]
  let ⟨_, hlevel⟩ ← checkLevel ι.nlevels fI.level
  let ⟨hctors⟩ ← guardProofOr (fI.ctors.size = ι.nsorts) (Failure.reject .arity)
  let hctorRows ← Array.forallM fI.ctors (fun s hs => fI.ctors[s].size = ι.nctors ⟨s, hctors ▸ hs⟩)
    fun s hs => guardProofOr (fI.ctors[s].size = ι.nctors ⟨s, hctors ▸ hs⟩) (Failure.reject .arity)
  let hctors' ← Array.forallM fI.ctors
    (fun s hs => ∀ c (hc : c < fI.ctors[s].size),
      CtorWF L F ι ⟨s, hctors ▸ hs⟩ ⟨c, hctorRows.down s hs ▸ hc⟩ fI.ctors[s][c])
    fun s hs => Array.forallM fI.ctors[s]
      (fun c hc => CtorWF L F ι ⟨s, hctors ▸ hs⟩ ⟨c, hctorRows.down s hs ▸ hc⟩ fI.ctors[s][c])
      fun c hc => FCtor.wf L F ι ⟨s, hctors ▸ hs⟩ ⟨c, hctorRows.down s hs ▸ hc⟩ fI.ctors[s][c]
  pure ⟨InductiveWF.of hparams hindices hrows.down hctors hctorRows.down hparams'
    hindices'.down ⟨_, hlevel⟩ hctors'.down⟩

end Metalean.FastChecker
