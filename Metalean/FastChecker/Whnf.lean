/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Inductive
public import Metalean.Control
public import Metalean.Syntax.Reduction
import Metalean.Meta.IfRfl
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.FastChecker

open Relation

variable (L : Literals) (F : FEnv) (n : Nat)

inductive FFrame where
  | app (a : FExpr)
  | recr (pos s : Nat) (ls : Array FLevel) (l : FLevel) (ps ms mins is : Array FExpr)
  | quotLift (pos : Nat) (l₁ l₂ : FLevel) (α r β f h : FExpr)
  | quotInd (pos : Nat) (l : FLevel) (α r β f : FExpr)
  | proj (pos s idx : Nat)

def FFrame.plug (e : FExpr) : FFrame → FExpr
  | .app a => .app e a
  | .recr pos s ls l ps ms mins is => .recr pos s ls l ps ms mins is e
  | .quotLift pos l₁ l₂ α r β f h => .quotLift pos l₁ l₂ α r β f h e
  | .quotInd pos l α r β f => .quotInd pos l α r β f e
  | .proj pos s idx => .proj pos s idx e

judgement FWHRed : FExpr → FExpr → Prop where

  FWHRed e₁ e₂
  ──────────────────── frame {e₁ e₂ : FExpr} (K : FFrame)
  FWHRed (K.plug e₁) (K.plug e₂)

  ──────────────────── beta (t b a : FExpr)
  FWHRed (.app (.lam t b) a) (FExpr.instAt a 0 b)

  ──────────────────── zeta (t v b : FExpr)
  FWHRed (.letE t v b) (FExpr.instAt v 0 b)

  F[pos]? = some (.def nlevels t v)
  ls.size = nlevels
  ──────────────────── delta {pos nlevels : Nat} {t v : FExpr} {ls : Array FLevel}
  FWHRed (.const pos ls) (v.instL ls)

  pos₂ = pos₁
  ──────────────────── quotIota {pos₁ pos₂ : Nat} {l₁ l₂ l₃ : FLevel} {α₁ r₁ β f h α₂ r₂ a : FExpr}
  FWHRed (.quotLift pos₁ l₁ l₂ α₁ r₁ β f h (.quotMk pos₂ l₃ α₂ r₂ a)) (.app f a)

  pos₂ = pos₁
  ──────────────────── quotIndIota {pos₁ pos₂ : Nat} {l₁ l₂ : FLevel} {α₁ r₁ β f α₂ r₂ a : FExpr}
  FWHRed (.quotInd pos₁ l₁ α₁ r₁ β f (.quotMk pos₂ l₂ α₂ r₂ a)) (.app f a)

  F[pos]? = some (.inductive ι I)
  I.ctors[s]?.bind (·[c]?) = some ctor
  pos₂ = pos
  s₂ = s
  ──────────────────── iota {pos pos₂ s s₂ c : Nat} {ι : IndSig} {I : FInductive} {ctor : FCtor}
    {ls ls₂ : Array FLevel} {l : FLevel} {ps ms mins is ps₂ fds recFds : Array FExpr}
    (hs : s < ι.nsorts) (hc : c < ι.nctors ⟨s, hs⟩)
    (hrec : ctor.recursive.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields)
    (hrecFds : recFds.size = ctor.recursive.size) (hmins : mins.size = Fin.sum ι.nctors)
  FWHRed (.recr pos s ls l ps ms mins is (.ctor pos₂ s₂ c ls₂ ps₂ fds recFds))
    (ctor.iotaRhs pos ls ps fds n
      (fun r => ((ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).recursiveTarget (r.cast hrec)).val) l ms mins
      (mins[(minorIndex ι ⟨s, hs⟩ ⟨c, hc⟩).val]'(hmins.symm ▸ (minorIndex ι ⟨s, hs⟩ ⟨c, hc⟩).isLt))
      recFds hrecFds)

  F[L.nat]? = some (.inductive Literals.Nat.sig I)
  ──────── natLitZero {I : FInductive}
  FWHRed (.natLit 0) (.ctor L.nat 0 0 #[] #[] #[] #[])

  F[L.nat]? = some (.inductive Literals.Nat.sig I)
  ──────── natLitSucc {I : FInductive} {num : Nat}
  FWHRed (.natLit (num + 1)) (.ctor L.nat 0 1 #[] #[] #[] #[.natLit num])

abbrev FWHRedS : FExpr → FExpr → Prop := ReflTransGen (FWHRed L F n)

variable {L F n} {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

theorem FFrame.denotes {K : FFrame} {e₁ e₂ : FExpr} {e₁' : Expr ζ ℓ n} :
    FExpr.Denotes L ⟨ζ, E⟩ 0 (K.plug e₁) e₁' →
    ∃ (K' : Frame ζ ℓ n) (e₁'' : Expr ζ ℓ n), e₁' = K'.plug e₁'' ∧ FExpr.Denotes L ⟨ζ, E⟩ 0 e₁ e₁'' ∧
      ∀ {e₂' : Expr ζ ℓ n},
      FExpr.Denotes L ⟨ζ, E⟩ 0 e₂ e₂' → FExpr.Denotes L ⟨ζ, E⟩ 0 (K.plug e₂) (K'.plug e₂') := by
  intro h
  cases K with
  | app a =>
    have .app hf ha := h
    exact ⟨.app _, _, by rfl, hf, fun h₂ => .app h₂ ha⟩
  | recr pos s ls l ps ms mins is =>
    have .recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' hmaj := h
    exact ⟨.recr _ _ _ _ _ _ _ _, _, by rfl, hmaj,
      fun h₂ => .recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' h₂⟩
  | quotLift pos l₁ l₂ α r β f g =>
    have .quotLift hη hl₁ hl₂ hα hr hβ hf hg ha := h
    exact ⟨.quotLift _ _ _ _ _ _ _ _, _, by rfl, ha,
      fun h₂ => .quotLift hη hl₁ hl₂ hα hr hβ hf hg h₂⟩
  | quotInd pos l α r β f =>
    have .quotInd hη hl hα hr hβ hf ha := h
    exact ⟨.quotInd _ _ _ _ _ _, _, by rfl, ha, fun h₂ => .quotInd hη hl hα hr hβ hf h₂⟩
  | proj pos s idx =>
    have .proj hstruct hη hs hidx he := h
    rw [Inductive.IsStructure.projTerm_eq_recr]
    exact ⟨.recr _ _ _ _ _ _ _ _, _, rfl, he, fun h₂ => by
      change FExpr.Denotes L ⟨ζ, E⟩ 0 _ (Expr.recr _ _ _ _ _ _ _ _ _)
      rw [← Inductive.IsStructure.projTerm_eq_recr]
      exact .proj hstruct hη hs hidx h₂⟩

theorem FWHRed.denotes {e₁ e₂ : FExpr} {e₁' : Expr ζ ℓ n} :
    FEnv.Denotes L F E →
    FWHRed L F n e₁ e₂ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 e₁ e₁' →
    ∃ e₂', FExpr.Denotes L ⟨ζ, E⟩ 0 e₂ e₂' ∧ E ⊢ e₁' ⤳* e₂' := by
  intro hE hred he
  induction hred generalizing e₁' with
  | frame K _ ih =>
    obtain ⟨K', e₁'', rfl, he₁, hK⟩ := FFrame.denotes he
    have ⟨e₂', he₂, hr⟩ := ih he₁
    exact ⟨_, hK he₂, hr.lift K'.plug fun _ _ => .frame⟩
  | beta =>
    have .app hf ha := he
    have .lam _ hb := hf
    exact ⟨_, hb.inst ha, .single .beta⟩
  | zeta =>
    have .letE _ hv hb := he
    exact ⟨_, hb.inst hv, .single .zeta⟩
  | @delta pos nlevels t v ls hfe hsize =>
    have .const hls hη hls' := he
    have ⟨η₀, hη₀, hden⟩ := hE.get hfe
    cases hη.symm.trans hη₀
    generalize hentry : E.get η₀ = entry at hden
    have .«def» _ hv := hden
    have hentry' : E.get (sig := .const .def nlevels) η₀ = .def _ _ := hentry
    refine ⟨_, ?_, .single .delta⟩
    rw [hentry']
    exact (hv.instL hls hls').wkClosed _
  | quotIota hpos =>
    subst hpos
    have .quotLift hη _ _ _ _ _ hf _ ha := he
    have .quotMk hη₂ _ _ _ ha := ha
    cases hη.symm.trans hη₂
    exact ⟨_, .app hf ha, .single .quotIota⟩
  | quotIndIota hpos =>
    subst hpos
    have .quotInd hη _ _ _ _ hf ha := he
    have .quotMk hη₂ _ _ _ ha := ha
    cases hη.symm.trans hη₂
    exact ⟨_, .app hf ha, .single .quotIndIota⟩
  | @iota pos pos₂ s s₂ c ι I ctor ls ls₂ l ps ms mins is ps₂ fds recFds hs hc hrec hrecFds hmins
      hfe hctor hpos hs₂ =>
    subst pos₂ s₂
    have .recr hls hps hms hmins' his hη hs' hls' hl hps' hms' hmins'' his' hmaj := he
    have .ctor hls₂ hps₂ hfds hrecFds' hη₂ hs₂' hc' hls₂' hps₂' hfds' hrecFds'' := hmaj
    cases hη.symm.trans hη₂
    have ⟨η₀, hη₀, hI⟩ := hE.inductive hfe
    cases hη.symm.trans hη₀
    obtain rfl : _ = (⟨s, hs⟩ : Fin ι.nsorts) := Fin.ext hs'
    obtain rfl : _ = (⟨s, hs⟩ : Fin ι.nsorts) := Fin.ext hs₂'
    obtain rfl : _ = (⟨c, hc⟩ : Fin (ι.nctors ⟨s, hs⟩)) := Fin.ext hc'
    have hctor' : ctor = (I.ctors[s]'(hI.ctorsLt ⟨s, hs⟩))[c]'(hI.ctorLt ⟨s, hs⟩ ⟨c, hc⟩) := by
      rw [Array.getElem?_eq_getElem (hI.ctorsLt ⟨s, hs⟩), Option.bind_some,
        Array.getElem?_eq_getElem (hI.ctorLt ⟨s, hs⟩ ⟨c, hc⟩), Option.some.injEq] at hctor
      exact hctor.symm
    subst hctor'
    refine ⟨_, ?_, .single .iota⟩
    exact (hI.ctors ⟨s, hs⟩ ⟨c, hc⟩).iotaRhs hls hls'
      ⟨hps, hps'⟩
      hη
      (fun r => rfl)
      ⟨hms, hms'⟩
      hl hmins' hmins''
      (hmins'' _ _)
      ⟨hfds, hfds'⟩
      ⟨hrecFds', hrecFds''⟩
  | natLitZero _ =>
    have .natLit hη := he
    exact ⟨_, FExpr.Denotes.zero hη, .refl⟩
  | natLitSucc _ =>
    have .natLit hη := he
    exact ⟨_, FExpr.Denotes.succLit hη, .refl⟩

theorem FWHRedS.denotes {e₁ e₂ : FExpr} {e₁' : Expr ζ ℓ n} :
    FEnv.Denotes L F E →
    FWHRedS L F n e₁ e₂ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 e₁ e₁' →
    ∃ e₂', FExpr.Denotes L ⟨ζ, E⟩ 0 e₂ e₂' ∧ E ⊢ e₁' ⤳* e₂' := by
  intro hE hred he
  induction hred with
  | refl => exact ⟨_, he, .refl⟩
  | tail _ hstep ih =>
    have ⟨_, he₂, hr₁⟩ := ih
    have ⟨_, he₃, hr₂⟩ := hstep.denotes hE he₂
    exact ⟨_, he₃, hr₁.trans hr₂⟩

theorem FWHRedS.frame {e₁ e₂ : FExpr} (K : FFrame) :
    FWHRedS L F n e₁ e₂ →
    FWHRedS L F n (K.plug e₁) (K.plug e₂) :=
  fun h => h.lift K.plug fun _ _ => .frame K

theorem FWHRedS.appList {e₁ e₂ : FExpr} (as : List FExpr) :
    FWHRedS L F n e₁ e₂ →
    FWHRedS L F n (FExpr.appList e₁ as) (FExpr.appList e₂ as) := by
  intro h
  induction as generalizing e₁ e₂ with
  | nil => exact h
  | cons a as ih => exact ih (h.frame (.app a))

theorem FWHRedS.betaMany {as : List FExpr} {f b : FExpr} :
    FExpr.LamBody as.length f b →
    FWHRedS L F n (FExpr.appList f as) (FExpr.instMany as b) := by
  intro h
  induction as generalizing f b with
  | nil =>
    cases h
    exact .refl
  | cons a as ih =>
    cases h with
    | @succ _ t f' _ h' =>
      have hstep : FWHRedS L F n (FExpr.appList (.app (.lam t f') a) as)
          (FExpr.appList (FExpr.instAt a 0 f') as) :=
        FWHRedS.appList as (.single (.beta t f' a))
      have hrest := ih (h'.instAt a 0)
      rw [Nat.zero_add] at hrest
      exact hstep.trans hrest

instance {e₁ : FExpr} : Nonempty {e₂ : FExpr // FWHRedS L F n e₁ e₂} :=
  ⟨e₁, .refl⟩

variable (L F n)

def litToCtor : (maj : FExpr) → {maj₂ : FExpr // FWHRedS L F n maj maj₂}
  | .natLit num =>
    match hfe : F[L.nat]? with
    | some (.inductive ι I) =>
      if hι : ι = Literals.Nat.sig then
        match num with
        | 0 => ⟨_, .single (.natLitZero (I := I) (by rw [hfe, hι]))⟩
        | num + 1 => ⟨_, .single (.natLitSucc (I := I) (by rw [hfe, hι]))⟩
      else ⟨.natLit num, .refl⟩
    | _ => ⟨.natLit num, .refl⟩
  | maj => ⟨maj, .refl⟩

def iotaStep (pos s : Nat) (ls : Array FLevel) (l : FLevel) (ps ms mins is : Array FExpr) :
    (maj : FExpr) → Option {e : FExpr // FWHRed L F n (.recr pos s ls l ps ms mins is maj) e}
  | .ctor pos₂ s₂ c _ _ _ recFds =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨rfl⟩ ← guardProof (pos = pos₂)
      let ⟨rfl⟩ ← guardProof (s = s₂)
      let ⟨hs⟩ ← guardProof (s < ι.nsorts)
      let ⟨hc⟩ ← guardProof (c < ι.nctors ⟨s, hs⟩)
      match hctor : I.ctors[s]?.bind (·[c]?) with
      | some ctor => do
        let ⟨hrec⟩ ← guardProof (ctor.recursive.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields)
        let ⟨hrecFds⟩ ← guardProof (recFds.size = ctor.recursive.size)
        let ⟨hmins⟩ ← guardProof (mins.size = Fin.sum ι.nctors)
        pure ⟨_, .iota hs hc hrec hrecFds hmins hfe hctor rfl rfl⟩
      | none => none
    | _ => none
  | _ => none

end Metalean.FastChecker
