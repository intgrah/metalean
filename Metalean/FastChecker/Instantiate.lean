/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Operations
public import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean.FastChecker

variable {ℓ ℓ' : Nat}

structure Ren.Shifts {m n : Nat} (k : Nat) (ρ : Ren m n) : Prop where
  free : ∀ v : Var m, v.val + k < m → (ρ v).val = v.val
  bound : ∀ v : Var m, m ≤ v.val + k → (ρ v).val + m = v.val + n

theorem Ren.Shifts.lift {m n k : Nat} {ρ : Ren m n} (h : Ren.Shifts k ρ) :
    Ren.Shifts (k + 1) ρ.lift where
  free v hv := by
    simpa [Ren.lift, show v.val < m by omega] using h.free _ (by simp; omega)
  bound v hv := by
    by_cases hvm : v.val < m
    · have := h.bound ⟨v.val, hvm⟩ (by simp; omega)
      simp at this
      simp [Ren.lift, hvm]
      omega
    · simp [Ren.lift, hvm]
      omega

variable {E : Σ ζ, Env ζ} {L : Literals}

theorem FExpr.Denotes.rename {m k : Nat} {fe : FExpr} {e : Expr E.1 ℓ m} {n k' : Nat}
    (ρ : Ren m n) (hk : k ≤ k') (hmn : m + k' ≤ n + k) (hρ : Ren.Shifts k ρ) :
    FExpr.Denotes L E k fe e →
    FExpr.Denotes L E k' fe (e.rename ρ) := by
  intro h
  induction h generalizing n k' with
  | @bvar m k i j hi hj =>
    have hv := hρ.bound ⟨i, by omega⟩ (by simp; omega)
    have : ρ ⟨i, by omega⟩ = ⟨n - 1 - j, by omega⟩ := Fin.ext (by simp at hv ⊢; omega)
    simpa [Expr.rename, this] using .bvar (by omega) (by omega)
  | @fvar m k i hi =>
    have hv := hρ.free ⟨i, by omega⟩ (by simp; omega)
    have : ρ ⟨i, by omega⟩ = ⟨i, by omega⟩ := Fin.ext hv
    simpa [Expr.rename, this] using .fvar (by omega)
  | sort hl => exact .sort hl
  | const hls hη hls' => exact .const hls hη hls'
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    exact .ind hls hps his hη hs hls'
      (fun p => ihps p ρ hk hmn hρ)
      (fun i => ihis i ρ hk hmn hρ)
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    exact .ctor hls hps hfds hrecFds hη hs hc hls'
      (fun p => ihps p ρ hk hmn hρ)
      (fun f => ihfds f ρ hk hmn hρ)
      (fun f => ihrecFds f ρ hk hmn hρ)
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    exact .recr hls hps hms hmins his hη hs hls' hl
      (fun p => ihps p ρ hk hmn hρ)
      (fun fe => ihms fe ρ hk hmn hρ)
      (fun fe c => ihmins fe c ρ hk hmn hρ)
      (fun i => ihis i ρ hk hmn hρ)
      (ihmaj ρ hk hmn hρ)
  | quot hη hl _ _ ihα ihr => exact .quot hη hl (ihα ρ hk hmn hρ) (ihr ρ hk hmn hρ)
  | quotMk hη hl _ _ _ ihα ihr iha =>
    exact .quotMk hη hl (ihα ρ hk hmn hρ) (ihr ρ hk hmn hρ) (iha ρ hk hmn hρ)
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact .quotLift hη hl₁ hl₂
      (ihα ρ hk hmn hρ)
      (ihr ρ hk hmn hρ)
      (ihβ ρ hk hmn hρ)
      (ihf ρ hk hmn hρ)
      (ihh ρ hk hmn hρ)
      (iha ρ hk hmn hρ)
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    exact .quotInd hη hl
      (ihα ρ hk hmn hρ)
      (ihr ρ hk hmn hρ)
      (ihβ ρ hk hmn hρ)
      (ihf ρ hk hmn hρ)
      (iha ρ hk hmn hρ)
  | proj hstruct hη hs hidx _ ihe =>
    rw [← Expr.subst_vars, Inductive.IsStructure.projTerm_subst]
    simpa using .proj hstruct hη hs hidx (ihe ρ hk hmn hρ)
  | app _ _ ihf iha => exact .app (ihf ρ hk hmn hρ) (iha ρ hk hmn hρ)
  | lam _ _ iht ihb => exact .lam (iht ρ hk hmn hρ) (ihb ρ.lift (by omega) (by omega) hρ.lift)
  | forallE _ _ iht ihb =>
    exact .forallE (iht ρ hk hmn hρ) (ihb ρ.lift (by omega) (by omega) hρ.lift)
  | letE _ _ _ iht ihv ihb =>
    exact .letE (iht ρ hk hmn hρ) (ihv ρ hk hmn hρ) (ihb ρ.lift (by omega) (by omega) hρ.lift)
  | natLit hNat =>
    rw [← Expr.subst_vars, Literals.subst_natLit]
    exact .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    rw [← Expr.subst_vars, Literals.subst_strLit]
    exact .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.wkOpen {n : Nat} {fe : FExpr} {e : Expr E.1 ℓ n} :
    FExpr.Denotes L E 0 fe e →
    FExpr.Denotes L E 1 fe e.wk := fun h =>
  h.rename _ (Nat.zero_le 1) (by omega) ⟨fun v _ => by simp, fun v hv => by omega⟩

theorem FExpr.Denotes.wk {n : Nat} {fe : FExpr} {e : Expr E.1 ℓ n} :
    FExpr.Denotes L E 0 fe e →
    FExpr.Denotes L E 0 fe e.wk := fun h =>
  h.rename _ le_rfl (by omega) ⟨fun v hv => by simp, fun v hv => by omega⟩

theorem FExpr.Denotes.wkClosed {fe : FExpr} {e : Expr E.1 ℓ 0} :
    FExpr.Denotes L E 0 fe e →
    (n : Nat) →
    FExpr.Denotes L E 0 fe (e.wkClosed (n := n))
  | h, 0 => h
  | h, n + 1 => (h.wkClosed n).wk

section

variable {n : Nat} {ft : FExpr} {e : Expr E.1 ℓ n}

theorem FExpr.Denotes.wkN :
    FExpr.Denotes L E 0 ft e →
    (k : Nat) →
    FExpr.Denotes L E 0 ft (e.wkN k)
  | h, 0 => h
  | h, k + 1 => (h.wkN k).wk

theorem FExpr.Denotes.wkNOpen (k : Nat) :
    FExpr.Denotes L E 0 ft e →
    FExpr.Denotes L E k ft (e.wkN k) := by
  intro h
  rw [Expr.wkN_eq_rename]
  exact h.rename _ (Nat.zero_le k) (by omega)
    ⟨fun v _ => rfl, fun v hv => absurd v.isLt (by omega)⟩

end

theorem FExpr.Denotes.noFVar {m d : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hf : fe.data.hasFVar = false) :
    FExpr.Denotes L E d fe e →
    FExpr.Denotes L E (d + 1) fe e := by
  intro h
  induction h with
  | bvar hi hj => exact .bvar hi (by omega)
  | fvar hi =>
    rw [FExpr.data_fvar, Data.hasFVar_mk] at hf
    cases hf
  | sort hl => exact .sort hl
  | const hls hη hls' => exact .const hls hη hls'
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    rw [FExpr.data_ind] at hf
    exact .ind hls hps his hη hs hls'
      (fun p => ihps p (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun i => ihis i (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.data_ctor] at hf
    exact .ctor hls hps hfds hrecFds hη hs hc hls'
      (fun p => ihps p (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun f => ihfds f (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun f => ihrecFds f (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.data_recr] at hf
    exact .recr hls hps hms hmins his hη hs hls' hl
      (fun p => ihps p (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun fe => ihms fe (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun fe c => ihmins fe c (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (fun i => ihis i (Data.hasFVar_eq_false_of_mem hf (by simp [FExpr.data_mem_map])))
      (ihmaj (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | quot hη hl _ _ ihα ihr =>
    rw [FExpr.data_quot] at hf
    exact .quot hη hl
      (ihα (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihr (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | quotMk hη hl _ _ _ ihα ihr iha =>
    rw [FExpr.data_quotMk] at hf
    exact .quotMk hη hl
      (ihα (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihr (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (iha (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.data_quotLift] at hf
    exact .quotLift hη hl₁ hl₂
      (ihα (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihr (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihβ (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihf (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihh (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (iha (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.data_quotInd] at hf
    exact .quotInd hη hl
      (ihα (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihr (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihβ (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (ihf (Data.hasFVar_eq_false_of_mem hf (by simp)))
      (iha (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | proj hstruct hη hs hidx _ ihe =>
    rw [FExpr.data_proj] at hf
    exact .proj hstruct hη hs hidx (ihe (Data.hasFVar_eq_false_of_mem hf (by simp)))
  | app _ _ ihf iha =>
    rw [FExpr.data_app, Data.hasFVar_mkApp, Bool.or_eq_false_iff] at hf
    exact .app (ihf hf.1) (iha hf.2)
  | lam _ _ iht ihb =>
    rw [FExpr.data_lam, Data.hasFVar_mkBinder, Bool.or_eq_false_iff] at hf
    exact .lam (iht hf.1) (ihb hf.2)
  | forallE _ _ iht ihb =>
    rw [FExpr.data_forallE, Data.hasFVar_mkBinder, Bool.or_eq_false_iff] at hf
    exact .forallE (iht hf.1) (ihb hf.2)
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.data_letE, Data.hasFVar_mkLet, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hf
    exact .letE (iht hf.1.1) (ihv hf.1.2) (ihb hf.2)
  | natLit hNat => exact .natLit hNat
  | strLit hNat hList hChar hOfNat hString => exact .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.fvarRange_le {m k : Nat} {fe : FExpr} {e : Expr E.1 ℓ m} :
    FExpr.Denotes L E k fe e →
    fe.fvarRange ≤ m - k := by
  intro h
  induction h with
  | bvar hi hj => simp
  | fvar hi =>
    rw [FExpr.fvarRange_fvar]
    omega
  | sort hl => simp
  | const hls hη hls' => simp
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    rw [FExpr.fvarRange_ind]
    refine Data.maxArr_le fun x hx => ?_
    simp only [Array.mem_append, Array.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihps ⟨i, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihis ⟨i, by omega⟩
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.fvarRange_ctor]
    refine Data.maxArr_le fun x hx => ?_
    simp only [Array.mem_append, Array.mem_map] at hx
    rcases hx with (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihps ⟨i, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihfds ⟨i, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihrecFds ⟨i, by omega⟩
  | @recr n k pos s ι η s' ls ls' l l' ps ms mins is maj ps' ms' mins' is' maj' hls hps hms
      hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.fvarRange_recr]
    refine Data.maxArr_le fun x hx => ?_
    simp only [Array.mem_append, Array.mem_map, Array.mem_singleton] at hx
    rcases hx with (((⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩) | rfl
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihps ⟨i, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihms ⟨i, by omega⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      have := ihmins (Fin.decodeSigma ι.nctors ⟨i, by omega⟩).1
        (Fin.decodeSigma ι.nctors ⟨i, by omega⟩).2
      simpa using this
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
      exact ihis ⟨i, by omega⟩
    · exact ihmaj
  | quot hη hl _ _ ihα ihr =>
    rw [FExpr.fvarRange_quot]
    refine Data.maxArr_le fun x hx => ?_
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [ihα, ihr]
  | quotMk hη hl _ _ _ ihα ihr iha =>
    rw [FExpr.fvarRange_quotMk]
    refine Data.maxArr_le fun x hx => ?_
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [ihα, ihr, iha]
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.fvarRange_quotLift]
    refine Data.maxArr_le fun x hx => ?_
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ihα, ihr, ihβ, ihf, ihh, iha]
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.fvarRange_quotInd]
    refine Data.maxArr_le fun x hx => ?_
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [ihα, ihr, ihβ, ihf, iha]
  | proj hstruct hη hs hidx _ ihe =>
    rw [FExpr.fvarRange_proj]
    refine Data.maxArr_le fun x hx => ?_
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ihe
  | app _ _ ihf iha =>
    rw [FExpr.fvarRange_app]
    exact Nat.max_le.mpr ⟨ihf, iha⟩
  | lam _ _ iht ihb =>
    rw [FExpr.fvarRange_lam]
    exact Nat.max_le.mpr ⟨iht, by omega⟩
  | forallE _ _ iht ihb =>
    rw [FExpr.fvarRange_forallE]
    exact Nat.max_le.mpr ⟨iht, by omega⟩
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.fvarRange_letE]
    exact Nat.max_le.mpr ⟨iht, Nat.max_le.mpr ⟨ihv, by omega⟩⟩
  | natLit hNat => simp
  | strLit hNat hList hChar hOfNat hString => simp

theorem FExpr.Denotes.bindUnused {m d : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hr : fe.fvarRange + d + 1 ≤ m) :
    FExpr.Denotes L E d fe e →
    FExpr.Denotes L E (d + 1) fe e := by
  intro h
  induction h with
  | bvar hi hj => exact .bvar hi (by omega)
  | fvar hi =>
    rw [FExpr.fvarRange_fvar] at hr
    exact .fvar (by omega)
  | sort hl => exact .sort hl
  | const hls hη hls' => exact .const hls hη hls'
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    rw [FExpr.fvarRange_ind] at hr
    exact .ind hls hps his hη hs hls'
      (fun p => ihps p (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun i => ihis i (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.fvarRange_ctor] at hr
    exact .ctor hls hps hfds hrecFds hη hs hc hls'
      (fun p => ihps p (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun f => ihfds f (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun f => ihrecFds f (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.fvarRange_recr] at hr
    exact .recr hls hps hms hmins his hη hs hls' hl
      (fun p => ihps p (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun fe => ihms fe (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun fe c => ihmins fe c (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (fun i => ihis i (Data.maxArr_bound hr (by simp [FExpr.fvarRange_mem_map])))
      (ihmaj (Data.maxArr_bound hr (by simp)))
  | quot hη hl _ _ ihα ihr =>
    rw [FExpr.fvarRange_quot] at hr
    exact .quot hη hl
      (ihα (Data.maxArr_bound hr (by simp)))
      (ihr (Data.maxArr_bound hr (by simp)))
  | quotMk hη hl _ _ _ ihα ihr iha =>
    rw [FExpr.fvarRange_quotMk] at hr
    exact .quotMk hη hl
      (ihα (Data.maxArr_bound hr (by simp)))
      (ihr (Data.maxArr_bound hr (by simp)))
      (iha (Data.maxArr_bound hr (by simp)))
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.fvarRange_quotLift] at hr
    exact .quotLift hη hl₁ hl₂
      (ihα (Data.maxArr_bound hr (by simp)))
      (ihr (Data.maxArr_bound hr (by simp)))
      (ihβ (Data.maxArr_bound hr (by simp)))
      (ihf (Data.maxArr_bound hr (by simp)))
      (ihh (Data.maxArr_bound hr (by simp)))
      (iha (Data.maxArr_bound hr (by simp)))
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.fvarRange_quotInd] at hr
    exact .quotInd hη hl
      (ihα (Data.maxArr_bound hr (by simp)))
      (ihr (Data.maxArr_bound hr (by simp)))
      (ihβ (Data.maxArr_bound hr (by simp)))
      (ihf (Data.maxArr_bound hr (by simp)))
      (iha (Data.maxArr_bound hr (by simp)))
  | proj hstruct hη hs hidx _ ihe =>
    rw [FExpr.fvarRange_proj] at hr
    exact .proj hstruct hη hs hidx (ihe (Data.maxArr_bound hr (by simp)))
  | app _ _ ihf iha =>
    rw [FExpr.fvarRange_app] at hr
    exact .app (ihf (by omega)) (iha (by omega))
  | lam _ _ iht ihb =>
    rw [FExpr.fvarRange_lam] at hr
    exact .lam (iht (by omega)) (ihb (by omega))
  | forallE _ _ iht ihb =>
    rw [FExpr.fvarRange_forallE] at hr
    exact .forallE (iht (by omega)) (ihb (by omega))
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.fvarRange_letE] at hr
    exact .letE (iht (by omega)) (ihv (by omega)) (ihb (by omega))
  | natLit hNat => exact .natLit hNat
  | strLit hNat hList hChar hOfNat hString => exact .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.instL_skip {n k : Nat} {fe : FExpr} {e : Expr E.1 ℓ n}
    (hp : fe.data.hasLevelParam = false) (σ : Param ℓ → RawLevel ℓ') :
    FExpr.Denotes L E k fe e →
    FExpr.Denotes L E k fe e{fun p : Param ℓ => (⟦σ p⟧ : Level ℓ')} := by
  intro h
  induction h with
  | bvar hi hj => exact .bvar hi hj
  | fvar hi => exact .fvar hi
  | sort hl =>
    rw [FExpr.data_sort, Data.hasLevelParam_mk] at hp
    simpa! [← Level.mk_inst, InstLevel.inst_tuple] using .sort (hl.inst_of_hasParam_eq_false hp σ)
  | const hls hη hls' =>
    rw [FExpr.data_const, Data.hasLevelParam_mk, Array.any_eq_false] at hp
    simpa! [← Level.mk_inst, InstLevel.inst_tuple] using .const hls hη (fun i =>
      (hls' i).inst_of_hasParam_eq_false (by simpa using hp _ (hls.symm ▸ i.isLt)) σ)
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    rw [FExpr.data_ind] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    rw [Array.any_eq_false] at hlp
    simpa! [← Level.mk_inst, InstLevel.inst_tuple] using .ind hls hps his hη hs
      (fun i => (hls' i).inst_of_hasParam_eq_false (by simpa using hlp _ (hls.symm ▸ i.isLt)) σ)
      (fun p => ihps p (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun i => ihis i (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.data_ctor] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    rw [Array.any_eq_false] at hlp
    simpa! [← Level.mk_inst, InstLevel.inst_tuple] using .ctor hls hps hfds hrecFds hη hs hc
      (fun i => (hls' i).inst_of_hasParam_eq_false (by simpa using hlp _ (hls.symm ▸ i.isLt)) σ)
      (fun p => ihps p (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun f => ihfds f (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun f => ihrecFds f (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.data_recr] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    rw [Bool.or_eq_false_iff, Array.any_eq_false] at hlp
    simpa! [← Level.mk_inst, InstLevel.inst_tuple] using .recr hls hps hms hmins his hη hs
      (fun i => (hls' i).inst_of_hasParam_eq_false (by simpa using hlp.1 _ (hls.symm ▸ i.isLt)) σ)
      (hl.inst_of_hasParam_eq_false hlp.2 σ)
      (fun p => ihps p (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun fe => ihms fe (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun fe c => ihmins fe c (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (fun i => ihis i (Data.hasLevelParam_eq_false_of_mem hp (by simp [FExpr.data_mem_map])))
      (ihmaj (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | quot hη hl _ _ ihα ihr =>
    rw [FExpr.data_quot] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    simpa! [← Level.mk_inst] using .quot hη
      (hl.inst_of_hasParam_eq_false hlp σ)
      (ihα (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihr (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | quotMk hη hl _ _ _ ihα ihr iha =>
    rw [FExpr.data_quotMk] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    simpa! [← Level.mk_inst] using .quotMk hη
      (hl.inst_of_hasParam_eq_false hlp σ)
      (ihα (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihr (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (iha (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.data_quotLift] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    rw [Bool.or_eq_false_iff] at hlp
    simpa! [← Level.mk_inst] using .quotLift hη
      (hl₁.inst_of_hasParam_eq_false hlp.1 σ)
      (hl₂.inst_of_hasParam_eq_false hlp.2 σ)
      (ihα (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihr (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihβ (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihf (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihh (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (iha (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.data_quotInd] at hp
    have hlp := Data.hasLevelParam_eq_false_init hp
    simpa! [← Level.mk_inst] using .quotInd hη
      (hl.inst_of_hasParam_eq_false hlp σ)
      (ihα (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihr (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihβ (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (ihf (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
      (iha (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | proj hstruct hη hs hidx _ ihe =>
    rw [FExpr.data_proj] at hp
    rw [Inductive.IsStructure.projTerm_instL]
    simpa [← Level.mk_inst, InstLevel.inst_tuple] using
      .proj hstruct hη hs hidx (ihe (Data.hasLevelParam_eq_false_of_mem hp (by simp)))
  | app _ _ ihf iha =>
    rw [FExpr.data_app, Data.hasLevelParam_mkApp, Bool.or_eq_false_iff] at hp
    exact .app (ihf hp.1) (iha hp.2)
  | lam _ _ iht ihb =>
    rw [FExpr.data_lam, Data.hasLevelParam_mkBinder, Bool.or_eq_false_iff] at hp
    exact .lam (iht hp.1) (ihb hp.2)
  | forallE _ _ iht ihb =>
    rw [FExpr.data_forallE, Data.hasLevelParam_mkBinder, Bool.or_eq_false_iff] at hp
    exact .forallE (iht hp.1) (ihb hp.2)
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.data_letE, Data.hasLevelParam_mkLet, Bool.or_eq_false_iff,
      Bool.or_eq_false_iff] at hp
    exact .letE (iht hp.1.1) (ihv hp.1.2) (ihb hp.2)
  | natLit hNat =>
    rw [Literals.instL_natLit]
    exact .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    rw [Literals.instL_strLit]
    exact .strLit hNat hList hChar hOfNat hString

structure Subst.Instantiates {m n q : Nat} (p d : Nat) (a' : Expr E.1 ℓ q) (σ : Subst E.1 ℓ m n) :
    Prop where
  size : p + d + 1 = m
  le : q + d ≤ n
  scope : m ≤ n + 1
  free : ∀ v : Var m, v.val < p → ∃ w : Var n, σ v = .var w ∧ w.val = v.val
  here : ∀ v : Var m, v.val = p → σ v = a'.rename (Fin.castLE (Nat.le_of_add_right_le le))
  bound : ∀ v : Var m, p < v.val → ∃ w : Var n, σ v = .var w ∧ w.val + m = v.val + n

theorem Subst.Instantiates.lift {m n q p d : Nat} {a' : Expr E.1 ℓ q} {σ : Subst E.1 ℓ m n}
    (h : Subst.Instantiates p d a' σ) :
    Subst.Instantiates p (d + 1) a' σ.lift where
  size := by have := h.size; omega
  le := by have := h.le; omega
  scope := by have := h.scope; omega
  free v hv := by
    have := h.size
    have ⟨w, hw, hwv⟩ := h.free ⟨v.val, by omega⟩ hv
    refine ⟨w.castSucc, ?_, by simpa using hwv⟩
    simp [Subst.lift, show v.val < m by omega, hw, Expr.wk, Expr.wkFrom, Expr.rename]
  here v hv := by
    have := h.size
    have := h.le
    simp [Subst.lift, show v.val < m by omega, h.here ⟨v.val, by omega⟩ hv,
      Expr.wk, Expr.wkFrom]
    congr 1
    funext w
    simp [Ren.comp, show w.val < n by omega]
  bound v hv := by
    by_cases hvm : v.val < m
    · have ⟨w, hw, hwv⟩ := h.bound ⟨v.val, hvm⟩ hv
      refine ⟨w.castSucc, ?_, by simp at hwv ⊢; omega⟩
      simp [Subst.lift, hvm, hw, Expr.wk, Expr.wkFrom, Expr.rename]
    · refine ⟨Fin.last n, by simp [Subst.lift, hvm], ?_⟩
      simp
      omega

theorem FExpr.Denotes.drop {m k : Nat} {fb : FExpr} {b : Expr E.1 ℓ m}
    {n q p d : Nat} {a : Expr E.1 ℓ q} {σ : Subst E.1 ℓ m n} (hk : k = d + 1)
    (hσ : Subst.Instantiates p d a σ)
    (hc : fb.data.looseBVarRange.toNat ≤ d ∧ fb.data.looseBVarRange.toNat < Data.maxRange) :
    FExpr.Denotes L E k fb b →
    FExpr.Denotes L E d fb (b.subst σ) := by
  intro hb
  induction hb generalizing n p d with
  | @bvar m k i j hi hj =>
    rw [FExpr.data_bvar, Data.toNat_looseBVarRange_mk] at hc
    have := hσ.size
    have ⟨w, hw, hwv⟩ := hσ.bound ⟨i, by omega⟩ (by simp; omega)
    simpa [Expr.subst, hw] using .bvar (i := w.val) (by simp at hwv; omega) (by omega)
  | @fvar m k i hi =>
    have := hσ.size
    have := hσ.scope
    have ⟨w, hw, hwv⟩ := hσ.free ⟨i, by omega⟩ (by simp; omega)
    simpa [Expr.subst, hw, show w = ⟨i, by omega⟩ by ext; simpa using hwv] using .fvar (by omega)
  | sort hl => exact .sort hl
  | const hls hη hls' => exact .const hls hη hls'
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    rw [FExpr.data_ind] at hc
    exact .ind hls hps his hη hs hls'
      (fun p => ihps p hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun i => ihis i hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
  | ctor hls hps hfds hrecFds hη hs hc' hls' _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.data_ctor] at hc
    exact .ctor hls hps hfds hrecFds hη hs hc' hls'
      (fun p => ihps p hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun f => ihfds f hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun f => ihrecFds f hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.data_recr] at hc
    exact .recr hls hps hms hmins his hη hs hls' hl
      (fun p => ihps p hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun ft => ihms ft hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun ft c => ihmins ft c hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (fun i => ihis i hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp [FExpr.data_mem_map])))
      (ihmaj hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | quot hη hl _ _ ihα ihr =>
    rw [FExpr.data_quot] at hc
    exact .quot hη hl
      (ihα hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihr hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | quotMk hη hl _ _ _ ihα ihr iha =>
    rw [FExpr.data_quotMk] at hc
    exact .quotMk hη hl
      (ihα hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihr hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (iha hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.data_quotLift] at hc
    exact .quotLift hη hl₁ hl₂
      (ihα hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihr hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihβ hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihf hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihh hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (iha hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.data_quotInd] at hc
    exact .quotInd hη hl
      (ihα hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihr hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihβ hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (ihf hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
      (iha hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | proj hstruct hη hs hidx _ ihe =>
    rw [FExpr.data_proj] at hc
    rw [Inductive.IsStructure.projTerm_subst]
    exact .proj hstruct hη hs hidx (ihe hk hσ (Data.closed_of_mem hc.1 hc.2 (by simp)))
  | app _ _ ihf iha =>
    rw [FExpr.data_app] at hc
    exact .app (ihf hk hσ (Data.closed_of_mkApp_left hc.1 hc.2))
      (iha hk hσ (Data.closed_of_mkApp_right hc.1 hc.2))
  | lam _ _ iht ihb =>
    rw [FExpr.data_lam] at hc
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc.1 hc.2
    exact .lam (iht hk hσ ht) (ihb (by omega) hσ.lift hb)
  | forallE _ _ iht ihb =>
    rw [FExpr.data_forallE] at hc
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc.1 hc.2
    exact .forallE (iht hk hσ ht) (ihb (by omega) hσ.lift hb)
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.data_letE] at hc
    have ⟨ht, hv, hb⟩ := Data.closed_of_mkLet hc.1 hc.2
    exact .letE (iht hk hσ ht) (ihv hk hσ hv) (ihb (by omega) hσ.lift hb)
  | natLit hNat =>
    rw [Literals.subst_natLit]
    exact .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    rw [Literals.subst_strLit]
    exact .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.instAtStep {m k q : Nat} {fb fa : FExpr} {b : Expr E.1 ℓ m}
    {a : Expr E.1 ℓ q} :
    FExpr.Denotes L E k fb b →
    (∀ {n p d : Nat} (σ : Subst E.1 ℓ m n),
      k = d + 1 →
      Subst.Instantiates p d a σ →
      FExpr.Denotes L E d (FExpr.instAtCore fa d fb) (b.subst σ)) →
    ∀ {n p d : Nat} (σ : Subst E.1 ℓ m n),
    k = d + 1 →
    Subst.Instantiates p d a σ →
    FExpr.Denotes L E d (FExpr.instAt fa d fb) (b.subst σ) := by
  intro hb hcore n p d σ hk hσ
  by_cases hc : fb.data.looseBVarRange.toNat ≤ d ∧ fb.data.looseBVarRange.toNat < Data.maxRange
  · rw [FExpr.instAt_of_closed fa d hc]
    exact hb.drop hk hσ hc
  · rw [FExpr.instAt_of_not_closed fa d hc]
    exact hcore σ hk hσ

theorem FExpr.Denotes.instAtCore {q m k : Nat} {fa fb : FExpr} {a : Expr E.1 ℓ q}
    {b : Expr E.1 ℓ m} :
    FExpr.Denotes L E 0 fa a →
    FExpr.Denotes L E k fb b →
    ∀ {n p d : Nat} (σ : Subst E.1 ℓ m n),
    k = d + 1 →
    Subst.Instantiates p d a σ →
    FExpr.Denotes L E d (FExpr.instAtCore fa d fb) (b.subst σ) := by
  intro ha hb n p d σ hk hσ
  induction hb generalizing n p d with
  | @bvar m k i j hi hj =>
    have := hσ.size
    by_cases hjd : j < d
    · have ⟨w, hw, hwv⟩ := hσ.bound ⟨i, by omega⟩ (by simp; omega)
      simpa [FExpr.instAtCore, Expr.subst, hjd, hw] using .bvar (i := w.val) (by simp at hwv; omega) hjd
    · have hjd' : j = d := by omega
      simp [FExpr.instAtCore, Expr.subst, hjd', hσ.here ⟨i, by omega⟩ (by simp; omega)]
      have := hσ.le
      exact ha.rename (Fin.castLE (by omega)) (Nat.zero_le d) (by omega)
        ⟨fun v _ => rfl, fun v hv => absurd v.isLt (by omega)⟩
  | @fvar m k i hi =>
    have := hσ.size
    have := hσ.scope
    have ⟨w, hw, hwv⟩ := hσ.free ⟨i, by omega⟩ (by simp; omega)
    simpa [FExpr.instAtCore, Expr.subst, hw, show w = ⟨i, by omega⟩ by ext; simpa using hwv] using .fvar (by omega)
  | sort hl =>
    simpa [FExpr.instAtCore] using .sort hl
  | const hls hη hls' =>
    simpa [FExpr.instAtCore] using .const hls hη hls'
  | ind hls hps his hη hs hls' hps' his' ihps ihis =>
    simpa [FExpr.instAtCore] using .ind hls
      (by simpa using hps)
      (by simpa using his)
      hη hs hls'
      (fun p => by simpa using (hps' p).instAtStep (ihps p) σ hk hσ)
      (fun i => by simpa using (his' i).instAtStep (ihis i) σ hk hσ)
  | ctor hls hps hfds hrecFds hη hs hc hls' hps' hfds' hrecFds' ihps ihfds ihrecFds =>
    simpa [FExpr.instAtCore] using .ctor hls
      (by simpa using hps)
      (by simpa using hfds)
      (by simpa using hrecFds)
      hη hs hc hls'
      (fun p => by simpa using (hps' p).instAtStep (ihps p) σ hk hσ)
      (fun f => by simpa using (hfds' f).instAtStep (ihfds f) σ hk hσ)
      (fun f => by simpa using (hrecFds' f).instAtStep (ihrecFds f) σ hk hσ)
  | recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' hmaj ihps ihms ihmins ihis
      ihmaj =>
    simpa [FExpr.instAtCore] using .recr hls
      (by simpa using hps)
      (by simpa using hms)
      (by simpa using hmins)
      (by simpa using his)
      hη hs hls' hl
      (fun p => by simpa using (hps' p).instAtStep (ihps p) σ hk hσ)
      (fun ft => by simpa using (hms' ft).instAtStep (ihms ft) σ hk hσ)
      (fun ft c => by simpa using (hmins' ft c).instAtStep (ihmins ft c) σ hk hσ)
      (fun i => by simpa using (his' i).instAtStep (ihis i) σ hk hσ)
      (hmaj.instAtStep ihmaj σ hk hσ)
  | quot hη hl hα hr ihα ihr =>
    simpa [FExpr.instAtCore] using .quot hη hl
      (hα.instAtStep ihα σ hk hσ)
      (hr.instAtStep ihr σ hk hσ)
  | quotMk hη hl hα hr ha' ihα ihr iha =>
    simpa [FExpr.instAtCore] using .quotMk hη hl
      (hα.instAtStep ihα σ hk hσ)
      (hr.instAtStep ihr σ hk hσ)
      (ha'.instAtStep iha σ hk hσ)
  | quotLift hη hl₁ hl₂ hα hr hβ hf hh ha' ihα ihr ihβ ihf ihh iha =>
    simpa [FExpr.instAtCore] using .quotLift hη hl₁ hl₂
      (hα.instAtStep ihα σ hk hσ)
      (hr.instAtStep ihr σ hk hσ)
      (hβ.instAtStep ihβ σ hk hσ)
      (hf.instAtStep ihf σ hk hσ)
      (hh.instAtStep ihh σ hk hσ)
      (ha'.instAtStep iha σ hk hσ)
  | quotInd hη hl hα hr hβ hf ha' ihα ihr ihβ ihf iha =>
    simpa [FExpr.instAtCore] using .quotInd hη hl
      (hα.instAtStep ihα σ hk hσ)
      (hr.instAtStep ihr σ hk hσ)
      (hβ.instAtStep ihβ σ hk hσ)
      (hf.instAtStep ihf σ hk hσ)
      (ha'.instAtStep iha σ hk hσ)
  | proj hstruct hη hs hidx he' ihe =>
    simpa [FExpr.instAtCore, Inductive.IsStructure.projTerm_subst] using
      .proj hstruct hη hs hidx (he'.instAtStep ihe σ hk hσ)
  | app hf ha' ihf iha =>
    simpa [FExpr.instAtCore] using .app
      (hf.instAtStep ihf σ hk hσ)
      (ha'.instAtStep iha σ hk hσ)
  | lam ht hb iht ihb =>
    simpa [FExpr.instAtCore] using .lam
      (ht.instAtStep iht σ hk hσ)
      (hb.instAtStep ihb σ.lift (by omega) hσ.lift)
  | forallE ht hb iht ihb =>
    simpa [FExpr.instAtCore] using .forallE
      (ht.instAtStep iht σ hk hσ)
      (hb.instAtStep ihb σ.lift (by omega) hσ.lift)
  | letE ht hv hb iht ihv ihb =>
    simpa [FExpr.instAtCore] using .letE
      (ht.instAtStep iht σ hk hσ)
      (hv.instAtStep ihv σ hk hσ)
      (hb.instAtStep ihb σ.lift (by omega) hσ.lift)
  | natLit hNat =>
    simpa [FExpr.instAtCore] using .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    simpa [FExpr.instAtCore] using .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.instAt {q m k : Nat} {fa fb : FExpr} {a : Expr E.1 ℓ q}
    {b : Expr E.1 ℓ m} :
    FExpr.Denotes L E 0 fa a →
    FExpr.Denotes L E k fb b →
    ∀ {n p d : Nat} (σ : Subst E.1 ℓ m n),
    k = d + 1 →
    Subst.Instantiates p d a σ →
    FExpr.Denotes L E d (FExpr.instAt fa d fb) (b.subst σ) :=
  fun ha hb => hb.instAtStep (ha.instAtCore hb)

theorem FExpr.Denotes.inst {n : Nat} {fb fa : FExpr} {b : Expr E.1 ℓ (n + 1)} {a : Expr E.1 ℓ n} :
    FExpr.Denotes L E 1 fb b →
    FExpr.Denotes L E 0 fa a →
    FExpr.Denotes L E 0 (FExpr.instAt fa 0 fb) (b.inst a) := fun hb ha =>
  ha.instAt hb _ rfl
    { size := rfl
      le := le_rfl
      scope := by omega
      free v hv := ⟨⟨v.val, hv⟩, by simp [Subst.extend, Fin.snoc, hv]; rfl, rfl⟩
      here v hv := by
        obtain rfl : v = Fin.last n := Fin.ext hv
        simp
        exact (Expr.rename_id a).symm
      bound v hv := absurd v.isLt (by omega) }

theorem FExpr.Denotes.instFVarAt {m p d : Nat} {fb : FExpr} {b : Expr E.1 ℓ m}
    (hm : p + d + 1 = m) :
    FExpr.Denotes L E (d + 1) fb b →
    FExpr.Denotes L E d (FExpr.instAt (.fvar p) d fb) b := by
  intro hb
  simpa using (FExpr.Denotes.fvar (Nat.lt_succ_self p)).instAt hb
    Subst.id rfl
    { size := hm
      le := by omega
      scope := by omega
      free v _ := ⟨v, rfl, rfl⟩
      here v hv := by
        exact congrArg Expr.var (Fin.ext hv)
      bound v _ := ⟨v, rfl, rfl⟩ }

theorem FExpr.Denotes.openBVars {m k base : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hm : base + k = m) :
    FExpr.Denotes L E k fe e →
    FExpr.Denotes L E 0 (FExpr.openBVars base k fe) e := by
  intro h
  induction k generalizing base fe with
  | zero => exact h
  | succ k ih => exact ih (by omega) (h.instFVarAt (by omega))

theorem FExpr.Denotes.abstractAtStep {m d x : Nat} {fe : FExpr} {e : Expr E.1 ℓ m} :
    FExpr.Denotes L E d fe e →
    FExpr.Denotes L E (d + 1) (FExpr.abstractAtCore x d fe) e →
    FExpr.Denotes L E (d + 1) (FExpr.abstractAt x d fe) e := by
  intro h hcore
  cases hf : fe.data.hasFVar
  · rw [FExpr.abstractAt_of_not_hasFVar x d hf]
    exact h.noFVar hf
  · rw [FExpr.abstractAt_of_hasFVar x d hf]
    exact hcore

theorem FExpr.Denotes.abstractAtCore {m d x : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hx : x + d + 1 = m) :
    FExpr.Denotes L E d fe e →
    FExpr.Denotes L E (d + 1) (FExpr.abstractAtCore x d fe) e := by
  intro h
  induction h generalizing x with
  | @bvar m d i j hi hj =>
    simpa [FExpr.abstractAtCore] using .bvar hi (by omega)
  | @fvar m d i hi =>
    simp [FExpr.abstractAtCore]
    by_cases hix : i = x
    · simp [hix]
      exact .bvar (by omega) (Nat.lt_succ_self d)
    · simp [hix]
      exact .fvar (by omega)
  | sort hl =>
    simpa [FExpr.abstractAtCore] using .sort hl
  | const hls hη hls' =>
    simpa [FExpr.abstractAtCore] using .const hls hη hls'
  | ind hls hps his hη hs hls' hps' his' ihps ihis =>
    simpa [FExpr.abstractAtCore] using .ind hls
      (by simpa using hps)
      (by simpa using his)
      hη hs hls'
      (fun p => by simpa using (hps' p).abstractAtStep (ihps p hx))
      (fun i => by simpa using (his' i).abstractAtStep (ihis i hx))
  | ctor hls hps hfds hrecFds hη hs hc hls' hps' hfds' hrecFds' ihps ihfds ihrecFds =>
    simpa [FExpr.abstractAtCore] using .ctor hls
      (by simpa using hps)
      (by simpa using hfds)
      (by simpa using hrecFds)
      hη hs hc hls'
      (fun p => by simpa using (hps' p).abstractAtStep (ihps p hx))
      (fun f => by simpa using (hfds' f).abstractAtStep (ihfds f hx))
      (fun f => by simpa using (hrecFds' f).abstractAtStep (ihrecFds f hx))
  | recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' hmaj ihps ihms ihmins ihis
      ihmaj =>
    simpa [FExpr.abstractAtCore] using .recr hls
      (by simpa using hps)
      (by simpa using hms)
      (by simpa using hmins)
      (by simpa using his)
      hη hs hls' hl
      (fun p => by simpa using (hps' p).abstractAtStep (ihps p hx))
      (fun t => by simpa using (hms' t).abstractAtStep (ihms t hx))
      (fun t c => by simpa using (hmins' t c).abstractAtStep (ihmins t c hx))
      (fun i => by simpa using (his' i).abstractAtStep (ihis i hx))
      (hmaj.abstractAtStep (ihmaj hx))
  | quot hη hl hα hr ihα ihr =>
    simpa [FExpr.abstractAtCore] using .quot hη hl
      (hα.abstractAtStep (ihα hx))
      (hr.abstractAtStep (ihr hx))
  | quotMk hη hl hα hr ha ihα ihr iha =>
    simpa [FExpr.abstractAtCore] using .quotMk hη hl
      (hα.abstractAtStep (ihα hx))
      (hr.abstractAtStep (ihr hx))
      (ha.abstractAtStep (iha hx))
  | quotLift hη hl₁ hl₂ hα hr hβ hf hh ha ihα ihr ihβ ihf ihh iha =>
    simpa [FExpr.abstractAtCore] using .quotLift hη hl₁ hl₂
      (hα.abstractAtStep (ihα hx))
      (hr.abstractAtStep (ihr hx))
      (hβ.abstractAtStep (ihβ hx))
      (hf.abstractAtStep (ihf hx))
      (hh.abstractAtStep (ihh hx))
      (ha.abstractAtStep (iha hx))
  | quotInd hη hl hα hr hβ hf ha ihα ihr ihβ ihf iha =>
    simpa [FExpr.abstractAtCore] using .quotInd hη hl
      (hα.abstractAtStep (ihα hx))
      (hr.abstractAtStep (ihr hx))
      (hβ.abstractAtStep (ihβ hx))
      (hf.abstractAtStep (ihf hx))
      (ha.abstractAtStep (iha hx))
  | proj hstruct hη hs hidx he' ihe =>
    simpa [FExpr.abstractAtCore] using .proj hstruct hη hs hidx (he'.abstractAtStep (ihe hx))
  | app hf ha ihf iha =>
    simpa [FExpr.abstractAtCore] using .app
      (hf.abstractAtStep (ihf hx))
      (ha.abstractAtStep (iha hx))
  | lam ht hb iht ihb =>
    simpa [FExpr.abstractAtCore] using .lam
      (ht.abstractAtStep (iht hx))
      (hb.abstractAtStep (ihb (by omega)))
  | forallE ht hb iht ihb =>
    simpa [FExpr.abstractAtCore] using .forallE
      (ht.abstractAtStep (iht hx))
      (hb.abstractAtStep (ihb (by omega)))
  | letE ht hv hb iht ihv ihb =>
    simpa [FExpr.abstractAtCore] using .letE
      (ht.abstractAtStep (iht hx))
      (hv.abstractAtStep (ihv hx))
      (hb.abstractAtStep (ihb (by omega)))
  | natLit hNat =>
    simpa [FExpr.abstractAtCore] using .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    simpa [FExpr.abstractAtCore] using .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.abstractAt {m d x : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hx : x + d + 1 = m) :
    FExpr.Denotes L E d fe e →
    FExpr.Denotes L E (d + 1) (FExpr.abstractAt x d fe) e :=
  fun h => h.abstractAtStep (h.abstractAtCore hx)

theorem FExpr.Denotes.instLStep {n k : Nat} {fe : FExpr} {e : Expr E.1 ℓ n} {us : Array FLevel}
    {σ : Param ℓ → RawLevel ℓ'} :
    FExpr.Denotes L E k fe e →
    FExpr.Denotes L E k (FExpr.instLCore us fe) e{fun p : Param ℓ => (⟦σ p⟧ : Level ℓ')} →
    FExpr.Denotes L E k (FExpr.instL us fe) e{fun p : Param ℓ => (⟦σ p⟧ : Level ℓ')} := by
  intro h hcore
  cases hp : fe.data.hasLevelParam
  · rw [FExpr.instL_of_not_hasLevelParam us hp]
    exact h.instL_skip hp σ
  · rw [FExpr.instL_of_hasLevelParam us hp]
    exact hcore

theorem FExpr.Denotes.instLCore {n k : Nat} {fe : FExpr} {e : Expr E.1 ℓ n} {us : Array FLevel}
    {σ : Param ℓ → RawLevel ℓ'} (hus : us.size = ℓ) :
    FExpr.Denotes L E k fe e →
    (∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (σ i)) →
    FExpr.Denotes L E k (fe.instLCore us) e{fun p : Param ℓ => (⟦σ p⟧ : Level ℓ')} := by
  intro h hus'
  induction h with
  | bvar hi hj =>
    simpa [FExpr.instLCore] using .bvar hi hj
  | fvar hi =>
    simpa [FExpr.instLCore] using .fvar hi
  | sort hl =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .sort (hl.inst hus hus')
  | const hls hη hls' =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using
      .const (by simpa using hls) hη (fun i => by simpa using (hls' i).inst hus hus')
  | ind hls hps his hη hs hls' hps' his' ihps ihis =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .ind
      (by simpa using hls)
      (by simpa using hps)
      (by simpa using his)
      hη hs
      (fun i => by simpa using (hls' i).inst hus hus')
      (fun p => by simpa using (hps' p).instLStep (ihps p))
      (fun i => by simpa using (his' i).instLStep (ihis i))
  | ctor hls hps hfds hrecFds hη hs hc hls' hps' hfds' hrecFds' ihps ihfds ihrecFds =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .ctor
      (by simpa using hls)
      (by simpa using hps)
      (by simpa using hfds)
      (by simpa using hrecFds)
      hη hs hc
      (fun i => by simpa using (hls' i).inst hus hus')
      (fun p => by simpa using (hps' p).instLStep (ihps p))
      (fun f => by simpa using (hfds' f).instLStep (ihfds f))
      (fun f => by simpa using (hrecFds' f).instLStep (ihrecFds f))
  | recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' hmaj ihps ihms ihmins ihis
      ihmaj =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .recr
      (by simpa using hls)
      (by simpa using hps)
      (by simpa using hms)
      (by simpa using hmins)
      (by simpa using his)
      hη hs
      (fun i => by simpa using (hls' i).inst hus hus')
      (hl.inst hus hus')
      (fun p => by simpa using (hps' p).instLStep (ihps p))
      (fun fe => by simpa using (hms' fe).instLStep (ihms fe))
      (fun fe c => by simpa using (hmins' fe c).instLStep (ihmins fe c))
      (fun i => by simpa using (his' i).instLStep (ihis i))
      (hmaj.instLStep ihmaj)
  | quot hη hl hα hr ihα ihr =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using
      .quot hη (hl.inst hus hus') (hα.instLStep ihα) (hr.instLStep ihr)
  | quotMk hη hl hα hr ha ihα ihr iha =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .quotMk hη
      (hl.inst hus hus')
      (hα.instLStep ihα)
      (hr.instLStep ihr)
      (ha.instLStep iha)
  | quotLift hη hl₁ hl₂ hα hr hβ hf hh ha ihα ihr ihβ ihf ihh iha =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .quotLift hη
      (hl₁.inst hus hus')
      (hl₂.inst hus hus')
      (hα.instLStep ihα)
      (hr.instLStep ihr)
      (hβ.instLStep ihβ)
      (hf.instLStep ihf)
      (hh.instLStep ihh)
      (ha.instLStep iha)
  | quotInd hη hl hα hr hβ hf ha ihα ihr ihβ ihf iha =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using .quotInd hη
      (hl.inst hus hus')
      (hα.instLStep ihα)
      (hr.instLStep ihr)
      (hβ.instLStep ihβ)
      (hf.instLStep ihf)
      (ha.instLStep iha)
  | proj hstruct hη hs hidx he' ihe =>
    simpa! [FExpr.instLCore, ← Level.mk_inst, InstLevel.inst_tuple] using
      .proj hstruct hη hs hidx (he'.instLStep ihe)
  | app hf ha ihf iha =>
    simpa [FExpr.instLCore] using .app (hf.instLStep ihf) (ha.instLStep iha)
  | lam ht hb iht ihb =>
    simpa [FExpr.instLCore] using .lam (ht.instLStep iht) (hb.instLStep ihb)
  | forallE ht hb iht ihb =>
    simpa [FExpr.instLCore] using .forallE (ht.instLStep iht) (hb.instLStep ihb)
  | letE ht hv hb iht ihv ihb =>
    simpa [FExpr.instLCore] using .letE (ht.instLStep iht) (hv.instLStep ihv) (hb.instLStep ihb)
  | natLit hNat =>
    simpa [FExpr.instLCore, Literals.instL_natLit] using .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    simpa [FExpr.instLCore, Literals.instL_strLit] using .strLit hNat hList hChar hOfNat hString

theorem FExpr.Denotes.instL {n k : Nat} {fe : FExpr} {e : Expr E.1 ℓ n} {us : Array FLevel}
    {σ : Param ℓ → RawLevel ℓ'} (hus : us.size = ℓ) :
    FExpr.Denotes L E k fe e →
    (∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (σ i)) →
    FExpr.Denotes L E k fe{us} e{fun p : Param ℓ => (⟦σ p⟧ : Level ℓ')} :=
  fun h hus' => h.instLStep (h.instLCore hus hus')

structure Subst.InstFVars {n₀ n k : Nat} (args : Array FExpr) (σ : Subst E.1 ℓ n₀ (n + k)) : Prop where
  size : args.size + k = n₀
  free : ∀ v : Var n₀, (hv : v.val < args.size) →
    ∃ a' : Expr E.1 ℓ n, FExpr.Denotes L E 0 args[v.val] a' ∧ σ v = a'.wkN k
  bound : ∀ v : Var n₀, args.size ≤ v.val →
    ∃ w : Var (n + k), σ v = .var w ∧ w.val + args.size = v.val + n

theorem Subst.InstFVars.lift {n₀ n k : Nat} {args : Array FExpr} {σ : Subst E.1 ℓ n₀ (n + k)}
    (h : Subst.InstFVars (L := L) (E := E) args σ) :
    Subst.InstFVars (L := L) (E := E) (n := n) (k := k + 1) args σ.lift where
  size := by have := h.size; omega
  free v hv := by
    have := h.size
    have ⟨a', ha', hσ⟩ := h.free ⟨v.val, by omega⟩ hv
    exact ⟨a', ha', by simp [Subst.lift, show v.val < n₀ by omega, hσ, Expr.wkN]⟩
  bound v hv := by
    have := h.size
    by_cases hvn : v.val < n₀
    · have ⟨w, hw, hwv⟩ := h.bound ⟨v.val, hvn⟩ hv
      refine ⟨w.castSucc, ?_, by simpa using hwv⟩
      simp [Subst.lift, hvn, hw, Expr.wk]
    · refine ⟨Fin.last (n + k), by simp [Subst.lift, hvn], ?_⟩
      simp
      omega

structure ArgsDenote (L : Literals) (E : Σ ζ, Env ζ) (args : Array FExpr) {m n : Nat} (σ : Subst E.1 ℓ m n) :
    Prop where
  size : args.size = m
  denotes : ∀ v : Fin m, FExpr.Denotes L E 0 (args[v.val]'(size.symm ▸ v.isLt)) (σ v)

namespace ArgsDenote

variable {n m : Nat} {args : Array FExpr} {σ : Subst E.1 ℓ m n}

theorem wkN (k : Nat) :
    ArgsDenote L E args σ →
    ArgsDenote L E args fun v => (σ v).wkN k :=
  fun h => ⟨h.size, fun v => (h.denotes v).wkN k⟩

theorem append {m₂ : Nat} {args₂ : Array FExpr} {σ₂ : Subst E.1 ℓ m₂ n}
    (h : ArgsDenote L E args σ) (h₂ : ArgsDenote L E args₂ σ₂) :
    ArgsDenote L E (args ++ args₂) (Fin.append σ σ₂) where
  size := by simp [h.size, h₂.size]
  denotes v := by
    have hs := h.size
    cases v using Fin.addCases with
    | left v =>
      simp only [Fin.append_left, Fin.val_castAdd]
      rw [Array.getElem_append_left (by omega)]
      exact h.denotes v
    | right v =>
      simp only [Fin.append_right, Fin.val_natAdd]
      rw [Array.getElem_append_right (by omega)]
      rw! [show m + v.val - args.size = v.val by omega]
      exact h₂.denotes v

theorem fvars (n k : Nat) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars n k) (Expr.boundVars n k 0) where
  size := by simp
  denotes v := by simpa using .fvar (by omega)

theorem params {nparams n : Nat} (h : nparams ≤ n) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars 0 nparams)
      (fun p : Fin nparams => (.var ⟨p.val, by omega⟩ : Expr E.1 ℓ n)) where
  size := by simp
  denotes v := by simpa using .fvar (by omega)

theorem liftN (k : Nat) :
    ArgsDenote L E args σ →
    ArgsDenote L E (args ++ FExpr.fvars n k) (σ.liftN k) := by
  intro h
  rw [Subst.liftN_eq_append]
  exact (h.wkN k).append (fvars n k)

theorem extract (h : ArgsDenote L E args σ) (j : Nat) (hj : j ≤ m) :
    ArgsDenote L E (args.extract 0 j) fun v : Fin j => σ (v.castLE hj) where
  size := by simp [h.size]; omega
  denotes v := by simpa using h.denotes (v.castLE hj)

end ArgsDenote

namespace FExpr.Denotes

theorem instFVarsAux {n₀ k n : Nat} {ft : FExpr} {e : Expr E.1 ℓ n₀} {args : Array FExpr}
    {σ : Subst E.1 ℓ n₀ (n + k)} :
    FExpr.Denotes L E k ft e →
    Subst.InstFVars (L := L) (E := E) args σ →
    FExpr.Denotes L E k (ft.instFVarsCore args) (e.subst σ) := by
  intro h hσ
  induction h with
  | @bvar _ k i j hi hj =>
    have := hσ.size
    have ⟨w, hw, hwv⟩ := hσ.bound ⟨i, by omega⟩ (by simp; omega)
    simpa! [FExpr.instFVarsCore, hw] using .bvar (i := w.val) (by simp at hwv; omega) hj
  | @fvar _ k i hi =>
    have := hσ.size
    have ⟨a', ha', hσ'⟩ := hσ.free ⟨i, by omega⟩ (by simp; omega)
    simpa! [FExpr.instFVarsCore, show i < args.size by omega, hσ'] using ha'.wkNOpen k
  | sort hl =>
    simpa [FExpr.instFVarsCore] using .sort hl
  | const hls hη hls' =>
    simpa [FExpr.instFVarsCore] using .const hls hη hls'
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    simpa [FExpr.instFVarsCore] using .ind hls
      (by simpa using hps)
      (by simpa using his)
      hη hs hls'
      (fun p => by simpa using ihps p hσ)
      (fun i => by simpa using ihis i hσ)
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    simpa [FExpr.instFVarsCore] using .ctor hls
      (by simpa using hps)
      (by simpa using hfds)
      (by simpa using hrecFds)
      hη hs hc hls'
      (fun p => by simpa using ihps p hσ)
      (fun ff => by simpa using ihfds ff hσ)
      (fun ff => by simpa using ihrecFds ff hσ)
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    simpa [FExpr.instFVarsCore] using .recr hls
      (by simpa using hps)
      (by simpa using hms)
      (by simpa using hmins)
      (by simpa using his)
      hη hs hls' hl
      (fun p => by simpa using ihps p hσ)
      (fun ft => by simpa using ihms ft hσ)
      (fun ft c => by simpa using ihmins ft c hσ)
      (fun i => by simpa using ihis i hσ)
      (ihmaj hσ)
  | quot hη hl _ _ ihα ihr =>
    simpa [FExpr.instFVarsCore] using .quot hη hl (ihα hσ) (ihr hσ)
  | quotMk hη hl _ _ _ ihα ihr iha =>
    simpa [FExpr.instFVarsCore] using .quotMk hη hl (ihα hσ) (ihr hσ) (iha hσ)
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    simpa [FExpr.instFVarsCore] using .quotLift hη hl₁ hl₂
      (ihα hσ)
      (ihr hσ)
      (ihβ hσ)
      (ihf hσ)
      (ihh hσ)
      (iha hσ)
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    simpa [FExpr.instFVarsCore] using .quotInd hη hl
      (ihα hσ)
      (ihr hσ)
      (ihβ hσ)
      (ihf hσ)
      (iha hσ)
  | proj hstruct hη hs hidx _ ihe =>
    simpa [FExpr.instFVarsCore, Inductive.IsStructure.projTerm_subst] using .proj hstruct hη hs hidx (ihe hσ)
  | app _ _ ihf iha =>
    simpa [FExpr.instFVarsCore] using .app (ihf hσ) (iha hσ)
  | lam _ _ iht ihb =>
    simpa [FExpr.instFVarsCore] using .lam (iht hσ) (ihb hσ.lift)
  | forallE _ _ iht ihb =>
    simpa [FExpr.instFVarsCore] using .forallE (iht hσ) (ihb hσ.lift)
  | letE _ _ _ iht ihv ihb =>
    simpa [FExpr.instFVarsCore] using .letE (iht hσ) (ihv hσ) (ihb hσ.lift)
  | natLit hNat =>
    simpa [FExpr.instFVarsCore, Literals.subst_natLit] using .natLit hNat
  | strLit hNat hList hChar hOfNat hString =>
    simpa [FExpr.instFVarsCore, Literals.subst_strLit] using .strLit hNat hList hChar hOfNat hString

theorem instFVars {m n : Nat} {ft : FExpr} {e : Expr E.1 ℓ m} {args : Array FExpr}
    {σ : Subst E.1 ℓ m n} :
    FExpr.Denotes L E 0 ft e →
    ArgsDenote L E args σ →
    FExpr.Denotes L E 0 (ft.instFVars args) (e.subst σ) := fun h hargs =>
  h.instFVarsAux (k := 0)
    { size := hargs.size
      free v hv := ⟨_, hargs.denotes v, rfl⟩
      bound v hv := absurd v.isLt (by have := hargs.size; omega) }

theorem appsFin {n : Nat} {ff : FExpr} {f : Expr E.1 ℓ n} :
    FExpr.Denotes L E 0 ff f →
    (k : Nat) → (fg : Fin k → FExpr) → (g : Fin k → Expr E.1 ℓ n) →
    (∀ i, FExpr.Denotes L E 0 (fg i) (g i)) →
    FExpr.Denotes L E 0 (Fin.foldl k (fun e i => .app e (fg i)) ff) (f.apps g)
  | hf, 0, _, _, _ => by simpa using hf
  | hf, k + 1, fg, g, hg => by
    rw [Fin.foldl_succ_last, Expr.apps_last]
    exact .app (hf.appsFin k _ _ fun i => hg i.castSucc) (hg (Fin.last k))

theorem apps {n k : Nat} {ff : FExpr} {f : Expr E.1 ℓ n} {args : Array FExpr}
    (hargs : args.size = k) {args' : Fin k → Expr E.1 ℓ n} :
    FExpr.Denotes L E 0 ff f →
    (∀ i : Fin k, FExpr.Denotes L E 0 (args[i.val]'(hargs.symm ▸ i.isLt)) (args' i)) →
    FExpr.Denotes L E 0 (ff.apps args) (f.apps args') := by
  intro hf hargs'
  subst hargs
  exact hf.appsFin _ _ _ hargs'

end FExpr.Denotes

inductive FExpr.NoProj : FExpr → Prop where
  | bvar (i : Nat) :
    FExpr.NoProj (.bvar i)
  | fvar (i : Nat) :
    FExpr.NoProj (.fvar i)
  | sort (l : FLevel) :
    FExpr.NoProj (.sort l)
  | const (pos : Nat) (ls : Array FLevel) :
    FExpr.NoProj (.const pos ls)
  | ind {pos s : Nat} {ls : Array FLevel} {ps is : Array FExpr} :
    (∀ p ∈ ps, FExpr.NoProj p) →
    (∀ i ∈ is, FExpr.NoProj i) →
    FExpr.NoProj (.ind pos s ls ps is)
  | ctor {pos s c : Nat} {ls : Array FLevel} {ps fds recFds : Array FExpr} :
    (∀ p ∈ ps, FExpr.NoProj p) →
    (∀ f ∈ fds, FExpr.NoProj f) →
    (∀ r ∈ recFds, FExpr.NoProj r) →
    FExpr.NoProj (.ctor pos s c ls ps fds recFds)
  | recr {pos s : Nat} {ls : Array FLevel} {l : FLevel} {ps ms mins is : Array FExpr}
    {maj : FExpr} :
    (∀ p ∈ ps, FExpr.NoProj p) →
    (∀ m ∈ ms, FExpr.NoProj m) →
    (∀ m ∈ mins, FExpr.NoProj m) →
    (∀ i ∈ is, FExpr.NoProj i) →
    FExpr.NoProj maj →
    FExpr.NoProj (.recr pos s ls l ps ms mins is maj)
  | quot {pos : Nat} {l : FLevel} {α r : FExpr} :
    FExpr.NoProj α →
    FExpr.NoProj r →
    FExpr.NoProj (.quot pos l α r)
  | quotMk {pos : Nat} {l : FLevel} {α r a : FExpr} :
    FExpr.NoProj α →
    FExpr.NoProj r →
    FExpr.NoProj a →
    FExpr.NoProj (.quotMk pos l α r a)
  | quotLift {pos : Nat} {l₁ l₂ : FLevel} {α r β f h a : FExpr} :
    FExpr.NoProj α →
    FExpr.NoProj r →
    FExpr.NoProj β →
    FExpr.NoProj f →
    FExpr.NoProj h →
    FExpr.NoProj a →
    FExpr.NoProj (.quotLift pos l₁ l₂ α r β f h a)
  | quotInd {pos : Nat} {l : FLevel} {α r β f a : FExpr} :
    FExpr.NoProj α →
    FExpr.NoProj r →
    FExpr.NoProj β →
    FExpr.NoProj f →
    FExpr.NoProj a →
    FExpr.NoProj (.quotInd pos l α r β f a)
  | app {f a : FExpr} :
    FExpr.NoProj f →
    FExpr.NoProj a →
    FExpr.NoProj (.app f a)
  | lam {t b : FExpr} :
    FExpr.NoProj t →
    FExpr.NoProj b →
    FExpr.NoProj (.lam t b)
  | forallE {t b : FExpr} :
    FExpr.NoProj t →
    FExpr.NoProj b →
    FExpr.NoProj (.forallE t b)
  | letE {t v b : FExpr} :
    FExpr.NoProj t →
    FExpr.NoProj v →
    FExpr.NoProj b →
    FExpr.NoProj (.letE t v b)
  | natLit (num : Nat) :
    FExpr.NoProj (.natLit num)
  | strLit (str : String) :
    FExpr.NoProj (.strLit str)

theorem FExpr.charList_noProj (L : Literals) (cs : List Char) : (FExpr.charList L cs).NoProj := by
  induction cs with
  | nil =>
    refine .ctor (fun p hp => ?_) (by simp) (by simp)
    obtain rfl : p = FExpr.char L := by simpa using hp
    exact .ind (by simp) (by simp)
  | cons c cs ih =>
    refine .ctor (fun p hp => ?_) (fun f hf => ?_) (fun r hr => ?_)
    · obtain rfl : p = FExpr.char L := by simpa using hp
      exact .ind (by simp) (by simp)
    · obtain rfl : f = FExpr.op₁ L.charOfNat (.natLit c.toNat) := by simpa using hf
      exact .app (.const _ _) (.natLit _)
    · obtain rfl : r = FExpr.charList L cs := by simpa using hr
      exact ih

theorem FExpr.strLitExpand_noProj (L : Literals) (str : String) :
    (FExpr.strLitExpand L str).NoProj :=
  .app (.const _ _) (FExpr.charList_noProj L _)

theorem FExpr.Denotes.unique {n k : Nat} {fe : FExpr} {e₁ e₂ : Expr E.1 ℓ n} :
    FExpr.Denotes L E k fe e₁ →
    FExpr.Denotes L E k fe e₂ →
    fe.NoProj →
    e₁ = e₂
  | .bvar hi _, .bvar hi₂ _, _ => congrArg Expr.var (Fin.ext (by simp; omega))
  | .fvar _, .fvar _, _ => rfl
  | .sort hl, .sort hl₂, _ => by rw [hl.unique hl₂]
  | .const _ hη hls', .const _ hη₂ hls'₂, _ => by
    cases hη.symm.trans hη₂
    obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
    rfl
  | .ind _ _ _ hη hs hls' hps his, .ind _ _ _ hη₂ hs₂ hls'₂ hps₂ his₂, .ind np ni => by
    cases hη.symm.trans hη₂
    cases Fin.ext (hs.trans hs₂.symm)
    obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
    congr 1 <;> funext i
    exacts [(hps i).unique (hps₂ i) (np _ (Array.getElem_mem _)),
      (his i).unique (his₂ i) (ni _ (Array.getElem_mem _))]
  | .ctor _ _ _ _ hη hs hc hls' hps hfds hrecFds,
    .ctor _ _ _ _ hη₂ hs₂ hc₂ hls'₂ hps₂ hfds₂ hrecFds₂, .ctor np nf nr => by
    cases hη.symm.trans hη₂
    cases Fin.ext (hs.trans hs₂.symm)
    cases Fin.ext (hc.trans hc₂.symm)
    obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
    congr 1 <;> funext i
    exacts [(hps i).unique (hps₂ i) (np _ (Array.getElem_mem _)),
      (hfds i).unique (hfds₂ i) (nf _ (Array.getElem_mem _)),
      (hrecFds i).unique (hrecFds₂ i) (nr _ (Array.getElem_mem _))]
  | .recr _ _ _ _ _ hη hs hls' hl hps hms hmins his hmaj,
    .recr _ _ _ _ _ hη₂ hs₂ hls'₂ hl₂ hps₂ hms₂ hmins₂ his₂ hmaj₂, .recr np nm nmin ni nmaj => by
    cases hη.symm.trans hη₂
    cases Fin.ext (hs.trans hs₂.symm)
    obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
    obtain rfl := hl.unique hl₂
    congr 1
    · funext i
      exact (hps i).unique (hps₂ i) (np _ (Array.getElem_mem _))
    · funext i
      exact (hms i).unique (hms₂ i) (nm _ (Array.getElem_mem _))
    · funext i c
      exact (hmins i c).unique (hmins₂ i c) (nmin _ (Array.getElem_mem _))
    · funext i
      exact (his i).unique (his₂ i) (ni _ (Array.getElem_mem _))
    · exact hmaj.unique hmaj₂ nmaj
  | .quot hη hl hα hr, .quot hη₂ hl₂ hα₂ hr₂, .quot nα nr => by
    cases hη.symm.trans hη₂
    obtain rfl := hl.unique hl₂
    rw [hα.unique hα₂ nα, hr.unique hr₂ nr]
  | .quotMk hη hl hα hr ha, .quotMk hη₂ hl₂ hα₂ hr₂ ha₂, .quotMk nα nr na => by
    cases hη.symm.trans hη₂
    obtain rfl := hl.unique hl₂
    rw [hα.unique hα₂ nα, hr.unique hr₂ nr, ha.unique ha₂ na]
  | .quotLift hη hl₁ hl₂ hα hr hβ hf hh ha,
    .quotLift hη₂ hl₁₂ hl₂₂ hα₂ hr₂ hβ₂ hf₂ hh₂ ha₂, .quotLift nα nr nβ nf nh na => by
    cases hη.symm.trans hη₂
    obtain rfl := hl₁.unique hl₁₂
    obtain rfl := hl₂.unique hl₂₂
    rw [hα.unique hα₂ nα, hr.unique hr₂ nr, hβ.unique hβ₂ nβ, hf.unique hf₂ nf,
      hh.unique hh₂ nh, ha.unique ha₂ na]
  | .quotInd hη hl hα hr hβ hf ha, .quotInd hη₂ hl₂ hα₂ hr₂ hβ₂ hf₂ ha₂,
    .quotInd nα nr nβ nf na => by
    cases hη.symm.trans hη₂
    obtain rfl := hl.unique hl₂
    rw [hα.unique hα₂ nα, hr.unique hr₂ nr, hβ.unique hβ₂ nβ, hf.unique hf₂ nf,
      ha.unique ha₂ na]
  | .app hf ha, .app hf₂ ha₂, .app nf na => by rw [hf.unique hf₂ nf, ha.unique ha₂ na]
  | .lam ht hb, .lam ht₂ hb₂, .lam nt nb => by rw [ht.unique ht₂ nt, hb.unique hb₂ nb]
  | .forallE ht hb, .forallE ht₂ hb₂, .forallE nt nb => by
    rw [ht.unique ht₂ nt, hb.unique hb₂ nb]
  | .letE ht hv hb, .letE ht₂ hv₂ hb₂, .letE nt nv nb => by
    rw [ht.unique ht₂ nt, hv.unique hv₂ nv, hb.unique hb₂ nb]
  | .natLit hNat, .natLit hNat₂, _ => by
    cases hNat.symm.trans hNat₂
    rfl
  | .strLit hNat hList hChar hOfNat hString,
    .strLit hNat₂ hList₂ hChar₂ hOfNat₂ hString₂, _ => by
    cases hNat.symm.trans hNat₂
    cases hList.symm.trans hList₂
    cases hChar.symm.trans hChar₂
    cases hOfNat.symm.trans hOfNat₂
    cases hString.symm.trans hString₂
    rfl

theorem FExpr.Denotes.strengthen {n : Nat} {fe : FExpr} {e : Expr E.1 ℓ (n + 1)}
    (hr : fe.fvarRange ≤ n) (hc : fe.data.looseBVarRange.toNat = 0) :
    FExpr.Denotes L E 0 fe e →
    ∃ e₀ : Expr E.1 ℓ n, FExpr.Denotes L E 0 fe e₀ := by
  intro h
  have h₁ := (h.bindUnused (by omega)).inst
    (.sort FLevel.Denotes.zero : FExpr.Denotes L E 0 (.sort .zero) (.sort ⟦.zero⟧ : Expr E.1 ℓ n))
  rw [FExpr.instAt_of_closed _ 0 ⟨by omega, by rw [hc]; decide⟩] at h₁
  exact ⟨_, h₁⟩

theorem FExpr.Denotes.unopenStep {m d p : Nat} {fb : FExpr} {b₀ b' : Expr E.1 ℓ m}
    (hm : p + d + 1 = m) :
    FExpr.Denotes L E (d + 1) fb b₀ →
    (FExpr.Denotes L E d (FExpr.instAtCore (.fvar p) d fb) b' →
      FExpr.Denotes L E (d + 1) fb b') →
    FExpr.Denotes L E d (FExpr.instAt (.fvar p) d fb) b' →
    FExpr.Denotes L E (d + 1) fb b' := by
  intro h₀ hcore h'
  by_cases hc : fb.data.looseBVarRange.toNat ≤ d ∧ fb.data.looseBVarRange.toNat < Data.maxRange
  · rw [FExpr.instAt_of_closed _ d hc] at h'
    have := h₀.fvarRange_le
    exact h'.bindUnused (by omega)
  · rw [FExpr.instAt_of_not_closed _ d hc] at h'
    exact hcore h'

theorem FExpr.Denotes.unopenCore {m k : Nat} {fb : FExpr} {b₀ : Expr E.1 ℓ m} :
    FExpr.Denotes L E k fb b₀ →
    ∀ {d p : Nat} {b' : Expr E.1 ℓ m},
    k = d + 1 →
    p + d + 1 = m →
    FExpr.Denotes L E d (FExpr.instAtCore (.fvar p) d fb) b' →
    FExpr.Denotes L E k fb b' := by
  intro h₀ d p b' hk hm h'
  induction h₀ generalizing d with
  | @bvar m k i j hi hj =>
    subst hk
    by_cases hjd : j < d
    · simp only [FExpr.instAtCore, hjd] at h'
      cases h' with
      | bvar hi₂ hj₂ => exact .bvar hi₂ (by omega)
    · have hjd' : j = d := by omega
      simp only [FExpr.instAtCore, hjd', Nat.lt_irrefl] at h'
      cases h' with
      | fvar hi₂ => exact .bvar (i := p) (by omega) (by omega)
  | fvar hi =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | fvar hi₂ => exact .fvar hi
  | sort hl =>
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | sort hl₂ => exact .sort hl₂
  | const hls hη hls' =>
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | const hls₂ hη₂ hls'₂ => exact .const hls₂ hη₂ hls'₂
  | ind hls hps his hη hs hls' hps' his' ihps ihis =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | ind _ _ _ hη₂ hs₂ hls'₂ hps₂ his₂ =>
      cases hη.symm.trans hη₂
      cases Fin.ext (hs.trans hs₂.symm)
      exact .ind hls hps his hη hs hls'₂
        (fun q => (hps' q).unopenStep hm (ihps q rfl hm) (by simpa using hps₂ q))
        (fun i => (his' i).unopenStep hm (ihis i rfl hm) (by simpa using his₂ i))
  | ctor hls hps hfds hrecFds hη hs hc hls' hps' hfds' hrecFds' ihps ihfds ihrecFds =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | ctor _ _ _ _ hη₂ hs₂ hc₂ hls'₂ hps₂ hfds₂ hrecFds₂ =>
      cases hη.symm.trans hη₂
      cases Fin.ext (hs.trans hs₂.symm)
      cases Fin.ext (hc.trans hc₂.symm)
      exact .ctor hls hps hfds hrecFds hη hs hc hls'₂
        (fun q => (hps' q).unopenStep hm (ihps q rfl hm) (by simpa using hps₂ q))
        (fun f => (hfds' f).unopenStep hm (ihfds f rfl hm) (by simpa using hfds₂ f))
        (fun r => (hrecFds' r).unopenStep hm (ihrecFds r rfl hm) (by simpa using hrecFds₂ r))
  | recr hls hps hms hmins his hη hs hls' hl hps' hms' hmins' his' hmaj ihps ihms ihmins ihis
      ihmaj =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | recr _ _ _ _ _ hη₂ hs₂ hls'₂ hl₂ hps₂ hms₂ hmins₂ his₂ hmaj₂ =>
      cases hη.symm.trans hη₂
      cases Fin.ext (hs.trans hs₂.symm)
      exact .recr hls hps hms hmins his hη hs hls'₂ hl₂
        (fun q => (hps' q).unopenStep hm (ihps q rfl hm) (by simpa using hps₂ q))
        (fun t => (hms' t).unopenStep hm (ihms t rfl hm) (by simpa using hms₂ t))
        (fun t c => (hmins' t c).unopenStep hm (ihmins t c rfl hm) (by simpa using hmins₂ t c))
        (fun i => (his' i).unopenStep hm (ihis i rfl hm) (by simpa using his₂ i))
        (hmaj.unopenStep hm (ihmaj rfl hm) hmaj₂)
  | quot hη hl hα hr ihα ihr =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | quot hη₂ hl₂ hα₂ hr₂ =>
      exact .quot hη₂ hl₂ (hα.unopenStep hm (ihα rfl hm) hα₂) (hr.unopenStep hm (ihr rfl hm) hr₂)
  | quotMk hη hl hα hr ha ihα ihr iha =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | quotMk hη₂ hl₂ hα₂ hr₂ ha₂ =>
      exact .quotMk hη₂ hl₂ (hα.unopenStep hm (ihα rfl hm) hα₂)
        (hr.unopenStep hm (ihr rfl hm) hr₂) (ha.unopenStep hm (iha rfl hm) ha₂)
  | quotLift hη hl₁ hl₂ hα hr hβ hf hh ha ihα ihr ihβ ihf ihh iha =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | quotLift hη₂ hl₁₂ hl₂₂ hα₂ hr₂ hβ₂ hf₂ hh₂ ha₂ =>
      exact .quotLift hη₂ hl₁₂ hl₂₂ (hα.unopenStep hm (ihα rfl hm) hα₂)
        (hr.unopenStep hm (ihr rfl hm) hr₂) (hβ.unopenStep hm (ihβ rfl hm) hβ₂)
        (hf.unopenStep hm (ihf rfl hm) hf₂) (hh.unopenStep hm (ihh rfl hm) hh₂)
        (ha.unopenStep hm (iha rfl hm) ha₂)
  | quotInd hη hl hα hr hβ hf ha ihα ihr ihβ ihf iha =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | quotInd hη₂ hl₂ hα₂ hr₂ hβ₂ hf₂ ha₂ =>
      exact .quotInd hη₂ hl₂ (hα.unopenStep hm (ihα rfl hm) hα₂)
        (hr.unopenStep hm (ihr rfl hm) hr₂) (hβ.unopenStep hm (ihβ rfl hm) hβ₂)
        (hf.unopenStep hm (ihf rfl hm) hf₂) (ha.unopenStep hm (iha rfl hm) ha₂)
  | proj hstruct hη hs hidx he ihe =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | proj hstruct₂ hη₂ hs₂ hidx₂ he₂ =>
      exact .proj hstruct₂ hη₂ hs₂ hidx₂ (he.unopenStep hm (ihe rfl hm) he₂)
  | app hf ha ihf iha =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | app hf₂ ha₂ =>
      exact .app (hf.unopenStep hm (ihf rfl hm) hf₂) (ha.unopenStep hm (iha rfl hm) ha₂)
  | lam ht hb iht ihb =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | lam ht₂ hb₂ =>
      exact .lam (ht.unopenStep hm (iht rfl hm) ht₂)
        (hb.unopenStep (by omega) (ihb rfl (by omega)) hb₂)
  | forallE ht hb iht ihb =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | forallE ht₂ hb₂ =>
      exact .forallE (ht.unopenStep hm (iht rfl hm) ht₂)
        (hb.unopenStep (by omega) (ihb rfl (by omega)) hb₂)
  | letE ht hv hb iht ihv ihb =>
    subst hk
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | letE ht₂ hv₂ hb₂ =>
      exact .letE (ht.unopenStep hm (iht rfl hm) ht₂) (hv.unopenStep hm (ihv rfl hm) hv₂)
        (hb.unopenStep (by omega) (ihb rfl (by omega)) hb₂)
  | natLit hNat =>
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | natLit hNat₂ => exact .natLit hNat₂
  | strLit hNat hList hChar hOfNat hString =>
    simp only [FExpr.instAtCore] at h'
    cases h' with
    | strLit hNat₂ hList₂ hChar₂ hOfNat₂ hString₂ =>
      exact .strLit hNat₂ hList₂ hChar₂ hOfNat₂ hString₂

theorem FExpr.Denotes.unopenBVars {m k base : Nat} {fe : FExpr} {e₀ e' : Expr E.1 ℓ m}
    (hm : base + k = m) :
    FExpr.Denotes L E k fe e₀ →
    FExpr.Denotes L E 0 (FExpr.openBVars base k fe) e' →
    FExpr.Denotes L E k fe e' := by
  intro h₀ h'
  induction k generalizing base fe with
  | zero => exact h'
  | succ k ih =>
    have h₁ := ih (base := base + 1) (by omega) (h₀.instFVarAt (p := base) (by omega)) h'
    exact h₀.unopenStep (by omega) (h₀.unopenCore rfl (by omega)) h₁

theorem FExpr.Denotes.unbind {m k : Nat} {fe : FExpr} {e : Expr E.1 ℓ m}
    (hk : k ≤ m) (hc : fe.data.looseBVarRange.toNat = 0) :
    FExpr.Denotes L E k fe e →
    FExpr.Denotes L E 0 fe e := by
  intro h
  induction k with
  | zero => exact h
  | succ k ih =>
    have h₁ := h.instFVarAt (p := m - k - 1) (by omega)
    rw [FExpr.instAt_of_closed _ k ⟨by omega, by rw [hc]; decide⟩] at h₁
    exact ih (by omega) h₁

theorem FExpr.Denotes.strengthenN {n k : Nat} {fe : FExpr} {e : Expr E.1 ℓ (n + k)}
    (hr : fe.fvarRange ≤ n) (hc : fe.data.looseBVarRange.toNat = 0) :
    FExpr.Denotes L E 0 fe e →
    ∃ e₀ : Expr E.1 ℓ n, FExpr.Denotes L E 0 fe e₀ := by
  intro h
  induction k with
  | zero => exact ⟨_, h⟩
  | succ k ih =>
    have ⟨_, h₀⟩ := h.strengthen (n := n + k) (by omega) hc
    exact ih h₀

end Metalean.FastChecker
