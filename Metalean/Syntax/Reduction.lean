/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Env
public import Metalean.Syntax.Inductive.Iota
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

open Relation

variable {ζ : Sigs}

inductive Frame (ζ : Sigs) (ℓ n : Nat) where
  | app (a : Expr ζ ℓ n)
  | recr {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n)
  | quotLift (η : Head ζ .quot) (l₁ l₂ : Level ℓ) (α r β f h : Expr ζ ℓ n)
  | quotInd (η : Head ζ .quot) (l : Level ℓ) (α r β f : Expr ζ ℓ n)

def Frame.plug {ℓ n : Nat} (e : Expr ζ ℓ n) : Frame ζ ℓ n → Expr ζ ℓ n
  | .app a => .app e a
  | .recr η s ls l ps ms mins is => .recr η s ls l ps ms mins is e
  | .quotLift η l₁ l₂ α r β f h => .quotLift η l₁ l₂ α r β f h e
  | .quotInd η l α r β f => .quotInd η l α r β f e

set_option hygiene false in
notation:65 E " ⊢ " e₁ " ⤳ " e₂:lead => WHRed E e₁ e₂

judgement WHRed (E : Env ζ) {ℓ : Nat} :
    {n : Nat} → Expr ζ ℓ n → Expr ζ ℓ n → Prop where

  E ⊢ e₁ ⤳ e₂
  ──────────────────── frame {n} {e₁ e₂ : Expr ζ ℓ n} {K : Frame ζ ℓ n}
  E ⊢ K.plug e₁ ⤳ K.plug e₂

  ──────────────────── beta {n} {t a : Expr ζ ℓ n} {e' : Expr ζ ℓ (n + 1)}
  E ⊢ .app (.lam t e') a ⤳ e'.inst a

  ──────────────────── zeta {n} {t v : Expr ζ ℓ n} {e' : Expr ζ ℓ (n + 1)}
  E ⊢ .letE t v e' ⤳ e'.inst v

  ──────────────────── delta {n nlevels : Nat} {η : Head ζ (.const .def nlevels)} {ls}
  E ⊢ .const η (n := n) ls ⤳ (E.get η).defValue{ls}.wkClosed

  E ⊢ maj₁ ⤳ maj₂
  ──────────────────── recrMajor {n ι} {η : Head ζ (.inductive ι)}
    {s ls l ps ms mins is} {maj₁ maj₂ : Expr ζ ℓ n}
  E ⊢ .recr η s ls l ps ms mins is maj₁ ⤳ .recr η s ls l ps ms mins is maj₂

  ──────────────────── iota {n : Nat} {ι : IndSig}
    {η : Head ζ (.inductive ι)}
    {ls₁ ls₂ : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {ms : Fin ι.nsorts → Expr ζ ℓ n}
    {mins : (s : Fin ι.nsorts) →
      Fin (ι.nctors s) → Expr ζ ℓ n}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
  E ⊢ .recr η s ls₁ l ps₁ ms mins is (.ctor η s c ls₂ ps₂ fds recFds) ⤳
    (E.get η).block.iotaRhs η ls₁ l ps₁ ms mins s c fds recFds

  ──────────────────── quotIota {n : Nat} {η : Head ζ .quot}
    {l₁ l₁' l₂ : Level ℓ} {α α' r r' β f h a : Expr ζ ℓ n}
  E ⊢ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁' α' r' a) ⤳ f.app a

  ──────────────────── quotIndIota {n : Nat} {η : Head ζ .quot}
    {l l' : Level ℓ} {α α' r r' β f a : Expr ζ ℓ n}
  E ⊢ .quotInd η l α r β f (.quotMk η l' α' r' a) ⤳ f.app a

def WHRedS (E : Env ζ) {ℓ n : Nat} : Expr ζ ℓ n → Expr ζ ℓ n → Prop :=
  ReflTransGen (WHRed E)

notation:65 E " ⊢ " e₁ " ⤳* " e₂:lead => WHRedS E e₁ e₂

theorem WHRedS.frame {E : Env ζ} {ℓ n : Nat} {e₁ e₂ : Expr ζ ℓ n} (K : Frame ζ ℓ n) :
    E ⊢ e₁ ⤳* e₂ →
    E ⊢ K.plug e₁ ⤳* K.plug e₂ :=
  fun h => h.lift K.plug fun _ _ => .frame

end Metalean
