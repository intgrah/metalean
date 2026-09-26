/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Spec
public import Metalean.Checker.Acceleration.Operations

@[expose] public section

namespace Metalean.Checker.Fast

open Acceleration

open Frontend (Failure)

variable (F : FEnv)

structure NatOpSpec (nat pos : Nat) (f : Nat → Nat → Nat) : Prop where
  natSig : ∃ I : FInductive, F[nat]? = some (.inductive Nat.sig I)
  opDef : ∃ t v, F[pos]? = some (.def 0 t v)
  eq {ζ : Sigs} {E : Env ζ} {ηNat : Head ζ (.inductive Nat.sig)} {kind : ConstKind}
      {ηOp : Head ζ (.const kind 0)} :
    FEnv.Denotes F E →
    EnvWF E →
    ζ.lookup nat = some ⟨.inductive Nat.sig, ηNat⟩ →
    ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
    NatOpEq E ηNat ηOp f

structure BoolOpSpec (nat bool pos : Nat) (f : Nat → Nat → Bool) : Prop where
  natSig : ∃ I : FInductive, F[nat]? = some (.inductive Nat.sig I)
  boolSig : ∃ I : FInductive, F[bool]? = some (.inductive Bool.sig I)
  opDef : ∃ t v, F[pos]? = some (.def 0 t v)
  eq {ζ : Sigs} {E : Env ζ} {ηNat : Head ζ (.inductive Nat.sig)}
      {ηBool : Head ζ (.inductive Bool.sig)} {kind : ConstKind}
      {ηOp : Head ζ (.const kind 0)} :
    FEnv.Denotes F E →
    EnvWF E →
    ζ.lookup nat = some ⟨.inductive Nat.sig, ηNat⟩ →
    ζ.lookup bool = some ⟨.inductive Bool.sig, ηBool⟩ →
    ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
    BoolOpEq E ηNat ηBool ηOp f

structure NatOp (f : Nat → Nat → Nat) where
  nat : Nat
  pos : Nat
  spec : NatOpSpec F nat pos f

structure BoolOp (f : Nat → Nat → Bool) where
  nat : Nat
  bool : Nat
  pos : Nat
  spec : BoolOpSpec F nat bool pos f

recall Nat.add
recall Nat.sub
recall Nat.mul
recall Nat.pow
recall Nat.beq
recall Nat.ble
recall Nat.div
recall Nat.mod
recall Nat.gcd
recall Nat.land
recall Nat.lor
recall Nat.xor
recall Nat.shiftLeft
recall Nat.shiftRight

structure Accel where
  protected Nat_add? : Option (NatOp F Nat.add) := none
  protected Nat_sub? : Option (NatOp F Nat.sub) := none
  protected Nat_mul? : Option (NatOp F Nat.mul) := none
  protected Nat_pow? : Option (NatOp F Nat.pow) := none
  protected Nat_beq? : Option (BoolOp F Nat.beq) := none
  protected Nat_ble? : Option (BoolOp F Nat.ble) := none
  protected Nat_div? : Option (NatOp F Nat.div) := none
  protected Nat_mod? : Option (NatOp F Nat.mod) := none
  protected Nat_gcd? : Option (NatOp F Nat.gcd) := none
  protected Nat_land? : Option (NatOp F Nat.land) := none
  protected Nat_lor? : Option (NatOp F Nat.lor) := none
  protected Nat_xor? : Option (NatOp F Nat.xor) := none
  protected Nat_shiftLeft? : Option (NatOp F Nat.shiftLeft) := none
  protected Nat_shiftRight? : Option (NatOp F Nat.shiftRight) := none

variable {F} {ζ : Sigs} {ℓ : Nat}

theorem FExpr.Denotes.op₂_natLit_inv {E : Env ζ} {k n nat pos num₁ num₂ : Nat}
    {e : Expr ζ ℓ n} :
    FExpr.Denotes ⟨ζ, E⟩ k
      (.appList (.const pos #[]) [.natLit nat num₁, .natLit nat num₂]) e →
    ∃ (ηNat : Head ζ (.inductive Nat.sig)) (kind : ConstKind)
      (ηOp : Head ζ (.const kind 0)),
      ζ.lookup nat = some ⟨.inductive Nat.sig, ηNat⟩ ∧
      ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ ∧
      e = Expr.op₂ ηOp (Expr.natLit ηNat num₁) (Expr.natLit ηNat num₂)
  | .app (.app (.const rfl hηOp _) (.natLit hη)) (.natLit hη₂) => by
    cases Sigs.lookup_head_eq hη₂ hη
    exact ⟨_, _, _, hη, hηOp, congr(.appList (.const _ $(funext nofun)) [_, _])⟩

theorem RedSpec.natOp {G : FCtx} {nat pos : Nat} {f : Nat → Nat → Nat} (num₁ num₂ : Nat) :
    NatOpSpec F nat pos f →
    RedSpec F ℓ G (.appList (.const pos #[]) [.natLit nat num₁, .natLit nat num₂])
      (.natLit nat (f num₁ num₂)) := by
  intro h ζ E n Γ e₁ t hS hd he
  obtain ⟨_, _, _, hη, hηOp, rfl⟩ := hd.op₂_natLit_inv
  exact ⟨_, .natLit hη,
    Defeq.retype hS.wf hS.ctxWF (h.eq hS.env hS.wf hη hηOp _ num₁ num₂) he⟩

theorem RedSpec.boolOp {G : FCtx} {nat bool pos : Nat} {f : Nat → Nat → Bool} (num₁ num₂ : Nat) :
    BoolOpSpec F nat bool pos f →
    RedSpec F ℓ G (.appList (.const pos #[]) [.natLit nat num₁, .natLit nat num₂])
      (FExpr.boolLit bool (f num₁ num₂)) := by
  intro h ζ E n Γ e₁ t hS hd he
  obtain ⟨_, _, _, hη, hηOp, rfl⟩ := hd.op₂_natLit_inv
  have ⟨_, hbool⟩ := h.boolSig
  have ⟨_, hηBool, _⟩ := hS.env.inductive hbool
  exact ⟨_, FExpr.Denotes.boolLit hηBool _,
    Defeq.retype hS.wf hS.ctxWF (h.eq hS.env hS.wf hη hηBool hηOp _ num₁ num₂) he⟩

theorem RedSpec.zeroLit {G : FCtx} {p : Nat} {I : FInductive}
    (hfe : F[p]? = some (.inductive Nat.sig I)) :
    RedSpec F ℓ G (.ctor p 0 0 #[] #[] #[] #[]) (.natLit p 0) := by
  intro ζ E n Γ e₁ t hS hd he
  have ⟨ηNat, hη, _⟩ := hS.env.inductive hfe
  rw [hd.unique (FExpr.Denotes.zero hη) (.ctor (by simp) (by simp) (by simp))] at he ⊢
  exact ⟨_, .natLit hη, he⟩

theorem RedSpec.succLit {G : FCtx} {p : Nat} {I : FInductive}
    (hfe : F[p]? = some (.inductive Nat.sig I)) (num : Nat) :
    RedSpec F ℓ G (.ctor p 0 1 #[] #[] #[] #[.natLit p num]) (.natLit p (num + 1)) := by
  intro ζ E n Γ e₁ t hS hd he
  have ⟨ηNat, hη, _⟩ := hS.env.inductive hfe
  rw [hd.unique (FExpr.Denotes.succLit hη)
    (.ctor (by simp) (by simp) fun r hr => by
      obtain rfl : r = .natLit p num := by simpa using hr
      exact .natLit p num)] at he ⊢
  exact ⟨_, .natLit hη, he⟩

theorem RedSpec.succArg {G : FCtx} {p : Nat} {I : FInductive} {x y : FExpr}
    (hfe : F[p]? = some (.inductive Nat.sig I)) :
    RedSpec F ℓ G x y →
    RedSpec F ℓ G (.ctor p 0 1 #[] #[] #[] #[x])
      (.ctor p 0 1 #[] #[] #[] #[y]) := by
  intro h ζ E n Γ e₁ t hS hd he
  have ⟨ηNat, hη, _⟩ := hS.env.inductive hfe
  have .ctor (s' := s') (c' := c') (ls' := ls') (ps' := ps') (fds' := fds') (recFds' := recFds')
    _ _ _ _ hη₂ hs hc _ _ _ hrecFdsd := hd
  cases hη.symm.trans hη₂
  obtain rfl : s' = 0 := Fin.ext hs
  obtain rfl : c' = 1 := Fin.ext (by simpa using hc)
  have hls0 : (fun i => (⟦ls' i⟧ : Level ℓ)) = ![] := funext nofun
  have hps0 : ps' = ![] := funext nofun
  have hfds0 : fds' = ![] := funext nofun
  have hrec0 : recFds' = ![recFds' ⟨0, by decide⟩] := funext fun ⟨0, _⟩ => rfl
  have heq : (Expr.ctor ηNat 0 1 (⟦ls' ·⟧) ps' fds' recFds' : Expr ζ ℓ n) =
      Expr.succ ηNat (recFds' ⟨0, by decide⟩) := by
    rw [hls0, hps0, hfds0]
    exact congr(Expr.ctor ηNat 0 1 ![] ![] ![] $hrec0)
  rw [heq] at he ⊢
  have ⟨ps₁, fds₁, _, _, _, hrecTy, _⟩ := he.ctor_inv
  obtain rfl : ps₁ = ![] := funext nofun
  obtain rfl : fds₁ = ![] := funext nofun
  have hty : ∀ f : Fin (Nat.sig.ctors 0 1).nrecFields,
      ((((E.get ηNat).block.ctors 0 1).recursive f).instantiatedType ηNat ![] ![]
        (Fin.append ![] ![]) : Expr ζ ℓ n) = Expr.nat ηNat := fun ⟨0, _⟩ => by
    simp [RecField.instantiatedType, RecField.instantiatedTelescope, Matrix.empty_eq,
      Expr.nat]
  have hx : E[Γ] ⊢ recFds' ⟨0, by decide⟩ : Expr.nat ηNat := by
    have h₀ := (hrecTy ⟨0, by decide⟩).right
    rw [hty ⟨0, by decide⟩] at h₀
    exact h₀
  have ⟨_, hy', hc'⟩ := h hS (by simpa using hrecFdsd ⟨0, by decide⟩) hx
  exact ⟨_, FExpr.Denotes.succ hη hy',
    Defeq.retype hS.wf hS.ctxWF (Expr.succ_congr hc') he⟩

end Metalean.Checker.Fast
