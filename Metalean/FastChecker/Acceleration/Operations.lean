/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Spec
public import Metalean.FastChecker.LiteralTyping

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable {ζ : Sigs} (L : Literals) (F : FEnv) (ℓ : Nat)

structure NatOpSpec (pos : Nat) (f : Nat → Nat → Nat) : Prop where
  natBound : L.nat < F.size
  opBound : pos < F.size
  eq {ζ : Sigs} {E : Env ζ} {ℓ' n : Nat} {Γ : Ctx ζ ℓ' 0 n}
      {ηNat : Head ζ (.inductive Literals.Nat.sig)} {kind : ConstKind}
      {ηOp : Head ζ (.const kind 0)} (num₁ num₂ : Nat) :
    FEnv.Denotes L F E →
    E.Ordered →
    L.NatTrust E →
    ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
    ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
    E[Γ] ⊢ Literals.natOp₂ ηOp (Literals.natLit ηNat num₁) (Literals.natLit ηNat num₂) ≡
      Literals.natLit ηNat (f num₁ num₂) : Literals.natType ηNat

structure BoolOpSpec (pos : Nat) (f : Nat → Nat → Bool) : Prop where
  natBound : L.nat < F.size
  boolBound : L.bool < F.size
  boolSig : ∃ I : FInductive, F[L.bool]? = some (.inductive Literals.Bool.sig I)
  opBound : pos < F.size
  eq {ζ : Sigs} {E : Env ζ} {ℓ' n : Nat} {Γ : Ctx ζ ℓ' 0 n}
      {ηNat : Head ζ (.inductive Literals.Nat.sig)}
      {ηBool : Head ζ (.inductive Literals.Bool.sig)} {kind : ConstKind}
      {ηOp : Head ζ (.const kind 0)} (num₁ num₂ : Nat) :
    FEnv.Denotes L F E →
    E.Ordered →
    L.NatTrust E →
    ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
    ζ.lookup L.bool = some ⟨.inductive Literals.Bool.sig, ηBool⟩ →
    ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
    E[Γ] ⊢ Literals.natOp₂ ηOp (Literals.natLit ηNat num₁) (Literals.natLit ηNat num₂) ≡
      Literals.boolLit ηBool (f num₁ num₂) : Literals.boolType ηBool

structure Accel (L : Literals) (F : FEnv) where
  add : Option (PLift (NatOpSpec L F L.add (· + ·))) := none
  sub : Option (PLift (NatOpSpec L F L.sub (· - ·))) := none
  mul : Option (PLift (NatOpSpec L F L.mul (· * ·))) := none
  pow : Option (PLift (NatOpSpec L F L.pow (· ^ ·))) := none
  beq : Option (PLift (BoolOpSpec L F L.beq Nat.beq)) := none
  ble : Option (PLift (BoolOpSpec L F L.ble Nat.ble)) := none
  div : Option (PLift (NatOpSpec L F L.div (· / ·))) := none
  mod : Option (PLift (NatOpSpec L F L.mod (· % ·))) := none
  gcd : Option (PLift (NatOpSpec L F L.gcd Nat.gcd)) := none
  land : Option (PLift (NatOpSpec L F L.land (· &&& ·))) := none
  lor : Option (PLift (NatOpSpec L F L.lor (· ||| ·))) := none
  xor : Option (PLift (NatOpSpec L F L.xor (· ^^^ ·))) := none
  shiftLeft : Option (PLift (NatOpSpec L F L.shiftLeft (· <<< ·))) := none
  shiftRight : Option (PLift (NatOpSpec L F L.shiftRight (· >>> ·))) := none

variable {L F ℓ}

theorem NatOpSpec.ofAxiom {pos : Nat} {f : Nat → Nat → Nat} (hnat : L.nat < F.size)
    (hop : pos < F.size)
    (ax : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄, L.NatAxioms E → L.NatAxiom E pos f) :
    NatOpSpec L F pos f where
  natBound := hnat
  opBound := hop
  eq num₁ num₂ _ _ htr hη hηOp := ax (htr .refl) num₁ num₂ hη hηOp

theorem FExpr.Denotes.op₂_natLit_inv {E : Env ζ} {k n pos num₁ num₂ : Nat} {e : Expr ζ ℓ n} :
    FExpr.Denotes L ⟨ζ, E⟩ k (.app (.app (.const pos #[]) (.natLit num₁)) (.natLit num₂)) e →
    ∃ (ηNat : Head ζ (.inductive Literals.Nat.sig)) (kind : ConstKind)
      (ηOp : Head ζ (.const kind 0)),
      ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ ∧
      ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ ∧
      e = Literals.natOp₂ ηOp (Literals.natLit ηNat num₁) (Literals.natLit ηNat num₂)
  | .app (.app (.const (ls' := ls') rfl hηOp _) (.natLit hη)) (.natLit hη₂) => by
    cases Sigs.lookup_head_eq hη₂ hη
    exact ⟨_, _, _, hη, hηOp, congr(.app (.app (.const _ $(funext nofun)) _) _)⟩

theorem RedSpec.natOp₂ {G : FCtx} {pos : Nat} {f : Nat → Nat → Nat} (num₁ num₂ : Nat) :
    NatOpSpec L F pos f →
    RedSpec L F ℓ G (.app (.app (.const pos #[]) (.natLit num₁)) (.natLit num₂))
      (.natLit (f num₁ num₂)) := by
  intro h ζ E n Γ e₁ t hS hd he
  obtain ⟨_, _, _, hη, hηOp, rfl⟩ := hd.op₂_natLit_inv
  exact ⟨_, .natLit hη,
    Defeq.retype hS.ordered hS.wf (h.eq num₁ num₂ hS.env hS.ordered hS.trust hη hηOp) he⟩

theorem RedSpec.boolOp {G : FCtx} {pos : Nat} {f : Nat → Nat → Bool} (num₁ num₂ : Nat) :
    BoolOpSpec L F pos f →
    RedSpec L F ℓ G (.app (.app (.const pos #[]) (.natLit num₁)) (.natLit num₂))
      (FExpr.boolLit L (f num₁ num₂)) := by
  intro h ζ E n Γ e₁ t hS hd he
  obtain ⟨_, _, _, hη, hηOp, rfl⟩ := hd.op₂_natLit_inv
  have ⟨_, hbool⟩ := h.boolSig
  have ⟨_, hηBool, _⟩ := hS.env.inductive hbool
  exact ⟨_, FExpr.Denotes.boolLit hηBool _,
    Defeq.retype hS.ordered hS.wf (h.eq num₁ num₂ hS.env hS.ordered hS.trust hη hηBool hηOp) he⟩

theorem RedSpec.zeroLit {G : FCtx} {I : FInductive}
    (hfe : F[L.nat]? = some (.inductive Literals.Nat.sig I)) :
    RedSpec L F ℓ G (.ctor L.nat 0 0 #[] #[] #[] #[]) (.natLit 0) := by
  intro ζ E n Γ e₁ t hS hd he
  have ⟨ηNat, hη, _⟩ := hS.env.inductive hfe
  rw [hd.unique (FExpr.Denotes.zero hη) (.ctor (by simp) (by simp) (by simp))] at he ⊢
  exact ⟨_, .natLit hη, he⟩

theorem RedSpec.succLit {G : FCtx} {I : FInductive}
    (hfe : F[L.nat]? = some (.inductive Literals.Nat.sig I)) (num : Nat) :
    RedSpec L F ℓ G (.ctor L.nat 0 1 #[] #[] #[] #[.natLit num]) (.natLit (num + 1)) := by
  intro ζ E n Γ e₁ t hS hd he
  have ⟨ηNat, hη, _⟩ := hS.env.inductive hfe
  rw [hd.unique (FExpr.Denotes.succLit hη)
    (.ctor (by simp) (by simp) fun r hr => by
      obtain rfl : r = .natLit num := by simpa using hr
      exact .natLit num)] at he ⊢
  exact ⟨_, .natLit hη, he⟩

theorem RedSpec.succArg {G : FCtx} {I : FInductive} {x y : FExpr}
    (hfe : F[L.nat]? = some (.inductive Literals.Nat.sig I)) :
    RedSpec L F ℓ G x y →
    RedSpec L F ℓ G (.ctor L.nat 0 1 #[] #[] #[] #[x])
      (.ctor L.nat 0 1 #[] #[] #[] #[y]) := by
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
      Literals.natSucc ηNat (recFds' ⟨0, by decide⟩) := by
    rw [hls0, hps0, hfds0]
    exact congr(Expr.ctor ηNat 0 1 ![] ![] ![] $hrec0)
  rw [heq] at he ⊢
  have ⟨ps₁, fds₁, _, _, _, hrecTy, _⟩ := he.ctor_inv
  obtain rfl : ps₁ = ![] := funext nofun
  obtain rfl : fds₁ = ![] := funext nofun
  have hty : ∀ f : Fin (Literals.Nat.sig.ctors 0 1).nrecFields,
      ((((E.get ηNat).block.ctors 0 1).recursive f).instantiatedType ηNat ![] ![]
        (Fin.append ![] ![]) : Expr ζ ℓ n) = Literals.natType ηNat := fun ⟨0, _⟩ => by
    simp [RecField.instantiatedType, RecField.instantiatedTelescope, Matrix.empty_eq,
      Literals.natType]
  have hx : E[Γ] ⊢ recFds' ⟨0, by decide⟩ : Literals.natType ηNat := by
    have h₀ := (hrecTy ⟨0, by decide⟩).right
    rw [hty ⟨0, by decide⟩] at h₀
    exact h₀
  have ⟨_, hy', hc'⟩ := h hS (by simpa using hrecFdsd ⟨0, by decide⟩) hx
  exact ⟨_, FExpr.Denotes.succ hη hy',
    Defeq.retype hS.ordered hS.wf (Literals.natSuccDF hc') he⟩

end Metalean.FastChecker
