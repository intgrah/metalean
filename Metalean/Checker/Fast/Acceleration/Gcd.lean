/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.NatFix
import all Init.Data.Nat.Gcd

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace Gcd

structure Consts extends toNatFix : NatFix.Consts where
  protected Nat_gcd__unary : Nat
  protected Nat_mod_lt : Nat
  protected Nat_zero_lt_of_ne_zero : Nat

instance : CoeOut Consts NatFix.Consts := ⟨Consts.toNatFix⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure {
    toNatFix := ← NatFix.Consts.resolve t
    Nat_gcd__unary := ← t.const ``Nat.gcd._unary
    Nat_mod_lt := ← t.const ``Nat.mod_lt
    Nat_zero_lt_of_ne_zero := ← t.const ``Nat.zero_lt_of_ne_zero }

end Gcd

namespace FExpr

variable (C : Gcd.Consts)

@[fexpr_unfold]
protected def Nat.mod_lt (x y h : FExpr) : FExpr :=
  .appList (.const C.Nat_mod_lt #[]) [x, y, h]

@[fexpr_unfold]
protected def Nat.zero_lt_of_ne_zero (a h : FExpr) : FExpr :=
  .appList (.const C.Nat_zero_lt_of_ne_zero #[]) [a, h]

end FExpr

namespace Gcd

open NatFix (sig pair μ lt recTy app₃)

open scoped NatFix

variable (F : FEnv) (C : Consts)

/-- `Nat.mod_lt n (Nat.zero_lt_of_ne_zero h) : n % m < m` -/
@[fexpr_unfold]
def recLemma (m n h : FExpr) : FExpr :=
  FExpr.Nat.mod_lt C n m (FExpr.Nat.zero_lt_of_ne_zero C m h)

/-- `fun h => R ⟨n % m, m⟩ (recLemma m n h)` -/
@[fexpr_unfold]
def onFalse (mod : Nat) (m n R : Nat → FExpr) : FExpr :=
  .lam (FExpr.Not C (FExpr.Eq C (nat C.Nat_) (m 0) (.natLit C.Nat_ 0)))
    (.appList (R 1) [pair C (op₂ mod (n 1) (m 1)) (m 1), recLemma C (m 1) (n 1) (.bvar 0)])

/-- `if h : m = 0 then n else R ⟨n % m, m⟩ (recLemma m n h)` -/
@[fexpr_unfold]
def body (mod : Nat) (m n R : Nat → FExpr) : FExpr :=
  FExpr.dite C (nat C.Nat_) (FExpr.Eq C (nat C.Nat_) (m 0) (.natLit C.Nat_ 0))
    (FExpr.instDecidableEqNat C (m 0) (.natLit C.Nat_ 0))
    (.lam (FExpr.Eq C (nat C.Nat_) (m 0) (.natLit C.Nat_ 0)) (n 1))
    (onFalse C mod m n R)

@[fexpr_unfold]
def bodyLam (mod : Nat) : FExpr :=
  .lam (nat C.Nat_) (.lam (nat C.Nat_) (.lam (recTy C (pair C (.bvar 2) (.bvar 1)))
    (body C mod (fun d => .bvar (d + 2)) (fun d => .bvar (d + 1)) (fun d => .bvar d))))

def bodyBeta (mod : Nat) : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_) (R : recTy C (pair C m n)) ⊢
    app₃ (bodyLam C mod) m n R ≡ body C mod (fun _ => m) (fun _ => n) (fun _ => R) : nat C.Nat_

def onFalseType (mod : Nat) : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_) (R : recTy C (pair C m n)) ⊢
    onFalse C mod (fun _ => m) (fun _ => n) (fun _ => R) :
    FExpr.Not C (FExpr.Eq C (nat C.Nat_) m (.natLit C.Nat_ 0)) ⟶ nat C.Nat_

def onFalseBeta (mod : Nat) : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_) (R : recTy C (pair C m n))
      (h : FExpr.Not C (FExpr.Eq C (nat C.Nat_) m (.natLit C.Nat_ 0))) ⊢
    .app (onFalse C mod (fun _ => m) (fun _ => n) (fun _ => R)) h ≡
      .appList R [pair C (op₂ mod n m) m, recLemma C m n h] :
    nat C.Nat_

def recLemmaType (mod : Nat) : Schema :=
  schema% (m : nat C.Nat_) (n : nat C.Nat_)
      (h : FExpr.Not C (FExpr.Eq C (nat C.Nat_) m (.natLit C.Nat_ 0))) ⊢
    recLemma C m n h : lt C (μ C (pair C (op₂ mod n m) m)) (μ C (pair C m n))

structure Spec (pos mod : Nat) (G : FExpr) : Prop where
  fix : NatFix.FixSpec F C pos G (bodyLam C mod)
  bodyBeta : (bodyBeta C mod).Spec F
  onFalseType : (onFalseType C mod).Spec F
  onFalseBeta : (onFalseBeta C mod).Spec F
  recLemmaType : (recLemmaType C mod).Spec F

/-- The functional `G` of `Nat.gcd._unary = WellFounded.Nat.fix h G` -/
def functional : Except Failure FExpr :=
  match F[C.Nat_gcd__unary]? with
  | some (.def 0 _ (.appList (.const _ _) [_, _, _, G])) => pure G
  | _ => throw .internal

variable (hints : PArray Export.Hints)

def check (pos mod : Nat) : EIO Failure ((G : FExpr) × PLift (Spec F C pos mod G)) := do
  let G ← functional F C
  let ⟨fix⟩ ← NatFix.checkFix F C hints pos G (bodyLam C mod)
  let ⟨bodyBeta⟩ ← (bodyBeta C mod).check F hints
  let ⟨onFalseType⟩ ← (onFalseType C mod).check F hints
  let ⟨onFalseBeta⟩ ← (onFalseBeta C mod).check F hints
  let ⟨recLemmaType⟩ ← (recLemmaType C mod).check F hints
  pure ⟨G, ⟨⟨fix, bodyBeta, onFalseType, onFalseBeta, recLemmaType⟩⟩⟩

section

variable {F C} {pos mod beq : Nat} {G : FExpr} (h : Spec F C pos mod G)
  (hfix : NatFix.Spec F C beq) {ζ : Sigs} {E : Env ζ} (hF : FEnv.Denotes F E)
  (hE : EnvWF E) (hn : NatSpec F C.Nat_) (hd : Decide.DecEqNat F C)
  (hmod : NatOpSpec F C.Nat_ mod Nat.mod)

include h hfix hF hE hn hd hmod in
theorem Spec.bodyEval : NatFix.BodyEval C E (bodyLam C mod) Nat.gcd := by
  intro a b R hr hrec
  have ha := FEq.natLit hF hn a
  have hb := FEq.natLit hF hn b
  have hz := FEq.natLit hF hn 0
  schema_have c₁ := h.bodyBeta Gcd.bodyBeta #[.natLit C.Nat_ a, .natLit C.Nat_ b, R] #[.natLit C.Nat_ a, .natLit C.Nat_ b, R]
    using ha, hb, hr
  schema_have heq := hfix.eqNatType NatFix.eqNatType #[.natLit C.Nat_ a, .natLit C.Nat_ 0]
    #[.natLit C.Nat_ a, .natLit C.Nat_ 0] using ha, hz
  schema_have ht := hfix.constLamType NatFix.constLamType
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ 0), .natLit C.Nat_ b]
    #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ a) (.natLit C.Nat_ 0), .natLit C.Nat_ b] using heq, hb
  schema_have he := h.onFalseType Gcd.onFalseType #[.natLit C.Nat_ a, .natLit C.Nat_ b, R]
    #[.natLit C.Nat_ a, .natLit C.Nat_ b, R] using ha, hb, hr
  have ⟨p, hp, c₂⟩ := hd a 0 hF hE ht he
  by_cases ha₀ : a = 0
  · subst ha₀
    simp only [beq_self_eq_true, Bool.cond_true] at hp c₂
    schema_have c₃ := hfix.constBeta NatFix.constBeta
      #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ 0) (.natLit C.Nat_ 0), .natLit C.Nat_ b, p]
      #[FExpr.Eq C (nat C.Nat_) (.natLit C.Nat_ 0) (.natLit C.Nat_ 0), .natLit C.Nat_ b, p] using heq, hb, hp
    rw [Nat.gcd_zero_left]
    exact c₁.trans (c₂.trans c₃)
  · rw [beq_eq_false_iff_ne.mpr ha₀, Bool.cond_false] at hp c₂
    schema_have c₃ := h.onFalseBeta Gcd.onFalseBeta #[.natLit C.Nat_ a, .natLit C.Nat_ b, R, p]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b, R, p] using ha, hb, hr, hp
    schema_have hy := hfix.pairCongr NatFix.pairCongr
      #[op₂ mod (.natLit C.Nat_ b) (.natLit C.Nat_ a), .natLit C.Nat_ a] #[.natLit C.Nat_ (b % a), .natLit C.Nat_ a]
      using FEq.natOp hF hE hn hmod b a, ha
    schema_have hq := h.recLemmaType Gcd.recLemmaType #[.natLit C.Nat_ a, .natLit C.Nat_ b, p]
      #[.natLit C.Nat_ a, .natLit C.Nat_ b, p] using ha, hb, hp
    rw [Nat.gcd_rec]
    exact c₁.trans (c₂.trans (c₃.trans (hrec (Nat.mod_lt b (Nat.pos_of_ne_zero ha₀)) hy hq)))

end

def verify (hd : Decide.DecEqNat F C) (hdb : Decide.DecEqBool F C) (pos : Nat)
    (beq : BoolOp F Nat.beq) (mod : NatOp F Nat.mod) :
    EIO Failure (NatOp F Nat.gcd) := do
  let ⟨hn⟩ ← natAt F C.Nat_
  let ⟨hbeq⟩ ← beq.at F C.Nat_ C.Bool_
  let ⟨hmod⟩ ← mod.at F C.Nat_
  let ⟨hop⟩ ← constDef F pos
  let ⟨hf⟩ ← Fuel.check F C hints
  let ⟨hfix⟩ ← NatFix.check F C hints beq.pos
  let ⟨_, ⟨h⟩⟩ ← check F C hints pos mod.pos
  pure ⟨C.Nat_, pos, NatOpSpec.ofFEq hn hop fun _ _ hF hE =>
    hfix.fixEval hF hE hn hf hdb hbeq h.fix (h.bodyEval hfix hF hE hn hd hmod)⟩

end Gcd

end Metalean.Checker.Fast
