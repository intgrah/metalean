/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Slow.Infer
public import Metalean.Syntax.Inductive.Pre
import Metalean.Typing.Env

@[expose] public section

namespace Metalean.Checker.Slow

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}

def checkTele (hE : EnvWF E) {P : Level ℓ → Prop} [DecidablePred P]
    (hΓ : E[Γ] ⊢ ok) {m : Nat} :
    (Δ : Ctx ζ ℓ n m) → Except Failure (PLift (TeleWF E P Γ Δ))
  | .nil => pure ⟨.nil⟩
  | .snoc Δ t => do
    let ⟨hΔ⟩ ← checkTele hE hΓ Δ
    let ⟨l, ht⟩ ← checkIsType hE (hΔ.appendCtxWF hΓ) t
    let ⟨hP⟩ ← guardProofOr (P l) (.reject .fieldLevel)
    pure ⟨.snoc hΔ ⟨l, hP, ht⟩⟩

def checkCtx (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {m : Nat} (Δ : Ctx ζ ℓ n m) :
    Except Failure (PLift (E[Γ ++ Δ] ⊢ ok)) := do
  let ⟨h⟩ ← checkTele (P := fun _ => True) hE hΓ Δ
  pure ⟨h.appendCtxWF hΓ⟩

def checkIdx (hE : EnvWF E) (I : Inductive ζ ι) {m : Nat}
    {Δ : Ctx ζ ι.nlevels 0 m} (hΔ : E[Δ] ⊢ ok) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ι.nlevels)
    (ps : Fin ι.nparams → Expr ζ ι.nlevels m)
    (is : Fin (ι.nindices s) → Expr ζ ι.nlevels m) :
    Except Failure (PLift (I.IdxWF E Δ s ls ps is)) := do
  let ⟨h⟩ ← Fin.sequenceM fun index => do
    let ⟨l, ht⟩ ← checkIsType hE hΔ (I.indexType ls s ps is index)
    checkAgainst hE hΔ (is index) (I.indexType ls s ps is index) ⟨l, ht⟩
  pure ⟨h⟩

def checkRecField (hE : EnvWF E) (I : Inductive ζ ι) {s : Fin ι.nsorts}
    {csig : CtorSig ι.nsorts} (ctor : Ctor ζ ι s csig)
    (hΓo : E[I.params ++ ctor.ordinaryTele] ⊢ ok) (f : Fin csig.nrecFields) :
    Except Failure (PLift (RecFieldWF E I (I.params ++ ctor.ordinaryTele) (ctor.recursive f))) := do
  let fd := ctor.recursive f
  let ⟨htele⟩ ← checkTele (P := I.LevelOK) hE hΓo fd.tele
  let ⟨hΓt⟩ ← checkCtx hE hΓo fd.tele
  let ⟨hidx⟩ ← checkIdx hE I hΓt (csig.recursiveTarget f) Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))⟩) fd.indices
  pure ⟨htele, hidx⟩

def checkCtorDecl (hE : EnvWF E) (I : Inductive ζ ι)
    (hΓp : E[I.params] ⊢ ok) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hord : ∀ f, FieldWF E I (I.params ++ (I.ctors s c).ordinaryTeleAux f.val (by omega))
      ((I.ctors s c).ordinary f)) :
    Except Failure (PLift (CtorWF E I (I.ctors s c))) := do
  let ⟨hΓo⟩ ← checkCtx hE hΓp (I.ctors s c).ordinaryTele
  let ⟨hrec⟩ ← Fin.sequenceM fun f => checkRecField hE I (I.ctors s c) hΓo f
  let ⟨hidx⟩ ← checkIdx hE I hΓo s Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le (Nat.le_add_right _ _)⟩)
    (I.ctors s c).targetIndices
  pure ⟨hord, hrec, hidx⟩

def checkPreInductive (hE : EnvWF E) (pre : PreInductive ζ ι) :
    Except Failure ((levels : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
        Fin (ι.ctors s c).nfields → Level ι.nlevels) ×'
      PLift (EntryWF E (.inductive (pre.withLevels levels)))) := do
  let ⟨hparams⟩ ← checkTele (P := fun _ => True) hE (Γ := .nil) Tele.Forall.nil pre.params
  have hΓp : E[pre.params] ⊢ ok := by
    simpa using hparams.appendCtxWF .nil
  let ordinary ← Fin.mapM fun s => Fin.mapM fun c => Fin.mapM fun f => do
    let ⟨hΓf⟩ ← checkCtx hE hΓp ((pre.ctors s c).ordinaryTeleAux f.val (Nat.le_of_lt f.isLt))
    let ⟨l, ht⟩ ← checkIsType hE hΓf ((pre.ctors s c).ordinary f)
    let ⟨hOK⟩ ← guardProofOr (Level.imax l pre.level ≤ pre.level) (.reject .fieldLevel)
    pure (⟨l, ht, hOK⟩ : {l : Level ι.nlevels //
      (E[pre.params ++ (pre.ctors s c).ordinaryTeleAux f.val (Nat.le_of_lt f.isLt)] ⊢
        (pre.ctors s c).ordinary f : .sort l) ∧ Level.imax l pre.level ≤ pre.level})
  let I := pre.withLevels fun s c f => (ordinary s c f).1
  let ⟨hindices⟩ ← Fin.sequenceM fun s =>
    checkTele (P := fun _ => True) hE hΓp (I.indices s)
  let ⟨hctors⟩ ← Fin.sequenceM fun s => Fin.sequenceM fun c =>
    checkCtorDecl hE I hΓp s c fun f =>
      ⟨by simpa [I] using (ordinary s c f).2.1, (ordinary s c f).2.2⟩
  pure ⟨_, ⟨.inductive ⟨hparams, hindices, hctors⟩⟩⟩

end Metalean.Checker.Slow
