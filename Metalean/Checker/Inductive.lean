/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Infer
public import Metalean.Syntax.Inductive.Pre
import Metalean.Strong.Env

@[expose] public section

namespace Metalean.Checker

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}

def checkTele (ho : E.Ordered) {P : Level ℓ → Prop} [DecidablePred P]
    (hΓ : E[Γ] ⊢ₛ ok) {m : Nat} :
    (Δ : Ctx ζ ℓ n m) → Except Failure (PLift (WFTeleStrong E P Γ Δ))
  | .nil => pure ⟨.nil⟩
  | .snoc Δ t => do
    let ⟨hΔ⟩ ← checkTele ho hΓ Δ
    let ⟨l, ht⟩ ← checkIsType ho (hΔ.appendCtxWFStrong hΓ) t
    let ⟨hP⟩ ← guardProofOr (P l) (.reject .fieldLevel)
    pure ⟨.snoc hΔ ⟨l, hP, ht⟩⟩

def checkCtx (ho : E.Ordered) (hΓ : E[Γ] ⊢ₛ ok) {m : Nat} (Δ : Ctx ζ ℓ n m) :
    Except Failure (PLift (E[Γ ++ Δ] ⊢ₛ ok)) := do
  let ⟨h⟩ ← checkTele (P := fun _ => True) ho hΓ Δ
  pure ⟨h.appendCtxWFStrong hΓ⟩

def checkIdx (ho : E.Ordered) (I : Inductive ζ ι) {m : Nat}
    {Δ : Ctx ζ ι.nlevels 0 m} (hΔ : E[Δ] ⊢ₛ ok) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ι.nlevels)
    (ps : Fin ι.nparams → Expr ζ ι.nlevels m)
    (is : Fin (ι.nindices s) → Expr ζ ι.nlevels m) :
    Except Failure (PLift (I.IdxWFStrong E Δ s ls ps is)) := do
  let ⟨h⟩ ← Fin.sequenceM fun index =>
    checkAgainst ho hΔ (is index) (I.indexType ls s ps is index)
  pure ⟨h⟩

def checkRecField (ho : E.Ordered) (I : Inductive ζ ι) {s : Fin ι.nsorts}
    {csig : CtorSig ι.nsorts} (ctor : Ctor ζ ι s csig)
    (hΓo : E[I.params ++ ctor.ordinaryTele] ⊢ₛ ok) (f : Fin csig.nrecFields) :
    Except Failure (PLift (RecField.WFStrong E I (I.params ++ ctor.ordinaryTele) (ctor.recursive f))) := do
  let fd := ctor.recursive f
  let ⟨htele⟩ ← checkTele (P := I.LevelOK) ho hΓo fd.tele
  let ⟨hΓt⟩ ← checkCtx ho hΓo fd.tele
  let ⟨hidx⟩ ← checkIdx ho I hΓt (csig.recursiveTarget f) Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))⟩) fd.indices
  pure ⟨htele, hidx⟩

def checkOrdField (ho : E.Ordered) (I : Inductive ζ ι) (hΓp : E[I.params] ⊢ₛ ok)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (f : Fin (ι.ctors s c).nfields)
    (hle : f.val ≤ (ι.ctors s c).nfields) :
    Except Failure (PLift (Field.WFStrong E I
      (I.params ++ (I.ctors s c).ordinaryTeleAux f.val hle)
      ((I.ctors s c).ordinary f))) := do
  let ⟨hΓf⟩ ← checkCtx ho hΓp ((I.ctors s c).ordinaryTeleAux f.val hle)
  let ⟨ht⟩ ← checkAgainst ho hΓf (((I.ctors s c).ordinary f).type)
    (.sort ((I.ctors s c).ordinary f).level)
  let ⟨hOK⟩ ← guardProofOr (I.LevelOK ((I.ctors s c).ordinary f).level) (.reject .fieldLevel)
  pure ⟨⟨ht, hOK⟩⟩

def checkCtorDecl (ho : E.Ordered) (I : Inductive ζ ι)
    (hΓp : E[I.params] ⊢ₛ ok) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Except Failure (PLift ((I.ctors s c).WFStrong E I)) := do
  let ⟨hord⟩ ← Fin.sequenceM fun f =>
    checkOrdField ho I hΓp f (Nat.le_of_lt f.isLt)
  let ⟨hΓo⟩ ← checkCtx ho hΓp (I.ctors s c).ordinaryTele
  let ⟨hrec⟩ ← Fin.sequenceM fun f => checkRecField ho I (I.ctors s c) hΓo f
  let ⟨hidx⟩ ← checkIdx ho I hΓo s Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le (Nat.le_add_right _ _)⟩)
    (I.ctors s c).targetIndices
  pure ⟨hord, hrec, hidx⟩

def checkInductive (ho : E.Ordered) (I : Inductive ζ ι) :
    Except Failure (PLift (Inductive.WFStrong E I)) := do
  let ⟨hparams⟩ ← checkTele (P := fun _ => True) ho (Γ := .nil)
    Tele.Forall.nil I.params
  have hΓp : E[I.params] ⊢ₛ ok := by
    simpa using hparams.appendCtxWFStrong .nil
  let ⟨hindices⟩ ← Fin.sequenceM fun s =>
    checkTele (P := fun _ => True) ho hΓp (I.indices s)
  let ⟨hctors⟩ ← Fin.sequenceM fun s =>
    Fin.sequenceM fun c => checkCtorDecl ho I hΓp s c
  pure ⟨hparams, hindices, hctors⟩

def checkInductiveEntry (ho : E.Ordered) (I : Inductive ζ ι) :
    Except Failure (PLift (Entry.WFStrong E (.inductive I))) := do
  let ⟨hwf⟩ ← checkInductive ho I
  pure ⟨.inductive hwf⟩

def inferOrdLevels (ho : E.Ordered) (pre : PreInductive ζ ι) :
    Except Failure ((s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Fin (ι.ctors s c).nfields → Level ι.nlevels) := do
  let ⟨hparams⟩ ← checkTele (P := fun _ => True) ho (Γ := .nil) Tele.Forall.nil pre.params
  have hΓp : E[pre.params] ⊢ₛ ok := by
    simpa using hparams.appendCtxWFStrong .nil
  Fin.mapM fun s => Fin.mapM fun c => Fin.mapM fun f => do
    let ⟨hΓf⟩ ← checkCtx ho hΓp ((pre.ctors s c).ordinaryTeleAux f.val (Nat.le_of_lt f.isLt))
    let ⟨l, _⟩ ← checkIsType ho hΓf ((pre.ctors s c).ordinary f)
    pure l

def checkPreInductive (ho : E.Ordered) (pre : PreInductive ζ ι) :
    Except Failure ((levels : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
        Fin (ι.ctors s c).nfields → Level ι.nlevels) ×'
      PLift (Entry.WFStrong E (.inductive (pre.withLevels levels)))) := do
  let levels ← inferOrdLevels ho pre
  let hwf ← checkInductiveEntry ho (pre.withLevels levels)
  pure ⟨levels, hwf⟩

end Metalean.Checker
