/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Inductive
public import Metalean.Semantics.Soundness.Context.Admissible
import Metalean.Semantics.Interpretation.Family.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}
  {ι : IndSig} {I : Inductive ζ ι} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
  {ctor : Ctor ζ ι s csig} {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {fds : Fin csig.nfields → Expr ζ ℓ Γ₁.as.len}

theorem SourceAdmissible.ordinaryPrefix {count : Nat} (hcount : count ≤ csig.nfields)
    (hctx : E[Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux count hcount)] ⊢ₛ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : I.paramType ls ps p)
    (hf : ∀ f, E[Γ₁.as.ctx] ⊢ₛ fds f : ctor.ordinaryFieldExpr ls ps fds f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (args : Fin count → RawValue Γ₂)
    (hadm : SourceAdmissible
      (σ₁ ≫ RawCtx.toCtx.map
        (⟨Fin.append ps fun f : Fin count => fds (f.castLE hcount),
          Ctor.ordinarySubstWFStrong hcount hps fun f => hf (f.castLE hcount)⟩ :
          Γ₁.as ⟶ (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux count hcount), hctx⟩ :
            CtxCat E ℓ).as)) (ρ.pushFin args))
    (i : Nat) (hi : i ≤ count)
    (hprefix : E[Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux i (hi.trans hcount))] ⊢ₛ ok) :
    SourceAdmissible
      (σ₁ ≫ RawCtx.toCtx.map
        (⟨Fin.append ps fun f : Fin i => fds (f.castLE (hi.trans hcount)),
          Ctor.ordinarySubstWFStrong (hi.trans hcount) hps
            fun f => hf (f.castLE (hi.trans hcount))⟩ :
          Γ₁.as ⟶ (⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux i (hi.trans hcount)),
            hprefix⟩ : CtxCat E ℓ).as))
      (ρ.pushFin fun f : Fin i => args (f.castLE hi)) := by
  induction count with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hi
    exact hadm
  | succ count ih =>
    by_cases heq : i = count + 1
    · subst i
      exact hadm
    have hi' : i ≤ count := by omega
    change E[(Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux count (by omega))).snoc
      ((ctor.ordinaryType ⟨count, by omega⟩).instL ls)] ⊢ₛ ok at hctx
    have .snoc hbase ⟨u, ht⟩ := hctx
    let Src : CtxCat E ℓ :=
      ⟨Ctx.instL ls (I.params ++ ctor.ordinaryTeleAux count (by omega)), hbase⟩
    let σ₂ : Γ₁.as ⟶ (CtxCat.extension Src ht).as :=
      ⟨Fin.append (m := ι.nparams) (n := count + 1) ps fun f : Fin (count + 1) => fds (f.castLE hcount),
        Ctor.ordinarySubstWFStrong hcount hps fun f => hf (f.castLE hcount)⟩
    let σ₂' : Γ₁.as ⟶ Src.as :=
      ⟨Fin.append ps fun f : Fin count => fds (f.castLE (by omega)),
        Ctor.ordinarySubstWFStrong (by omega) hps fun f => hf (f.castLE (by omega))⟩
    have hover : RawCtx.toCtx.map σ₂ ≫ CtxCat.rawProjection Src ht = RawCtx.toCtx.map σ₂' :=
      (RawCtx.toCtx.map_comp _ _).symm.trans (congrArg RawCtx.toCtx.map (RawCtx.Hom.ext (funext
        fun v => Fin.append_castLE_right ps (fun f => fds (f.castLE hcount)) (Nat.le_succ count) v)))
    have htail := SourceAdmissible.tail (Γ₁ := Src) ht hadm
    change SourceAdmissible ((σ₁ ≫ RawCtx.toCtx.map σ₂) ≫ CtxCat.rawProjection Src ht)
      (ρ.pushFin fun f : Fin count => args f.castSucc) at htail
    rw [Category.assoc, hover] at htail
    exact ih (by omega) hbase (fun f => args f.castSucc) htail hi' hprefix

end Metalean.CoherentShape
