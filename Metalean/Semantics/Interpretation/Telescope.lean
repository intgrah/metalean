/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory IndSig

variable {ζ : Sigs} {E : Env ζ} {ℓ b m : Nat} {P : Level ℓ → Prop}

theorem rawInterpret_ctxLam (D : CodeAssignment E ℓ) {Γ : CtxCat E ℓ}
    (Δ : Ctx ζ ℓ Γ.as.len m) (hΔ : WFTeleStrong E P Γ.as.ctx Δ) (hb : Δ.headRank < b)
    (body : Expr ζ ℓ m) :
    rawInterpret D Γ (Ctx.lam body Δ) =
      RawFamily.ctxLam D (fun Γ e _ => rawInterpret D Γ e) Γ Δ hΔ hb
        (rawInterpret D (CtxCat.extendTele Γ Δ hΔ) body) := by
  induction Δ with
  | nil => rfl
  | snoc Δ t ih =>
    exact (ih hΔ.init (lt_of_le_of_lt (le_max_left _ _) hb) (.lam t body)).trans
      (congrArg (RawFamily.ctxLam D _ Γ Δ hΔ.init _) (rawInterpret_lam D hΔ.last.choose_spec.2))

variable {ι : IndSig} {η : Head ζ (.inductive ι)} {l : Level ℓ}

theorem recursor_unfold (D : CodeAssignment E ℓ) (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ)
    (s : Fin ι.nsorts) :
    recursor D hd ls s =
      RawFamily.ctxLam D (fun Γ e _ => rawInterpret D Γ e) (CtxCat.nil E ℓ) _ hd.block.recrTele
        (recrTele_headRank_lt η ls s)
        (recursorBody D (fun Γ e _ => rawInterpret D Γ e) hd ls (recursor D hd ls) s) :=
  congrFun (recursorWith_unfold D _ hd ls).symm s

theorem recursorHyp_eq (D : CodeAssignment E ℓ) (hd : RecDecl E η l) (hrel : l.rel = true)
    (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) :
    recursorHyp D (fun Γ e _ => rawInterpret D Γ e) hd ls (recursor D hd ls) s c f =
      RawFamily.ctxLam D (fun Γ e _ => rawInterpret D Γ e) (CtxCat.recr hd ls s) _
        (((RecTyping.generic hd ls s).block.ctors s c).fieldTele rfl
          (CtxCat.recr hd ls s).as.wf (RecTyping.generic hd ls s).param)
        (fieldTele_headRank_lt (CtxCat.recr hd ls s) (fun p => .var (RecrBinder.param p).resolve)
          (fun _ => Expr.headRank_var_le _) s c)
        (rawInterpret D (CtxCat.ctorFields (RecTyping.generic hd ls s).toIndData s c)
          ((CtorInstance.generic (RecTyping.generic hd ls s).toIndData s c).ih l
            (fun t => ((Expr.var (RecrBinder.motive t).resolve).wkN (ι.ctors s c).nfields).wkN
              (ι.ctors s c).nrecFields)
            (fun t c₁ => ((Expr.var (RecrBinder.case t c₁).resolve).wkN (ι.ctors s c).nfields).wkN
              (ι.ctors s c).nrecFields) f)) := by
  rw [CtorInstance.generic_ih_eq_lam, rawInterpret_ctxLam D _ (fieldTelescopeStrong _ s c f)
      (fieldTelescope_headRank_lt _ (fun _ => Expr.headRank_var_le _) s c f),
    rawInterpret_recr D ((RecTyping.generic hd ls s).toRecData.ihTyping s c f) hrel]
  rfl

end Metalean.CoherentShape
