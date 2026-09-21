/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Telescope
public import Metalean.TypeTheory.Syntactic.Substitution
import Metalean.Strong.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory Limits TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ : RawCtx E ℓ}
  {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Γ.len (Γ.len + k)}

def RawCtx.Hom.liftTele {Γ₁ Γ₂ : RawCtx E ℓ} {Δ : Ctx ζ ℓ Γ₁.len (Γ₁.len + k)}
    (σ : Γ₂ ⟶ Γ₁) (hΔ : WFTeleStrong E P Γ₁.ctx Δ) :
    (⟨Γ₂.ctx ++ Ctx.substN σ.subst k Δ,
      (hΔ.substitution σ.typed).appendCtxWFStrong Γ₂.wf⟩ : RawCtx E ℓ) ⟶
      ⟨Γ₁.ctx ++ Δ, hΔ.appendCtxWFStrong Γ₁.wf⟩ where
  subst := σ.subst.liftN k
  typed := SubstWFStrong.liftN hΔ σ.typed

theorem Tm.map_liftTele_varLabel {Γ₁ Γ₂ : RawCtx E ℓ} {Δ : Ctx ζ ℓ Γ₁.len (Γ₁.len + k)}
    (σ : Γ₂ ⟶ Γ₁) (hΔ : WFTeleStrong E P Γ₁.ctx Δ)
    (f : Var k) :
    (Tm E ℓ).map (RawCtx.toCtx.map (σ.liftTele hΔ)).op
        (Tm.varLabel ⟨⟨Γ₁.ctx ++ Δ, hΔ.appendCtxWFStrong Γ₁.wf⟩⟩ (Fin.natAdd Γ₁.len f)) =
      Tm.varLabel ⟨⟨Γ₂.ctx ++ Ctx.substN σ.subst k Δ,
        (hΔ.substitution σ.typed).appendCtxWFStrong Γ₂.wf⟩⟩ (Fin.natAdd Γ₂.len f) :=
  Tm.label_eq_var _ (Subst.liftN_var σ.subst f)

def RawCtx.Hom.teleProjection {m : Nat} {Δ : Ctx ζ ℓ Γ.len m}
    (hΔ : WFTeleStrong E P Γ.ctx Δ) :
    (⟨Γ.ctx ++ Δ, hΔ.appendCtxWFStrong Γ.wf⟩ : RawCtx E ℓ) ⟶ Γ where
  subst v := .var (v.castLE Δ.le)
  typed v := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le Δ.le
    simpa! [Expr.wkN_eq_rename, Ren.wkN, Fin.castAdd] using (Γ.wf.var v).wkN

theorem Tm.map_teleProjection_varLabel (hΔ : WFTeleStrong E P Γ.ctx Δ) (v : Var Γ.len) :
    (Tm E ℓ).map (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op
        (Tm.varLabel ⟨Γ⟩ v) =
      Tm.varLabel ⟨⟨Γ.ctx ++ Δ, hΔ.appendCtxWFStrong Γ.wf⟩⟩ (v.castAdd k) :=
  Tm.label_eq_var ((RawCtx.Hom.teleProjection hΔ).typed v) rfl

theorem RawCtx.Hom.teleProjection_snoc {m : Nat} {Δ : Ctx ζ ℓ Γ.len m}
    (hΔ : WFTeleStrong E P Γ.ctx Δ)
    {t : Expr ζ ℓ m} {u : Level ℓ} (hu : P u)
    (ht : E[Γ.ctx ++ Δ] ⊢ₛ t : .sort u) :
    RawCtx.toCtx.map (teleProjection (hΔ.snoc ⟨u, hu, ht⟩)) =
      CtxCat.rawProjection ⟨⟨Γ.ctx ++ Δ, hΔ.appendCtxWFStrong Γ.wf⟩⟩ ht ≫
        RawCtx.toCtx.map (teleProjection hΔ) :=
  congrArg RawCtx.toCtx.map (RawCtx.Hom.ext rfl)

theorem RawCtx.Hom.liftTele_isPullback {Γ₁ Γ₂ : RawCtx E ℓ}
    {Δ : Ctx ζ ℓ Γ₁.len (Γ₁.len + k)} (σ : Γ₂ ⟶ Γ₁)
    (hΔ : WFTeleStrong E P Γ₁.ctx Δ) :
    IsPullback (RawCtx.toCtx.map (σ.liftTele hΔ))
      (RawCtx.toCtx.map (teleProjection (hΔ.substitution σ.typed)))
      (RawCtx.toCtx.map (teleProjection hΔ)) (RawCtx.toCtx.map σ) := by
  cases Γ₁ with
  | @mk n ctx wf =>
    let Γ₁ : RawCtx E ℓ := ⟨ctx, wf⟩
    induction Δ using Tele.addInduction with
    | nil =>
      change IsPullback (RawCtx.toCtx.map σ) (RawCtx.toCtx.map (𝟙 Γ₂))
        (RawCtx.toCtx.map (𝟙 Γ₁)) (RawCtx.toCtx.map σ)
      rw [RawCtx.toCtx.map_id, RawCtx.toCtx.map_id]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    | snoc k Δ A ih =>
      have ⟨u, hu, hA⟩ := hΔ.last
      have hmap : RawCtx.toCtx.map (σ.liftTele (k := k + 1) hΔ) =
          CtxCat.extensionMap hA (σ.liftTele hΔ.init) := rfl
      have hproj := RawCtx.Hom.teleProjection_snoc hΔ.init hu hA
      have hproj' := RawCtx.Hom.teleProjection_snoc (hΔ.init.substitution σ.typed) hu
        (hA.substitution (σ.liftTele hΔ.init).typed)
      erw [hmap, hproj, hproj']
      exact (CtxCat.extensionIsPullback hA (σ.liftTele hΔ.init)).paste_vert (ih hΔ.init)

theorem RawCtx.Hom.applyTele_typed {Γ₁ Γ₂ : RawCtx E ℓ}
    {Δ : Ctx ζ ℓ Γ₁.len (Γ₁.len + k)} (hΔ : WFTeleStrong E P Γ₁.ctx Δ)
    {σ₁ : Γ₂ ⟶ Γ₁}
    (σ₂ : Γ₂ ⟶ (⟨Γ₁.ctx ++ Δ, hΔ.appendCtxWFStrong Γ₁.wf⟩ : RawCtx E ℓ))
    (hover : σ₂ ≫ teleProjection hΔ = σ₁)
    {e : Expr ζ ℓ Γ₂.len} {body : Expr ζ ℓ (Γ₁.len + k)} {u : Level ℓ} :
    E[Γ₁.ctx ++ Δ] ⊢ₛ body : .sort u →
    E[Γ₂.ctx] ⊢ₛ e : (Δ.pi body).subst σ₁.subst →
    E[Γ₂.ctx] ⊢ₛ e.apps (fun i => σ₂.subst (Fin.natAdd Γ₁.len i)) : body.subst σ₂.subst := by
  intro hbody he
  induction Δ using Tele.addInduction generalizing u with
  | nil =>
    have hσ₂ : σ₂.subst = σ₁.subst := congrArg RawCtx.Hom.subst hover
    simpa [hσ₂] using he
  | snoc k Δ t ih =>
    have ⟨v, hv, ht⟩ := hΔ.last
    let C : CtxCat E ℓ := ⟨⟨Γ₁.ctx ++ Δ, hΔ.init.appendCtxWFStrong Γ₁.wf⟩⟩
    let σ₃ := σ₂ ≫ CtxCat.projectionRaw C ht
    have hoverInit : σ₃ ≫ teleProjection hΔ.init = σ₁ := by
      trans σ₂ ≫ teleProjection hΔ
      · apply RawCtx.Hom.ext
        rfl
      · exact hover
    have hfun := ih hΔ.init σ₃ hoverInit (.forallEDF ht hbody hbody) he
    have harg : E[Γ₂.ctx] ⊢ₛ σ₂.subst (Fin.last (Γ₁.len + k)) : t.subst σ₃.subst := by
      have hh := σ₂.typed (Fin.last (Γ₁.len + k))
      erw [Ctx.get_last, Expr.wk_subst] at hh
      exact hh
    have htσ := ht.substitution σ₃.typed
    have hbodyσ := hbody.substitution (σ₃.lift ⟨v, ht⟩).typed
    have happ := DefeqStrong.appDF htσ hbodyσ hfun harg (hbodyσ.inst_congr harg)
    have hσ₂ : σ₃.subst.extend (σ₂.subst (Fin.last (Γ₁.len + k))) = σ₂.subst :=
      Fin.snoc_init_self σ₂.subst
    change E[Γ₂.ctx] ⊢ₛ (e.apps fun i => σ₂.subst (Fin.natAdd Γ₁.len i.castSucc)).app
        (σ₂.subst (Fin.last (Γ₁.len + k))) :
      (body.subst σ₃.subst.lift).inst (σ₂.subst (Fin.last (Γ₁.len + k))) at happ
    rw [Expr.apps_last]
    simpa [Expr.inst_subst_lift, hσ₂] using happ

end Metalean
