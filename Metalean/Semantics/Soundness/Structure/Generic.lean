module

public import Metalean.Semantics.Soundness.Rules.Inductive
import Metalean.Strong.Structure
import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
  {ι : IndSig} {η : Head ζ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ : CtxCat E ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len}

theorem RawJudgment.structure_generic
    (hs : (E.get η).block.IsStructure s c)
    (hps : ∀ p, E[Γ.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pt : RawInterpretationProperties Γ (.ind η s ls ps hs.indices)) :
    RawJudgment (Γ.extension (hs.indTypeStrong hps))
      (.var (Fin.last Γ.as.len)) (.var (Fin.last Γ.as.len))
      (.ind η s ls (fun p => (ps p).wk) hs.indices) := by
  have ht := hs.indTypeStrong hps
  let G := Γ.extension ht
  have hidx : (fun i => (hs.indices i : Expr ζ ℓ Γ.as.len).wk) = hs.indices :=
    funext hs.no_indices.elim
  have hw : (Expr.ind η s ls ps hs.indices).wk =
      .ind η s ls (fun p => (ps p).wk) hs.indices := by
    change Expr.ind η s ls (fun p => (ps p).wk)
      (fun i => (hs.indices i : Expr ζ ℓ Γ.as.len).wk) = _
    rw [hidx]
  have hv : E[G.as.ctx] ⊢ₛ .var (Fin.last Γ.as.len) : (Expr.ind η s ls ps hs.indices).wk :=
    G.as.wf.varLast
  have pv := RawInterpretationProperties.var G (Fin.last Γ.as.len)
  rw [← hw]
  exact {
    syntactic := hv
    type := pt.wk ht
    left := pv
    right := pv
    equal := HasEquality.refl G _
    fixed := HasFixedness.varLast ht pt.subst }

theorem RawJudgment.wkN {k : Nat} {P : Level ℓ → Prop} {e₁ e₂ t : Expr ζ ℓ Γ.as.len}
    (Δ : Ctx ζ ℓ Γ.as.len (Γ.as.len + k)) (hΔ : WFTeleStrong E P Γ.as.ctx Δ)
    (p : RawJudgment Γ e₁ e₂ t) :
    RawJudgment (CtxCat.extendTele Γ Δ hΔ) (e₁.wkN k) (e₂.wkN k) (t.wkN k) where
  syntactic := p.syntactic.wkN
  type := p.type.wkN Δ hΔ
  left := p.left.wkN Δ hΔ
  right := p.right.wkN Δ hΔ
  equal _ σ ρ hρ := by
    rw [p.left.wkN_value hΔ σ ρ hρ, p.right.wkN_value hΔ σ ρ hρ]
    exact p.equal _ _ (by simpa using hρ.tailTele hΔ)
  fixed := HasFixedness.wkN Δ hΔ p.syntactic.left p.type p.left p.fixed

theorem RawJudgment.wk {e₁ e₂ t A : Expr ζ ℓ Γ.as.len} {u : Level ℓ}
    (hA : E[Γ.as.ctx] ⊢ₛ A : .sort u) (p : RawJudgment Γ e₁ e₂ t) :
    RawJudgment (Γ.extension hA) e₁.wk e₂.wk t.wk :=
  p.wkN (P := fun _ => True) ((#t[] : Ctx ζ ℓ Γ.as.len Γ.as.len).snoc A) (.snoc .nil ⟨u, trivial, hA⟩)

theorem RawJudgment.paramType_wk {A : Expr ζ ℓ Γ.as.len} {u : Level ℓ}
    (pps : ∀ p, RawJudgment Γ (ps p) (ps p) ((E.get η).block.paramType ls ps p))
    (hA : E[Γ.as.ctx] ⊢ₛ A : .sort u) (p : Fin ι.nparams) :
    RawJudgment (Γ.extension hA) (ps p).wk (ps p).wk
      ((E.get η).block.paramType ls (fun p => (ps p).wk) p) := by
  have q := (pps p).wk hA
  simp only [Expr.wk, Inductive.paramType_wkFrom] at q ⊢
  exact q

end Metalean.CoherentShape
