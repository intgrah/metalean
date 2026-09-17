/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Instantiate
public import Metalean.Metatheory.SubjectReduction
public import Metalean.Metatheory.Unique
public import Metalean.Strong.Inversion
public import Metalean.Strong.Strengthen
public import Metalean.Metatheory.Conversion
public import Metalean.Metatheory.Injectivity

@[expose] public section

namespace Metalean.FastChecker

variable {ζ : Sigs} {E : Env ζ} {L : Literals} {ℓ : Nat}

def SubstRel (E : Env ζ) {n m : Nat} (Δ : Ctx ζ ℓ 0 m) (σ₁ σ₂ : Subst ζ ℓ n m) : Prop :=
  ∀ v, σ₁ v = σ₂ v ∨ ∃ T, E[Δ] ⊢ₛ σ₁ v ≡ σ₂ v : T

theorem SubstRel.lift {n m : Nat} {Δ : Ctx ζ ℓ 0 m} {σ₁ σ₂ : Subst ζ ℓ n m}
    (A : Expr ζ ℓ m) :
    SubstRel E Δ σ₁ σ₂ →
    SubstRel E (Δ.snoc A) σ₁.lift σ₂.lift := by
  intro h v
  by_cases hv : v.val < n
  · obtain ⟨w, rfl⟩ : ∃ w : Var n, v = w.castSucc := ⟨⟨v.val, hv⟩, rfl⟩
    rw [Subst.lift_castSucc, Subst.lift_castSucc]
    rcases h w with heq | ⟨T, hT⟩
    · exact .inl (by rw [heq])
    · exact .inr ⟨_, hT.wk A⟩
  · obtain rfl : v = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    exact .inl (by rw [Subst.lift_last, Subst.lift_last])

theorem SubstRel.extend {n m : Nat} {Δ : Ctx ζ ℓ 0 m} {σ₁ σ₂ : Subst ζ ℓ n m}
    {v₁ v₂ T : Expr ζ ℓ m} :
    SubstRel E Δ σ₁ σ₂ →
    E[Δ] ⊢ₛ v₁ ≡ v₂ : T →
    SubstRel E Δ (σ₁.extend v₁) (σ₂.extend v₂) := by
  intro h hv v
  by_cases hlt : v.val < n
  · obtain ⟨w, rfl⟩ : ∃ w : Var n, v = w.castSucc := ⟨⟨v.val, hlt⟩, rfl⟩
    rw [Subst.extend_castSucc, Subst.extend_castSucc]
    exact h w
  · obtain rfl : v = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    rw [Subst.extend_last, Subst.extend_last]
    exact .inr ⟨_, hv⟩

theorem FExpr.Denotes.coherent {E : Σ ζ, Env ζ} (ho : E.2.Ordered) {k n : Nat} {fe : FExpr}
    {e₁ e₂ : Expr E.1 ℓ n} :
    FExpr.Denotes L E k fe e₁ →
    FExpr.Denotes L E k fe e₂ →
    ∀ {m : Nat} {Δ : Ctx E.1 ℓ 0 m} {σ₁ σ₂ : Subst E.1 ℓ n m} {t₁ t₂ : Expr E.1 ℓ m},
    E.2[Δ] ⊢ₛ ok →
    SubstRel E.2 Δ σ₁ σ₂ →
    E.2[Δ] ⊢ₛ e₁.subst σ₁ : t₁ →
    E.2[Δ] ⊢ₛ e₂.subst σ₂ : t₂ →
    E.2[Δ] ⊢ₛ e₁.subst σ₁ ≡ e₂.subst σ₂ : t₁ := by
  intro h₁ h₂
  induction h₁ with
  | @bvar n k i j hi hj =>
    cases h₂ with
    | @bvar _ _ i₂ _ hi₂ hj₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      obtain rfl : i = i₂ := by omega
      simp only [Expr.subst] at he₁ ⊢
      rcases hσ ⟨i, by omega⟩ with heq | ⟨_, hT⟩
      · rw [← heq]
        exact he₁
      · exact DefeqStrong.retype ho hΔ hT he₁
  | @fvar n k i hi =>
    cases h₂ with
    | fvar hi₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      simp only [Expr.subst] at he₁ ⊢
      rcases hσ ⟨i, by omega⟩ with heq | ⟨_, hT⟩
      · rw [← heq]
        exact he₁
      · exact DefeqStrong.retype ho hΔ hT he₁
  | sort hl =>
    cases h₂ with
    | sort hl₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      obtain rfl := hl.unique hl₂
      exact he₁
  | const hls hη hls' =>
    cases h₂ with
    | const _ hη₂ hls'₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
      exact he₁
  | proj hstruct hη hs hidx _ ihe =>
    cases h₂ with
    | proj hstruct₂ hη₂ hs₂ hidx₂ he₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := Fin.ext (hs.trans hs₂.symm)
      simp only [Inductive.IsStructure.projTerm_subst] at he₁ he₂ ⊢
      exact Inductive.IsStructure.projTerm_congr_defeq ho hstruct hstruct₂ _ _
        (hidx.trans hidx₂.symm) hΔ he₁ he₂ fun ht₁ ht₂ => ihe he₂d hΔ hσ ht₁ ht₂
  | app _ _ ihf iha =>
    cases h₂ with
    | app hf₂ ha₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, _, hf', ha', hty₁⟩ := he₁.app_inv (Or.inl rfl)
      have ⟨_, _, hg', hb', _⟩ := he₂.app_inv (Or.inl rfl)
      have hfg := ihf hf₂ hΔ hσ hf' hg'
      have hteq := DefeqStrong.uniqTy ho hΔ hfg.right hg'
      have ⟨hdom, _⟩ := IsTypeEq.forallE_inj ho hΔ hteq
      have hab := iha ha₂ hΔ hσ ha' (hdom.symm.convStrong hb')
      have ⟨_, hpi⟩ := hf'.regular
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hpi.forallE_inv (Or.inl rfl)
      exact hty₁.symm.convStrong (DefeqStrong.appDF ht ht' hfg hab (ht'.inst_congr hab))
  | lam _ _ iht ihb =>
    cases h₂ with
    | lam ht₂d hb₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, hb₁', hchain₁⟩ := he₁.lam_inv (Or.inl rfl) hΔ
      have ⟨_, hb₂', hchain₂⟩ := he₂.lam_inv (Or.inl rfl) hΔ
      have ⟨_, hpi₁⟩ := hchain₁.isType.2
      have ⟨_, hpi₂⟩ := hchain₂.isType.2
      have ht₁ := (hpi₁.forallE_inv (Or.inl rfl)).1
      have ht₂ := (hpi₂.forallE_inv (Or.inl rfl)).1
      have ⟨_, ht₁'⟩ := ht₁
      have ⟨_, ht₂'⟩ := ht₂
      have hd : E.2[Δ] ⊢ₛ _ ≡ _ typ := .ofDefEq (iht ht₂d hΔ hσ ht₁' ht₂')
      have hb₂'' := ((hd.symm.snocConv ho hΔ).mp hb₂'.defeq).toStrongOrdered ho (hΔ.snoc ht₁)
      have hb := ihb hb₂d (hΔ.snoc ht₁) (hσ.lift _) hb₁' hb₂''
      have ⟨_, hdl⟩ := hd.sort_uniq ho hΔ
      have ⟨_, htb⟩ := hb₁'.regular
      have htb₂ := ((hd.snocConv ho hΔ).mp htb.defeq).toStrongOrdered ho (hΔ.snoc ht₂)
      have hb₂ := ((hd.snocConv ho hΔ).mp hb.defeq).toStrongOrdered ho (hΔ.snoc ht₂)
      have hlam := DefeqStrong.lamDF hdl htb htb₂ hb hb₂
      exact hchain₁.symm.convStrong hlam
  | forallE _ _ iht ihb =>
    cases h₂ with
    | forallE ht₂d hb₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have hinv₁ := he₁.forallE_inv (Or.inl rfl)
      have hinv₂ := he₂.forallE_inv (Or.inl rfl)
      have ⟨_, ht₁'⟩ := hinv₁.1
      have ⟨_, ht₂'⟩ := hinv₂.1
      have hd : E.2[Δ] ⊢ₛ _ ≡ _ typ := .ofDefEq (iht ht₂d hΔ hσ ht₁' ht₂')
      have ⟨_, hc₁⟩ := hinv₁.2
      have ⟨_, hc₂⟩ := hinv₂.2
      have hc₂' := ((hd.symm.snocConv ho hΔ).mp hc₂.defeq).toStrongOrdered ho
        (hΔ.snoc hinv₁.1)
      have hcod : E.2[Δ.snoc _] ⊢ₛ _ ≡ _ typ :=
        .ofDefEq (ihb hb₂d (hΔ.snoc hinv₁.1) (hσ.lift _) hc₁ hc₂')
      have ⟨_, hpi⟩ := (hd.forallE_congr' ho hΔ hcod).sort_uniq ho hΔ
      exact DefeqStrong.retype ho hΔ hpi he₁
  | letE _ _ _ iht ihv ihb =>
    cases h₂ with
    | letE ht₂d hv₂d hb₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, ⟨_, hts₁⟩, hv₁, hbody₁, _⟩ := he₁.letE_inv (Or.inl rfl) hΔ
      have ⟨_, ⟨_, hts₂⟩, hv₂, hbody₂, _⟩ := he₂.letE_inv (Or.inl rfl) hΔ
      have hv := ihv hv₂d hΔ hσ hv₁ hv₂
      rw [Expr.inst_subst_lift] at hbody₁ hbody₂
      have hb := ihb hb₂d hΔ (hσ.extend hv) hbody₁ hbody₂
      have ⟨_, hr₁⟩ := hbody₁.regular
      have ⟨_, hr₂⟩ := hbody₂.regular
      have hz₁ := DefeqStrong.zeta hts₁ hv₁ hr₁ (Expr.inst_subst_lift _ _ _ ▸ hbody₁)
      have hz₂ := DefeqStrong.zeta hts₂ hv₂ hr₂ (Expr.inst_subst_lift _ _ _ ▸ hbody₂)
      rw [Expr.inst_subst_lift] at hz₁ hz₂
      have hchain := hz₁.trans (hb.trans (DefeqStrong.retype ho hΔ hz₂.symm hb.right))
      exact DefeqStrong.retype ho hΔ hchain he₁
  | natLit hNat =>
    cases h₂ with
    | natLit hNat₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hNat.symm.trans hNat₂
      simp only [Literals.subst_natLit] at he₁ ⊢
      exact he₁
  | strLit hNat hList hChar hOfNat hString =>
    cases h₂ with
    | strLit hNat₂ hList₂ hChar₂ hOfNat₂ hString₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hNat.symm.trans hNat₂
      cases hList.symm.trans hList₂
      cases hChar.symm.trans hChar₂
      cases hOfNat.symm.trans hOfNat₂
      cases hString.symm.trans hString₂
      simp only [Literals.subst_strLit] at he₁ ⊢
      exact he₁
  | ind hls hps his hη hs hls' _ _ ihps ihis =>
    cases h₂ with
    | ind _ _ _ hη₂ hs₂ hls'₂ hps₂d his₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := Fin.ext (hs.trans hs₂.symm)
      obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, _, hpsw₁, hisw₁, _⟩ := he₁.ind_inv (Or.inl rfl)
      have ⟨_, _, hpsw₂, hisw₂, _⟩ := he₂.ind_inv (Or.inl rfl)
      have hpsE p := (hpsw₁ p).trans
        (ihps p (hps₂d p) hΔ hσ (hpsw₁ p).right (hpsw₂ p).right)
      have hisE i := (hisw₁ i).trans
        (ihis i (his₂d i) hΔ hσ (hisw₁ i).right (hisw₂ i).right)
      exact DefeqStrong.retype ho hΔ
        ((DefeqStrong.indDF hpsw₁ hisw₁).symm.trans (.indDF hpsE hisE)) he₁
  | ctor hls hps hfds hrecFds hη hs hc hls' _ _ _ ihps ihfds ihrecFds =>
    cases h₂ with
    | ctor _ _ _ _ hη₂ hs₂ hc₂ hls'₂ hps₂d hfds₂d hrecFds₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := Fin.ext (hs.trans hs₂.symm)
      obtain rfl := Fin.ext (hc.trans hc₂.symm)
      obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
      simp only [Expr.subst] at he₁ he₂ ⊢
      have hB := (ho.entryWFStrong ‹Head E.1 (Sig.inductive _)›).block
      have ⟨_, _, _, hpsw₁, hfdsw₁, hrecFdsw₁, hindw₁, _⟩ := he₁.ctor_inv (Or.inl rfl)
      have ⟨_, _, _, hpsw₂, hfdsw₂, hrecFdsw₂, _, _⟩ := he₂.ctor_inv (Or.inl rfl)
      have hpsE p := (hpsw₁ p).trans
        (ihps p (hps₂d p) hΔ hσ (hpsw₁ p).right (hpsw₂ p).right)
      have hfdsE f := (hfdsw₁ f).trans
        (ihfds f (hfds₂d f) hΔ hσ (hfdsw₁ f).right (hfdsw₂ f).right)
      have hrecFdsE r := (hrecFdsw₁ r).trans
        (ihrecFds r (hrecFds₂d r) hΔ hσ (hrecFdsw₁ r).right (hrecFdsw₂ r).right)
      have hctor := hB.ctors ‹Fin _› ‹Fin (IndSig.nctors _ _)›
      have hleft := hindw₁.ctorDF hpsw₁ hfdsw₁ hrecFdsw₁
        (fun f => (hctor.ordinaryFieldExpr_congr hB.params f hpsw₁ hfdsw₁).choose_spec)
        (fun r => (hctor.recursiveFieldExpr_congr hB.params rfl r hpsw₁ hfdsw₁).choose_spec)
      have hright := (DefeqStrong.indDF hpsE fun i =>
        hctor.targetIndex_congr hB.params i hpsE hfdsE).ctorDF hpsE hfdsE hrecFdsE
        (fun f => (hctor.ordinaryFieldExpr_congr hB.params f hpsE hfdsE).choose_spec)
        (fun r => (hctor.recursiveFieldExpr_congr hB.params rfl r hpsE hfdsE).choose_spec)
      exact DefeqStrong.retype ho hΔ (hleft.symm.trans hright) he₁
  | recr hls hps hms hmins his hη hs hls' hl _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    cases h₂ with
    | recr _ _ _ _ _ hη₂ hs₂ hls'₂ hl₂ hps₂d hms₂d hmins₂d his₂d hmaj₂d =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := Fin.ext (hs.trans hs₂.symm)
      obtain rfl : _ = _ := funext fun i => (hls' i).unique (hls'₂ i)
      obtain rfl := hl.unique hl₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have hB := (ho.entryWFStrong ‹Head E.1 (Sig.inductive _)›).block
      have ⟨_, _, _, _, _, hallowed, hpsw₁, hmsw₁, hminsw₁, hisw₁, hmajw₁, hresw₁, _⟩ :=
        he₁.recr_inv (Or.inl rfl)
      have ⟨_, _, _, _, _, _, hpsw₂, hmsw₂, hminsw₂, hisw₂, hmajw₂, _, _⟩ :=
        he₂.recr_inv (Or.inl rfl)
      have hpsE p := (hpsw₁ p).trans
        (ihps p (hps₂d p) hΔ hσ (hpsw₁ p).right (hpsw₂ p).right)
      have hmsE t := (hmsw₁ t).trans
        (ihms t (hms₂d t) hΔ hσ (hmsw₁ t).right (hmsw₂ t).right)
      have hminsE t c := (hminsw₁ t c).trans
        (ihmins t c (hmins₂d t c) hΔ hσ (hminsw₁ t c).right (hminsw₂ t c).right)
      have hisE i := (hisw₁ i).trans
        (ihis i (his₂d i) hΔ hσ (hisw₁ i).right (hisw₂ i).right)
      have hmajE := hmajw₁.trans (ihmaj hmaj₂d hΔ hσ hmajw₁.right hmajw₂.right)
      have hleft := DefeqStrong.recrDF hallowed hpsw₁ hmsw₁ hminsw₁ hisw₁ hmajw₁ hresw₁
      have hright := DefeqStrong.recrDF hallowed hpsE hmsE hminsE hisE hmajE
        (hB.motiveResult_congr hΔ hpsE hmsE hisE hmajE)
      exact DefeqStrong.retype ho hΔ (hleft.symm.trans hright) he₁
  | quot hη hl _ _ ihα ihr =>
    cases h₂ with
    | quot hη₂ hl₂ hα₂ hr₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := hl.unique hl₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨hαt₁, hrt₁⟩ := he₁.quot_formation_inv (Or.inl rfl)
      have ⟨hαt₂, hrt₂⟩ := he₂.quot_formation_inv (Or.inl rfl)
      exact DefeqStrong.retype ho hΔ
        (.quotDF (ihα hα₂ hΔ hσ hαt₁ hαt₂) (ihr hr₂ hΔ hσ hrt₁ hrt₂)) he₁
  | quotMk hη hl _ _ _ ihα ihr iha =>
    cases h₂ with
    | quotMk hη₂ hl₂ hα₂ hr₂ ha₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := hl.unique hl₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, _, _, hαw₁, hrw₁, haw₁, _⟩ := he₁.quotMk_prem (Or.inl rfl)
      have ⟨_, _, _, hαw₂, hrw₂, haw₂, _⟩ := he₂.quotMk_prem (Or.inl rfl)
      have hleft := DefeqStrong.quotMkDF (η := ‹Head E.1 .quot›) hαw₁ hrw₁ haw₁
      have hright := DefeqStrong.quotMkDF (η := ‹Head E.1 .quot›)
        (hαw₁.trans (ihα hα₂ hΔ hσ hαw₁.right hαw₂.right))
        (hrw₁.trans (ihr hr₂ hΔ hσ hrw₁.right hrw₂.right))
        (haw₁.trans (iha ha₂ hΔ hσ haw₁.right haw₂.right))
      exact DefeqStrong.retype ho hΔ (hleft.symm.trans hright) he₁
  | quotLift hη hl₁ hl₂ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    cases h₂ with
    | quotLift hη₂ hl₁' hl₂' hα₂ hr₂ hβ₂ hf₂ hh₂ ha₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := hl₁.unique hl₁'
      obtain rfl := hl₂.unique hl₂'
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, _, _, _, _, _, hαw₁, hrw₁, hβw₁, hfw₁, hhw₁, haw₁, _⟩ :=
        he₁.quotLift_prem (Or.inl rfl)
      have ⟨_, _, _, _, _, _, hαw₂, hrw₂, hβw₂, hfw₂, hhw₂, haw₂, _⟩ :=
        he₂.quotLift_prem (Or.inl rfl)
      have hleft := DefeqStrong.quotLiftDF (η := ‹Head E.1 .quot›) hαw₁ hrw₁ hβw₁ hfw₁ hhw₁ haw₁
      have hright := DefeqStrong.quotLiftDF (η := ‹Head E.1 .quot›)
        (hαw₁.trans (ihα hα₂ hΔ hσ hαw₁.right hαw₂.right))
        (hrw₁.trans (ihr hr₂ hΔ hσ hrw₁.right hrw₂.right))
        (hβw₁.trans (ihβ hβ₂ hΔ hσ hβw₁.right hβw₂.right))
        (hfw₁.trans (ihf hf₂ hΔ hσ hfw₁.right hfw₂.right))
        (hhw₁.trans (ihh hh₂ hΔ hσ hhw₁.right hhw₂.right))
        (haw₁.trans (iha ha₂ hΔ hσ haw₁.right haw₂.right))
      exact DefeqStrong.retype ho hΔ (hleft.symm.trans hright) he₁
  | quotInd hη hl _ _ _ _ _ ihα ihr ihβ ihf iha =>
    cases h₂ with
    | quotInd hη₂ hl₂ hα₂ hr₂ hβ₂ hf₂ ha₂ =>
      intro m Δ σ₁ σ₂ t₁ t₂ hΔ hσ he₁ he₂
      cases hη.symm.trans hη₂
      obtain rfl := hl.unique hl₂
      simp only [Expr.subst] at he₁ he₂ ⊢
      have ⟨_, _, _, _, _, hαw₁, hrw₁, hβw₁, hfw₁, haw₁, hresw₁, _⟩ :=
        he₁.quotInd_prem (Or.inl rfl)
      have ⟨_, _, _, _, _, hαw₂, hrw₂, hβw₂, hfw₂, haw₂, _, _⟩ :=
        he₂.quotInd_prem (Or.inl rfl)
      have hleft := DefeqStrong.quotIndDF (η := ‹Head E.1 .quot›) hαw₁ hrw₁ hβw₁ hfw₁ haw₁ hresw₁
      have hβ' := hβw₁.trans (ihβ hβ₂ hΔ hσ hβw₁.right hβw₂.right)
      have ha' := haw₁.trans (iha ha₂ hΔ hσ haw₁.right haw₂.right)
      have ⟨_, hmotive⟩ := hβ'.regular
      have ⟨⟨_, hquot⟩, ⟨_, hprop⟩⟩ := hmotive.forallE_inv (Or.inl rfl)
      have hright := DefeqStrong.quotIndDF (η := ‹Head E.1 .quot›)
        (hαw₁.trans (ihα hα₂ hΔ hσ hαw₁.right hαw₂.right))
        (hrw₁.trans (ihr hr₂ hΔ hσ hrw₁.right hrw₂.right))
        hβ'
        (hfw₁.trans (ihf hf₂ hΔ hσ hfw₁.right hfw₂.right))
        ha'
        (.appDF hquot hprop hβ' ha' (hprop.inst_congr ha'))
      exact DefeqStrong.retype ho hΔ (hleft.symm.trans hright) he₁

theorem FExpr.Denotes.defeq {E : Σ ζ, Env ζ} (ho : E.2.Ordered) {k n : Nat} {fe : FExpr}
    {e₁ e₂ t₁ t₂ : Expr E.1 ℓ n} {Γ : Ctx E.1 ℓ 0 n} :
    E.2[Γ] ⊢ₛ ok →
    FExpr.Denotes L E k fe e₁ →
    FExpr.Denotes L E k fe e₂ →
    E.2[Γ] ⊢ₛ e₁ : t₁ →
    E.2[Γ] ⊢ₛ e₂ : t₂ →
    E.2[Γ] ⊢ₛ e₁ ≡ e₂ : t₁ := by
  intro hΓ h₁ h₂ he₁ he₂
  have h := h₁.coherent ho h₂ (σ₁ := Subst.id) (σ₂ := Subst.id) hΓ (fun _ => .inl rfl)
    (by simpa using he₁) (by simpa using he₂)
  simpa using h

end Metalean.FastChecker
