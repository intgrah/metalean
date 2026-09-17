/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Defs
public import Metalean.Syntax.Reduction
public import Metalean.Syntax.Structure
import Metalean.Strong
import Metalean.Strong.Substitution
import Metalean.Syntax.Substitution
import Metalean.Metatheory.Unique

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {e₁ e₂ v t t₁ t₂ : Expr ζ ℓ n} {e' : Expr ζ ℓ (n + 1)}

local notation:65 E "[" Γ "]" " ⊢ₛ " e₁:51 " : " t:51 " ⤳ " e₂:lead =>
  E[Γ] ⊢ₛ e₁ : t → E[Γ] ⊢ₛ e₁ ≡ e₂ : t

theorem DefeqStrong.retype (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁ →
    E[Γ] ⊢ₛ e₁ : t₂ →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t₂ := by
  intro hΓ h ht₂
  have ⟨_, ht⟩ := (DefeqStrong.uniqTy ho hΓ h.left ht₂).sort_uniq ho hΓ
  exact ht.defeqDF h

theorem WHRed.beta_defeq (ho : E.Ordered) {t e : Expr ζ ℓ n}
    {e' : Expr ζ ℓ (n + 1)} {t₁ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .app (.lam t e') e : t₁ ⤳ e'.inst e := by
  intro hΓ hty
  have ⟨_, _, hf, he, _⟩ := DefeqStrong.app_inv (Or.inl rfl) hty
  have ⟨_, he', hπ⟩ := DefeqStrong.lam_inv (Or.inl rfl) hf hΓ
  have ⟨_, hπTy⟩ := hπ.isType.2
  have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ :=
    DefeqStrong.forallE_inv (Or.inl rfl) hπTy
  have het := (hπ.forallE_inj ho hΓ).1.convStrong he
  exact DefeqStrong.retype ho hΓ (.beta ht ht' he' het (ht'.inst_congr het)
    (he'.inst_congr het)) hty

theorem WHRed.zeta_defeq (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .letE t v e' : t₁ ⤳ e'.inst v := by
  intro hΓ hty
  have ⟨_, ⟨_, ht⟩, hv, he', _⟩ := DefeqStrong.letE_inv (Or.inl rfl) hty hΓ
  have ⟨_, ht'⟩ := he'.regular
  exact DefeqStrong.retype ho hΓ
    (.zeta ht hv ht' he') hty

theorem WHRed.delta_defeq (ho : E.Ordered)
    {nlevels : Nat} {η : Head ζ (.const .def nlevels)}
    {ls : Fin nlevels → Level ℓ} {t : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ .const η ls : t ⤳ ((E.get η).defValue.instL ls).wkClosed := by
  intro hty
  have ⟨u, htype⟩ := (ho.entryWFStrong η).constType (Γ := Γ) ls
  exact (hty.const_inv (Or.inl rfl)).symm.convStrong
    (.delta htype ((ho.entryWFStrong η).defValue ls))

theorem WHRed.quotIota_defeq (ho : E.Ordered)
    {η : Head ζ .quot} {l₁ lq l₂ : Level ℓ}
    {α αq r rq β f h a : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .quotLift η l₁ l₂ α r β f h (.quotMk η lq αq rq a) : t ⤳ .app f a := by
  intro hΓ hty
  have ⟨α', r', β', f', h', maj, hα, hr, hβ, hf, hh, hmaj, ht⟩ :=
    DefeqStrong.quotLift_prem (Or.inl rfl) hty
  have ⟨_, _, a', _, _, ha, hquot⟩ :=
    DefeqStrong.quotMk_prem (Or.inr rfl) hmaj
  have hαeq := (hquot.quot_inj ho hΓ).2.1
  have ha' : E[Γ] ⊢ₛ a' ≡ a : α' := hαeq.symm.convStrong ha
  have haa := ha'.right
  have hαrefl := hα.left
  have hrrefl := hr.left
  have hβrefl := hβ.left
  have hfrefl := hf.left
  have hhrefl := hh.left
  obtain ⟨rfl, hαq, hrq⟩ := (hmaj.quotMk_inv (Or.inr rfl)).quot_inj ho hΓ
  have ⟨_, hαq⟩ := hαq.sort_uniq ho hΓ
  have hαq := DefeqStrong.retype ho hΓ hαq hαrefl
  have hmk : E[Γ] ⊢ₛ .quotMk η l₁ α' r' a ≡
      .quotMk η l₁ αq rq a : .quot η l₁ α' r' :=
    .quotMkDF hαq hrq haa
  have hmaj' := hmaj.trans hmk.symm
  have htoRedex : E[Γ] ⊢ₛ .quotLift η l₁ l₂ α' r' β' f' h' maj ≡
      .quotLift η l₁ l₂ α' r' β' f' h' (.quotMk η l₁ α' r' a) : β' :=
    .quotLiftDF hαrefl hrrefl hβrefl hfrefl hhrefl hmaj'
  have hlhs : E[Γ] ⊢ₛ .quotLift η l₁ l₂ α' r' β' f' h'
      (.quotMk η l₁ α' r' a) ≡ .quotLift η l₁ l₂ α' r' β' f' h'
        (.quotMk η l₁ α' r' a) : β' :=
    .quotLiftDF hαrefl hrrefl hβrefl hfrefl hhrefl (.quotMkDF hαrefl hrrefl haa)
  have hβwk := hβrefl.wk α'
  have hβinst : E[Γ] ⊢ₛ β'.wk.inst a : .sort l₂ := by simpa using hβrefl
  have hrhs : E[Γ] ⊢ₛ .app f' a : β' := by
    simpa using DefeqStrong.appDF hαrefl hβwk hfrefl haa hβinst
  have hiota : E[Γ] ⊢ₛ .quotLift η l₁ l₂ α' r' β' f' h'
      (.quotMk η l₁ α' r' a) ≡ .app f' a : β' :=
    .quotIota hαrefl hrrefl hβrefl hfrefl hhrefl haa hlhs hrhs
  have hleft : E[Γ] ⊢ₛ .quotLift η l₁ l₂ α' r' β' f' h' maj ≡
      .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ αq rq a) : β' :=
    .quotLiftDF hα hr hβ hf hh hmaj
  have hright : E[Γ] ⊢ₛ .app f' a ≡ .app f a : β' := by
    simpa using DefeqStrong.appDF hαrefl hβwk hf haa hβinst
  exact ht.symm.convStrong
    (hleft.symm.trans (htoRedex.trans (hiota.trans hright)))

theorem WHRed.quotIndIota_defeq (ho : E.Ordered) {η : Head ζ .quot}
    {l lq : Level ℓ} {α αq r rq β f a : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .quotInd η l α r β f (.quotMk η lq αq rq a) : t ⤳ .app f a := by
  intro hΓ hty
  have ⟨α', r', β', f', maj, hα, hr, hβ, hf, hmaj, hresult, ht⟩ :=
    DefeqStrong.quotInd_prem (Or.inl rfl) hty
  have ⟨_, _, a', _, _, ha, hquot⟩ :=
    DefeqStrong.quotMk_prem (Or.inr rfl) hmaj
  have ha' : E[Γ] ⊢ₛ a' ≡ a : α' :=
    (hquot.quot_inj ho hΓ).2.1.symm.convStrong ha
  have haa := ha'.right
  obtain ⟨rfl, hαq, hrq⟩ := (hmaj.quotMk_inv (Or.inr rfl)).quot_inj ho hΓ
  have ⟨_, hαq⟩ := hαq.sort_uniq ho hΓ
  have hαq := DefeqStrong.retype ho hΓ hαq hα.left
  have hmaj' := hmaj.trans (DefeqStrong.quotMkDF hαq hrq haa).symm
  have ⟨_, hmotive⟩ := hβ.regular
  have ⟨⟨_, hquotTy⟩, ⟨_, hprop⟩⟩ := DefeqStrong.forallE_inv (Or.inl rfl) hmotive
  have hmotiveApp : E[Γ] ⊢ₛ .app β' maj ≡ .app β' (.quotMk η l α' r' a) : .prop :=
    .appDF hquotTy hprop hβ.left hmaj' (hprop.inst_congr hmaj')
  have hredex := DefeqStrong.quotIndDF hα hr hβ hf hmaj hresult
  have hfrefl := hf.right
  have ⟨_, hminor⟩ := hfrefl.regular
  have ⟨⟨_, hα'⟩, ⟨_, hbody⟩⟩ := DefeqStrong.forallE_inv (Or.inl rfl) hminor
  have happ : E[Γ] ⊢ₛ .app f a : .app β' (.quotMk η l α' r' a) := by
    simpa using DefeqStrong.appDF hα' hbody hfrefl haa (hbody.inst_congr haa)
  exact ht.symm.convStrong (.proofIrrel hresult.left
    hredex.right (.defeqDF hmotiveApp.symm happ))

theorem WHRed.iota_defeq (ho : E.Ordered)
    {ι : IndSig} {η : Head ζ (.inductive ι)}
    {ls₁ ls₂ : Fin ι.nlevels → Level ℓ} {u : Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .recr η s ls₁ u ps₁ ms mins is (.ctor η s c ls₂ ps₂ fds recFds) : t ⤳
      (E.get η).block.iotaRhs η ls₁ u ps₁ ms mins s c fds recFds := by
  intro hΓ hty
  have hB := (ho.entryWFStrong η).block
  have ⟨ps', ms', mins', is', maj',
    hallowed, hps, hms, hmins, his, hmaj, hresult, ht⟩ :=
    DefeqStrong.recr_inv (Or.inl rfl) hty
  have ⟨psc, fdsc, recFdsc, hpsc, hfdsc, hrecFdsc, _, htc⟩ :=
    DefeqStrong.ctor_inv (Or.inr rfl) hmaj
  have ⟨_, htcStrong⟩ := htc.sort_uniq ho hΓ
  have hindSelf := DefeqStrong.indDF (fun p => (hps p).left) (fun i => (his i).left)
  obtain ⟨rfl, hpsInj, hisInj⟩ := (htcStrong.retype ho hΓ hindSelf).ind_inj ho hΓ
  have hpsc' p := (hpsInj p).choose_spec.retype ho hΓ (hps p).left
  have hisc' i := (hisInj i).choose_spec.retype ho hΓ (his i).left
  have hpscps p := ((hpsc' p).symm.trans (hps p)).retype ho hΓ (hpsc p).left
  have hps₂ps₁ p := ((hpsc p).symm.trans (hpscps p)).retype ho hΓ (Inductive.paramType_conv hB p hpsc)
  have hfds f := ((hB.ctors s c).ordinaryFieldExpr_congr
    hB.params f hpsc hfdsc).choose_spec.defeqDF (hfdsc f).right
  have hrecFds f := ((hB.ctors s c).recursiveFieldExpr_congr
    hB.params rfl f hpsc hfdsc).choose_spec.defeqDF (hrecFdsc f).right
  have hordFd f := ((hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps₂ps₁ hfds).choose_spec
  have hrecFd f := ((hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps₂ps₁ hfds).choose_spec
  have hctor := (DefeqStrong.indDF hps₂ps₁ fun i =>
    (hB.ctors s c).targetIndex_congr hB.params i hps₂ps₁ hfds).ctorDF
      hps₂ps₁ hfds hrecFds hordFd hrecFd
  have hmaj' := hmaj.trans (.retype ho hΓ hctor hmaj.right)
  have his' i := (hisc' i).trans (.retype ho hΓ
    ((hB.ctors s c).targetIndex_congr hB.params i hpscps hfdsc) (hisc' i).right)
  have hresult' := hB.motiveResult_congr hΓ hps hms his' hmaj'
  have hpsu p := Inductive.paramType_conv hB p hps
  have hmsu x := (Inductive.motiveType_congr hB hΓ hps).convStrong
    (hms x).right
  have hminsu x y := Inductive.caseFnType_conv hB hΓ hps hms (hmins x y)
  have hfdsu f := (hordFd f).defeqDF (hfds f)
  have hrecFdsu f := (hrecFd f).defeqDF (hrecFds f)
  have hσ := Ctor.targetSubstWFStrong hpsu hfdsu
  have hisu index := (hB.ctors s c).targetIndex index hσ
  have hmaju := DefeqStrong.ctorDF hpsu hfdsu hrecFdsu
    (fun f => (hB.ctors s c).ordinaryFieldExprStrong f hpsu hfdsu)
    (fun f => ((hB.ctors s c).recursiveFieldExprStrong rfl f hΓ hpsu hfdsu).choose_spec)
    (.indDF hpsu hisu)
  have htypeu := hB.motiveResult_congr hΓ hpsu hmsu hisu hmaju
  have hiota := DefeqStrong.iota hallowed hpsu hmsu hminsu hfdsu hrecFdsu htypeu
    (Inductive.iotaLhs_hasTypeStrong (hB.ctors s c) hallowed hΓ hpsu hmsu hminsu
      hfdsu hrecFdsu hσ htypeu)
    (hB.iotaRhs_hasTypeStrong hallowed hΓ hpsu hmsu hminsu hfdsu hrecFdsu)
  have hleft : E[Γ] ⊢ₛ .recr η s ls₁ u ps' ms' mins' is' maj' ≡
      .recr η s ls₁ u ps₁ ms mins is (.ctor η s c ls₁ ps₂ fds recFds) :
        Inductive.motiveResult (ms' s) is' maj' :=
    .recrDF hallowed hps hms hmins his hmaj hresult
  exact ht.symm.convStrong (hleft.symm.trans
    ((DefeqStrong.recrDF hallowed hps hms hmins his' hmaj' hresult').trans
      (.defeqDF hresult'.symm hiota)))

theorem Inductive.IsStructure.projTerm_ctor_defeq (ho : E.Ordered)
    {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (h : (E.get η).block.IsStructure s c)
    {ls ls₂ : Fin ι.nlevels → Level ℓ} {ps ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n} (f : Fin (ι.ctors s c).nfields) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ h.projTerm η ls ps f (.ctor η s c ls₂ ps₂ fds recFds) : t ⤳ fds f := by
  intro hΓ hty
  have hB := (ho.entryWFStrong η).block
  have hty' := hty
  rw [Inductive.IsStructure.projTerm_eq_recr] at hty'
  have ⟨ps', _, _, is', maj', _, hps, _, _, his, hmaj, _, _⟩ :=
    DefeqStrong.recr_inv (Or.inl rfl) hty'
  have ⟨psc, fdsc, recFdsc, hpsc, hfdsc, hrecFdsc, _, htc⟩ :=
    DefeqStrong.ctor_inv (Or.inr rfl) hmaj
  have ⟨_, htcStrong⟩ := htc.sort_uniq ho hΓ
  have hindSelf := DefeqStrong.indDF (fun p => (hps p).left) (fun i => (his i).left)
  obtain ⟨rfl, hpsInj, _⟩ := (htcStrong.retype ho hΓ hindSelf).ind_inj ho hΓ
  have hpsc' p := (hpsInj p).choose_spec.retype ho hΓ (hps p).left
  have hpscps p := ((hpsc' p).symm.trans (hps p)).retype ho hΓ (hpsc p).left
  have hps₂ps p :=
    ((hpsc p).symm.trans (hpscps p)).retype ho hΓ (Inductive.paramType_conv hB p hpsc)
  have hfds f := ((hB.ctors s c).ordinaryFieldExpr_congr
    hB.params f hpsc hfdsc).choose_spec.defeqDF (hfdsc f).right
  have hrecFds f := ((hB.ctors s c).recursiveFieldExpr_congr
    hB.params rfl f hpsc hfdsc).choose_spec.defeqDF (hrecFdsc f).right
  have hordFd f := ((hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps₂ps hfds).choose_spec
  have hrecFd f :=
    ((hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps₂ps hfds).choose_spec
  have hctor := (DefeqStrong.indDF hps₂ps fun i =>
    (hB.ctors s c).targetIndex_congr hB.params i hps₂ps hfds).ctorDF
      hps₂ps hfds hrecFds hordFd hrecFd
  have hpsu p := Inductive.paramType_conv hB p hps
  have hind : E[Γ] ⊢ₛ .ind η s ls ps' is' ≡ .ind η s ls ps h.indices typ :=
    .ofDefEq (DefeqStrong.indDF hps fun i => h.no_indices.elim i)
  have hmaj₂ := hind.convStrong hmaj.right
  have hctor' := DefeqStrong.retype ho hΓ hctor hmaj₂
  obtain rfl : recFds = h.recursive := funext h.no_recursive.elim
  have hfields cur : E[Γ] ⊢ₛ fds cur :
      Inductive.IsStructure.projTypeWith (E.get η).block ls ps cur fun previous =>
        fds (previous.castLE cur.isLt.le) := by
    simpa [Inductive.IsStructure.projTypeWith, Ctor.ordinaryType, Ctor.ordinaryFieldExpr]
      using (hordFd cur).defeqDF (hfds cur)
  have hiota := h.projTerm_ctorStrong hB f fds hΓ hpsu hctor'.right hfields
  have hcongr := h.projTerm_congrStrong hB f hpsu hctor'
  exact DefeqStrong.retype ho hΓ
    (hcongr.trans (DefeqStrong.retype ho hΓ hiota hcongr.right)) hty

theorem Inductive.IsStructure.projTerm_congr_defeq (ho : E.Ordered)
    {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c₁ c₂ : Fin (ι.nctors s)}
    (h₁ : (E.get η).block.IsStructure s c₁) (h₂ : (E.get η).block.IsStructure s c₂)
    {ls₁ ls₂ : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {maj₁ maj₂ : Expr ζ ℓ n} (f₁ : Fin (ι.ctors s c₁).nfields)
    (f₂ : Fin (ι.ctors s c₂).nfields) (hf : f₁.val = f₂.val) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ h₁.projTerm η ls₁ ps₁ f₁ maj₁ : t₁ →
    E[Γ] ⊢ₛ h₂.projTerm η ls₂ ps₂ f₂ maj₂ : t₂ →
    (∀ {T₁ T₂ : Expr ζ ℓ n}, E[Γ] ⊢ₛ maj₁ : T₁ → E[Γ] ⊢ₛ maj₂ : T₂ →
      E[Γ] ⊢ₛ maj₁ ≡ maj₂ : T₁) →
    E[Γ] ⊢ₛ h₁.projTerm η ls₁ ps₁ f₁ maj₁ ≡ h₂.projTerm η ls₂ ps₂ f₂ maj₂ : t₁ := by
  intro hΓ hty₁ hty₂ hmajD
  obtain rfl := h₁.ctor_unique c₂
  obtain rfl := Fin.ext hf
  have hB := (ho.entryWFStrong η).block
  have hty₁' := hty₁
  have hty₂' := hty₂
  rw [Inductive.IsStructure.projTerm_eq_recr] at hty₁' hty₂'
  have ⟨ps₁', _, _, is₁', _, _, hps₁, _, _, _, hmaj₁, _, _⟩ :=
    DefeqStrong.recr_inv (Or.inl rfl) hty₁'
  have ⟨ps₂', _, _, is₂', _, _, hps₂, _, _, _, hmaj₂, _, _⟩ :=
    DefeqStrong.recr_inv (Or.inl rfl) hty₂'
  have hpsu₁ p := Inductive.paramType_conv hB p hps₁
  have hpsu₂ p := Inductive.paramType_conv hB p hps₂
  have hind₁ : E[Γ] ⊢ₛ .ind η s ls₁ ps₁' is₁' ≡ .ind η s ls₁ ps₁ h₁.indices typ :=
    .ofDefEq (DefeqStrong.indDF hps₁ fun i => h₁.no_indices.elim i)
  have hind₂ : E[Γ] ⊢ₛ .ind η s ls₂ ps₂' is₂' ≡ .ind η s ls₂ ps₂ h₁.indices typ :=
    .ofDefEq (DefeqStrong.indDF hps₂ fun i => h₁.no_indices.elim i)
  have hm := hmajD (hind₁.convStrong hmaj₁.right) (hind₂.convStrong hmaj₂.right)
  have ⟨_, hindEq⟩ := (DefeqStrong.uniqTy ho hΓ hm.right (hind₂.convStrong hmaj₂.right)).sort_uniq
    ho hΓ
  obtain ⟨rfl, hpsInj, _⟩ :=
    (hindEq.retype ho hΓ (h₁.indTypeStrong hpsu₁)).ind_inj ho hΓ
  have hps p := (hpsInj p).choose_spec.retype ho hΓ (hpsu₁ p)
  have hcongr := h₁.projTerm_congrStrong hB f₁ hps hm
  exact DefeqStrong.retype ho hΓ hcongr hty₁

theorem Frame.plug_defeq (ho : E.Ordered) (K : Frame ζ ℓ n) :
    E[Γ] ⊢ₛ ok →
    (∀ {t₁}, E[Γ] ⊢ₛ e₁ : t₁ ⤳ e₂) →
    E[Γ] ⊢ₛ K.plug e₁ : t ⤳ K.plug e₂ := by
  intro hΓ hred hty
  cases K with
  | app a =>
    have ⟨t₁, t₂, hf, he, ht⟩ := hty.app_inv (Or.inl rfl)
    have ⟨_, hπ⟩ := hf.regular
    have ⟨⟨_, ht₁⟩, ⟨_, ht₂⟩⟩ := hπ.forallE_inv (Or.inl rfl)
    exact ht.symm.convStrong (.appDF ht₁ ht₂ (hred hf) he (ht₂.inst_congr he))
  | recr η s ls l ps ms mins is =>
    have ⟨_, _, _, _, _, hallowed, hps, hms, hmins, his, hmaj, hresult, ht⟩ :=
      hty.recr_inv (Or.inl rfl)
    have hmaj₂ := hmaj.trans (hred hmaj.right)
    exact ht.symm.convStrong
      ((DefeqStrong.recrDF hallowed hps hms hmins his hmaj hresult).symm.trans
        (.recrDF hallowed hps hms hmins his hmaj₂
          ((ho.entryWFStrong η).block.motiveResult_congr hΓ hps hms his hmaj₂)))
  | quotLift η l₁ l₂ α r β f h =>
    have ⟨_, _, _, _, _, _, hα, hr, hβ, hf, hh, ha, ht⟩ := hty.quotLift_prem (Or.inl rfl)
    exact ht.symm.convStrong
      ((DefeqStrong.quotLiftDF hα hr hβ hf hh ha).symm.trans
        (.quotLiftDF hα hr hβ hf hh (ha.trans (hred ha.right))))
  | quotInd η l α r β f =>
    have ⟨_, _, _, _, _, hα, hr, hβ, hf, ha, hresult, ht⟩ := hty.quotInd_prem (Or.inl rfl)
    have ha₂ := ha.trans (hred ha.right)
    have ⟨_, hmotive⟩ := hβ.regular
    have ⟨⟨_, hquot⟩, ⟨_, hprop⟩⟩ := hmotive.forallE_inv (Or.inl rfl)
    exact ht.symm.convStrong
      ((DefeqStrong.quotIndDF hα hr hβ hf ha hresult).symm.trans
        (.quotIndDF hα hr hβ hf ha₂ (.appDF hquot hprop hβ ha₂ (hprop.inst_congr ha₂))))

theorem WHRed.defeq (ho : E.Ordered) :
    E ⊢ e₁ ⤳ e₂ →
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ e₁ : t ⤳ e₂ := by
  intro hred hΔ h
  induction hred generalizing Γ t with
  | @frame _ _ K _ ih => exact K.plug_defeq ho hΔ (ih hΔ) h
  | beta => exact WHRed.beta_defeq ho hΔ h
  | zeta => exact WHRed.zeta_defeq ho hΔ h
  | delta => exact WHRed.delta_defeq ho h
  | recrMajor _ ih => exact (Frame.recr ..).plug_defeq ho hΔ (ih hΔ) h
  | iota => exact WHRed.iota_defeq ho hΔ h
  | quotIota => exact WHRed.quotIota_defeq ho hΔ h
  | quotIndIota => exact WHRed.quotIndIota_defeq ho hΔ h

theorem WHRedS.defeq (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E ⊢ e₁ ⤳* e₂ →
    E[Γ] ⊢ₛ e₁ : t ⤳ e₂ := by
  intro hΓ hred hty
  induction hred generalizing t with
  | refl => exact hty
  | tail _ hstep ih =>
    have h := ih hty
    exact h.trans (hstep.defeq ho hΓ h.right)

theorem WHRed.klike_defeq (ho : E.Ordered)
    {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n} {maj t : Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ .ind η s ls ps is : .prop →
    E[Γ] ⊢ₛ maj : .ind η s ls ps is →
    E[Γ] ⊢ₛ .ctor η s c ls ps fds recFds : .ind η s ls ps is →
    E[Γ] ⊢ₛ .recr η s ls l ps ms mins is maj : t ⤳
      (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds := by
  intro hΓ hprop hmaj hctor hrec
  have hm := DefeqStrong.proofIrrel hprop hmaj hctor
  have hr := (Frame.recr η s ls l ps ms mins is).plug_defeq ho hΓ (hm.retype ho hΓ) hrec
  exact hr.trans (WHRed.iota_defeq ho hΓ hr.right)

end Metalean
