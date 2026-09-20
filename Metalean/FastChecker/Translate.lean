/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Infer
public import Metalean.FastChecker.WF
public import Metalean.Frontend.Inductive

@[expose] public section

namespace Metalean.FastChecker

open Lean (Name)
open Frontend (Failure Table Binding Scope)

def translateLevel (lps : List Name) :
    Export.Level → Except Failure {l : FLevel // LevelWF lps.length l}
  | .zero => pure ⟨.zero, .zero, .zero⟩
  | .succ l => do
    let ⟨l, hl⟩ ← translateLevel lps l
    pure ⟨.succ l, have ⟨_, hl⟩ := hl; ⟨_, .succ hl⟩⟩
  | .max l₁ l₂ => do
    let ⟨l₁, hl₁⟩ ← translateLevel lps l₁
    let ⟨l₂, hl₂⟩ ← translateLevel lps l₂
    pure ⟨.max l₁ l₂, have ⟨_, hl₁⟩ := hl₁; have ⟨_, hl₂⟩ := hl₂; ⟨_, .max hl₁ hl₂⟩⟩
  | .imax l₁ l₂ => do
    let ⟨l₁, hl₁⟩ ← translateLevel lps l₁
    let ⟨l₂, hl₂⟩ ← translateLevel lps l₂
    pure ⟨.imax l₁ l₂, have ⟨_, hl₁⟩ := hl₁; have ⟨_, hl₂⟩ := hl₂; ⟨_, .imax hl₁ hl₂⟩⟩
  | .param name =>
    match lps.idxOf? name with
    | some p =>
      if hp : p < lps.length then pure ⟨.param p, ⟨.param ⟨p, hp⟩, .param hp⟩⟩
      else throw (.reject .unknownLevelParam)
    | none => throw (.reject .unknownLevelParam)

def translateLevels (lps : List Name) (us : List Export.Level) :
    Except Failure {ls : Array FLevel // ∀ i (h : i < ls.size), LevelWF lps.length ls[i]} := do
  let rs ← us.mapM (translateLevel lps)
  pure ⟨(rs.map Subtype.val).toArray, by
    intro i hi
    have hmem : (rs.map Subtype.val).toArray[i] ∈ rs.map Subtype.val :=
      List.getElem_mem _
    have ⟨r, hr, hval⟩ := List.mem_map.mp hmem
    exact hval ▸ r.2⟩

def ctorTargets (ι : IndSig) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (fctor : FCtor) :
    Except Failure (Fin fctor.recursive.size → Nat) := do
  let ⟨h⟩ ← guardProofOr (fctor.recursive.size = (ι.ctors s c).nrecFields) .internal
  pure fun r => ((ι.ctors s c).recursiveTarget ⟨r.val, h ▸ r.isLt⟩).val

def orderFns (metaOrder : List Nat) (k : Nat) :
    Except Failure ((Fin k → Fin k) × (Fin k → Fin k)) := do
  let some (π, πinv) := Frontend.orderMaps? metaOrder k | throw .internal
  let some toMeta := Fin.mapM π | throw .internal
  let some toLean := Fin.mapM πinv | throw .internal
  pure (toMeta, toLean)

def motivesOf (ms : Array FExpr) {nrec : Nat} (target : Fin nrec → Nat) :
    Except Failure (Fin nrec → FExpr) :=
  Fin.mapM fun r =>
    match ms[target r]? with
    | some m => pure m
    | none => throw .internal

def wrapCase (fctor : FCtor) (pos : Nat) (us : Array FLevel) (ps ms : Array FExpr) (n : Nat)
    (metaOrder : List Nat) (target : Fin fctor.recursive.size → Nat) (minor : FExpr) :
    Except Failure FExpr := do
  let nf := fctor.ordinary.size
  let nr := fctor.recursive.size
  if Frontend.isIdentityOrder metaOrder (nf + nr) then pure minor else
  let (toMeta, _) ← orderFns metaOrder (nf + nr)
  let motive ← motivesOf ms target
  let fieldArgs := Array.ofFn fun o : Fin (nf + nr) => FExpr.fvar (n + (toMeta o).val)
  let caseTys := fctor.ordinaryTys us ps n ++ fctor.recursiveTys pos us ps n target ++
    fctor.ihTys us ps n motive
  pure (FExpr.lamTele n caseTys ((minor.apps fieldArgs).apps (FExpr.fvars (n + nf + nr) nr)))

def indTerm (fI : FInductive) (pos s : Nat) (hs : s < fI.indices.size) (us : Array FLevel) : FExpr :=
  let np := fI.params.size
  FExpr.lamTele 0 (fI.params.map (·.instL us) ++ fI.indices[s].map (·.instL us))
    (.ind pos s us (FExpr.fvars 0 np) (FExpr.fvars np fI.indices[s].size))

def ctorTerm (fI : FInductive) (fctor : FCtor) (pos s c : Nat) (us : Array FLevel)
    (metaOrder : List Nat) (target : Fin fctor.recursive.size → Nat) : Except Failure FExpr := do
  let np := fI.params.size
  let nf := fctor.ordinary.size
  let nr := fctor.recursive.size
  let (toMeta, toLean) ← orderFns metaOrder (nf + nr)
  let fieldVars := Array.ofFn fun m : Fin (nf + nr) => FExpr.fvar (np + (toLean m).val)
  let ps := FExpr.fvars 0 np
  let tys := Array.ofFn fun o : Fin (nf + nr) =>
    let m := toMeta o
    if hm : m.val < nf then
      (fctor.ordinary[m.val].type.instL us).instFVars (ps ++ fieldVars.extract 0 m.val)
    else
      fctor.recursive[m.val - nf].instType pos (target ⟨m.val - nf, by omega⟩) us ps
        (ps ++ fieldVars.extract 0 nf) (np + o.val)
  pure (FExpr.lamTele 0 (fI.params.map (·.instL us) ++ tys)
    (.ctor pos s c us ps (fieldVars.extract 0 nf) (fieldVars.extract nf (nf + nr))))

def leanCaseType (fctor : FCtor) (pos t c : Nat) (us : Array FLevel) (ps ms : Array FExpr) (n : Nat)
    (metaOrder : List Nat) (target : Fin fctor.recursive.size → Nat) : Except Failure FExpr := do
  let nf := fctor.ordinary.size
  let nr := fctor.recursive.size
  let (toMeta, toLean) ← orderFns metaOrder (nf + nr)
  let motive ← motivesOf ms target
  let some sortMotive := ms[t]? | throw .internal
  let metaTys := fctor.ordinaryTys us ps n ++ fctor.recursiveTys pos us ps n target ++
    fctor.ihTys us ps n motive
  have hsize : metaTys.size = nf + nr + nr := by
    simp only [metaTys, nf, nr, FCtor.ordinaryTys, FCtor.recursiveTys, FCtor.ihTys, Array.size_append,
      Array.size_ofFn]
  let ren := FExpr.fvars 0 n ++
    (Array.ofFn fun m : Fin (nf + nr) => FExpr.fvar (n + (toLean m).val)) ++
    FExpr.fvars (n + nf + nr) nr
  let permTys := Array.ofFn fun o : Fin metaTys.size =>
    (if ho : o.val < nf + nr then metaTys[(toMeta ⟨o.val, ho⟩).val]'(by omega) else metaTys[o])
      |>.instFVars ren
  pure (FExpr.piTele n permTys ((fctor.caseType pos t c us ps n sortMotive).instFVars ren))

def recrTerm (ι : IndSig) (fI : FInductive) (pos s : Nat) (hs : s < fI.indices.size)
    (us : Array FLevel) (l : FLevel)
    (metaOrders : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) : Except Failure FExpr := do
  let np := fI.params.size
  let ns := ι.nsorts
  let nc := Fin.sum ι.nctors
  let casesEnd := np + ns + nc
  let ni := fI.indices[s].size
  let ps := FExpr.fvars 0 np
  let ms := FExpr.fvars np ns
  let motiveTys ← Fin.mapM fun t : Fin ns => do
    let ⟨ht⟩ ← guardProofOr (t.val < fI.indices.size) .internal
    pure (fI.motiveType pos us ps np t.val ht l)
  let caseTys ← Fin.mapM fun idx : Fin nc => do
    let ⟨t, c⟩ := Fin.decodeSigma ι.nctors idx
    let fctor ← fI.getCtor t.val c.val
    let target ← ctorTargets ι t c fctor
    leanCaseType fctor pos t.val c.val us ps ms (np + ns + idx.val) (metaOrders t c) target
  let mins ← Fin.mapM fun idx : Fin nc => do
    let ⟨t, c⟩ := Fin.decodeSigma ι.nctors idx
    let fctor ← fI.getCtor t.val c.val
    let target ← ctorTargets ι t c fctor
    wrapCase fctor pos us ps ms (casesEnd + ni + 1) (metaOrders t c) target
      (.fvar (np + ns + idx.val))
  let tele := fI.params.map (·.instL us) ++ Array.ofFn motiveTys ++ Array.ofFn caseTys ++
    fI.indexTele us ps casesEnd s hs ++ #[.ind pos s us ps (FExpr.fvars casesEnd ni)]
  pure (FExpr.lamTele 0 tele
    (.recr pos s us l ps ms (Array.ofFn mins) (FExpr.fvars casesEnd ni) (.fvar (casesEnd + ni))))

variable (F : FEnv) (L : Literals) (table : Table) (lps : List Name) (hints : Array Export.Hints)
  (accel : Accel L F)

def whnfOf (G : FCtx) (t : FExpr) : CheckM L F lps.length FExpr := do
  let ⟨t, _⟩ ← whnf L F lps.length hints accel G t
  pure t

def inferWhnf (G : FCtx) (e : FExpr) : CheckM L F lps.length FExpr := do
  let G ← prefixFor L F lps.length G e
  let ⟨t, _⟩ ← inferOnly L F lps.length hints accel G e
  whnfOf F L lps hints accel G t

section ProofProjection

variable (fI : FInductive) (fctor : FCtor) (pos s : Nat) (hs : s < fI.indices.size)
  (us : Array FLevel) (target : Fin fctor.recursive.size → Nat)

mutual

partial def proofProjection (n : Nat) (G : FCtx) (ps : Array FExpr) (f : Nat)
    (maj : FExpr) : CheckM L F lps.length FExpr := do
  let Δ := fI.motiveTele pos us ps n s hs
  let ni := fI.indices[s].size
  let type ← proofProjectionType (n + ni + 1) (G ++ Δ) ps f (.fvar (n + ni))
  let motive := FExpr.lamTele n Δ type
  let case := FExpr.lamTele n
    (fctor.ordinaryTys us ps n ++ fctor.recursiveTys pos us ps n target ++
      fctor.ihTys us ps n fun _ => motive)
    (.fvar (n + f))
  pure (.recr pos s us .zero ps #[motive] #[case] #[] maj)

partial def proofProjectionType (n : Nat) (G : FCtx) (ps : Array FExpr) (f : Nat)
    (maj : FExpr) : CheckM L F lps.length FExpr := do
  let mut type := FExpr.piTele n (fctor.ordinaryTys us ps n ++ fctor.recursiveTys pos us ps n target)
    (.sort .zero)
  for j in [:f] do
    let .forallE _ body ← whnfOf F L lps hints accel G type | throw (.decline .unchecked)
    if body.data.looseBVarRange.toNat = 0 then type := body
    else
      unless j < fctor.ordinary.size do throw (.decline .unchecked)
      let projected ← proofProjection n G ps j maj
      type := FExpr.instAt projected 0 body
  let .forallE field _ ← whnfOf F L lps hints accel G type | throw (.decline .unchecked)
  let .sort l ← inferWhnf F L lps hints accel G field | throw (.decline .unchecked)
  unless ← liftExcept (l.isZero lps.length) do throw (.reject .propProjection)
  pure field

end

end ProofProjection

abbrev Witnessed (F : FEnv) (L : Literals) (ℓ n k : Nat) :=
  {e : FExpr // WFSpec L F ℓ n k e}

theorem mem_witnessed {ℓ n k : Nat} {args : List (Witnessed F L ℓ n k)} {a : FExpr}
    (ha : a ∈ args.map Subtype.val) :
    WFSpec L F ℓ n k a :=
  have ⟨r, _, hval⟩ := List.mem_map.mp ha
  hval ▸ r.2

def applyArgs {ℓ n k : Nat} (e : Witnessed F L ℓ n k) (args : List (Witnessed F L ℓ n k)) :
    Witnessed F L ℓ n k :=
  ⟨e.val.appList (args.map Subtype.val), WFSpec.appList _ e.2 fun _ => mem_witnessed F L⟩

theorem teleWF_push {ℓ n : Nat} {Δ : Array FExpr} {t : FExpr}
    (hΔ : ∀ j (hj : j < Δ.size), WFSpec L F ℓ (n + j) 0 Δ[j])
    (ht : WFSpec L F ℓ (n + Δ.size) 0 t) :
    ∀ j (hj : j < (Δ.push t).size), WFSpec L F ℓ (n + j) 0 (Δ.push t)[j] := by
  intro j hj
  by_cases hlt : j < Δ.size
  · rw [Array.getElem_push_lt hlt]
    exact hΔ j hlt
  · obtain rfl : j = Δ.size := by simp at hj; omega
    rw [Array.getElem_push_eq]
    exact ht

theorem arrWF_extract {ℓ n k : Nat} {a : Array FExpr}
    (h : ∀ i (hi : i < a.size), WFSpec L F ℓ n k a[i]) (lo hi : Nat) :
    ArrWF L F ℓ n k (a.extract lo hi) := by
  intro i hi'
  rw [Array.getElem_extract]
  exact h _ _

theorem arrWF_ofFn {ℓ n k m : Nat} {f : Fin m → Witnessed F L ℓ n k} :
    ArrWF L F ℓ n k (Array.ofFn fun i => (f i).val) := by
  intro i hi
  rw [Array.getElem_ofFn]
  exact (f _).2

theorem arrWF_witnessed {ℓ n k : Nat} (a : Array (Witnessed F L ℓ n k)) :
    ∀ i (hi : i < (a.map Subtype.val).size), WFSpec L F ℓ n k (a.map Subtype.val)[i] := by
  intro i hi
  rw [Array.getElem_map]
  exact (a[i]'(by simpa using hi)).2

def witness {ℓ n k : Nat} (e : FExpr) : Except Failure (Witnessed F L ℓ n k) := do
  let ⟨h⟩ ← FExpr.wf L F ℓ n k e
  pure ⟨e, h⟩

structure TranslateState (ℓ n : Nat) where
  cache : Std.HashMap (USize × Nat) ((k : Nat) × Witnessed F L ℓ (n + k) k) := ∅
  «scoped» : Std.HashMap (USize × Nat × Nat) ((k : Nat) × Witnessed F L ℓ (n + k) k × Nat) := ∅
  closed : Std.HashMap USize (Witnessed F L ℓ n 0) := ∅
  nextId : Nat := 1
  replace : Std.HashMap Nat FExpr.OpenClose := ∅
  resolves : Std.HashMap Nat FExpr.ReplaceCache := ∅
  reach : Option Nat := none
  caches : Caches L F ℓ := {}
  wf : WFCache L F ℓ := ∅

abbrev TranslateM (n : Nat) :=
  StateT (TranslateState F L lps.length n) (Except Failure)

def liftCheck {n : Nat} {α : Type} (x : CheckM L F lps.length α) : TranslateM F L lps n α := do
  let st ← get
  match x.run st.caches with
  | .ok a caches => set { st with caches }; pure a
  | .error f caches => set { st with caches }; throw f

def liftWF {n : Nat} {α : Type} (x : WFM L F lps.length α) : TranslateM F L lps n α := do
  let st ← get
  let (r, wf) ← x.run st.wf
  set { st with wf }
  pure r

def openMemo (n k : Nat) (fe : FExpr) : TranslateM F L lps n FExpr :=
  modifyGet fun st =>
    let replace := st.replace
    let st := { st with replace := ∅ }
    let c := replace.getD k {}
    let replace := replace.erase k
    let (r, c) := c.open n k fe
    (r, { st with replace := replace.insert k c })

def closeMemo (n k : Nat) (fe : FExpr) : TranslateM F L lps n FExpr :=
  modifyGet fun st =>
    let replace := st.replace
    let st := { st with replace := ∅ }
    let c := replace.getD k {}
    let replace := replace.erase k
    let (r, c) := c.close n k fe
    (r, { st with replace := replace.insert k c })

structure LocalScope where
  ids : Array Nat
  types : FCtx
  values : Array FExpr
  letId : Option Nat

def LocalScope.ofCtx (G : FCtx) : LocalScope where
  ids := #[]
  types := G
  values := Array.ofFn fun i : Fin G.size => .fvar i.val
  letId := none

def resolve {n : Nat} (G : LocalScope) (fe : FExpr) : TranslateM F L lps n FExpr :=
  match G.letId with
  | none => pure fe
  | some id =>
    modifyGet fun st =>
      let resolves := st.resolves
      let st := { st with resolves := ∅ }
      let c := resolves.getD id {}
      let resolves := resolves.erase id
      let (r, c) := c.instFVars G.values fe
      (r, { st with resolves := resolves.insert id c })

def structType (n k : Nat) (G : LocalScope) (e : FExpr) :
    TranslateM F L lps n (FCtx × FExpr × FExpr) := do
  let opened ← openMemo F L lps n k e
  let r ← liftCheck F L lps (inferWhnf F L lps hints accel G.types opened)
  if r matches .ind .. then return (G.types, opened, r)
  if G.letId.isNone then return (G.types, opened, r)
  let opened ← resolve F L lps G opened
  let types ← G.types.foldlM (init := (#[] : FCtx)) fun acc t => do
    let ⟨acc, _⟩ ← liftCheck F L lps (pushCtx L F lps.length acc (← resolve F L lps G t))
    pure acc
  let r ← liftCheck F L lps (inferWhnf F L lps hints accel types opened)
  return (types, opened, r)

def project (n k : Nat) (G : LocalScope) (name : Name) (idx : Nat)
    (e : Witnessed F L lps.length (n + k) k) :
    TranslateM F L lps n (Witnessed F L lps.length (n + k) k) := do
  let some (.ind pos s) := table.get? name | throw (.reject (.unknownName name))
  match hfe : F[pos]? with
  | some (.inductive ι fI) => do
    let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
    let ⟨hc₁⟩ ← guardProofOr (ι.nctors ⟨s, hs⟩ = 1) (.reject .shape)
    have hc : 0 < ι.nctors ⟨s, hs⟩ := by omega
    let ⟨hf⟩ ← guardProofOr (idx < (ι.ctors ⟨s, hs⟩ ⟨0, hc⟩).nfields) (.reject .arity)
    if hstruct : fI.isStructure s 0 then
      return ⟨.proj pos s idx e.val, WFSpec.proj hfe hs hc hstruct hf e.2⟩
    let range := e.val.data.looseBVarRange.toNat
    if range ≠ 0 then
      let depth := if range < Data.maxRange then k - range else 0
      modify fun st => { st with reach := some (st.reach.elim depth (min depth)) }
    let (types, opened, r) ← structType F L lps hints accel n k G e.val
    let .ind pos₂ s₂ us psOpen _ := r
      | throw (.reject .shape)
    unless pos₂ = pos ∧ s₂ = s do throw (.reject .shape)
    let ⟨hs'⟩ ← guardProofOr (s < fI.indices.size) .internal
    let fctor ← fI.getCtor s 0
    let target ← ctorTargets ι ⟨s, hs⟩ ⟨0, hc⟩ fctor
    unless ι.nsorts = 1 do throw (.reject .shape)
    unless ι.nindices ⟨s, hs⟩ = 0 do throw (.reject .shape)
    unless (ι.ctors ⟨s, hs⟩ ⟨0, hc⟩).nrecFields = 0 do throw (.reject .shape)
    let proj ← liftCheck F L lps
      (proofProjection F L lps hints accel fI fctor pos s hs' us target (n + k) types psOpen idx opened)
    let closed ← closeMemo F L lps n k proj
    let ⟨h⟩ ← liftWF F L lps (FExpr.wfM L F lps.length (n + k) k closed)
    return ⟨closed, h⟩
  | _ => throw .internal

def wrapCaseW {n k : Nat} (fctor : FCtor) (pos : Nat) (us : Array FLevel) (ps ms : Array FExpr)
    (metaOrder : List Nat) (target : Fin fctor.recursive.size → Nat)
    (minor : Witnessed F L lps.length n k) :
    Except Failure (Witnessed F L lps.length n k) := do
  if Frontend.isIdentityOrder metaOrder (fctor.ordinary.size + fctor.recursive.size) then pure minor
  else
    let opened (e : FExpr) := e.openBVars (n - k) k
    let wrapped ← wrapCase fctor pos us (ps.map opened) (ms.map opened) n metaOrder target
      (opened minor.val)
    witness F L (wrapped.closeFVars (n - k) k)

def saturate {ℓ n k : Nat} (arity : Nat) (args : List (Witnessed F L ℓ n k))
    (node : (a : Array (Witnessed F L ℓ n k)) → a.size = arity →
      Except Failure (Witnessed F L ℓ n k))
    (eta : Unit → Except Failure (Witnessed F L ℓ n k)) :
    Except Failure (Witnessed F L ℓ n k) := do
  if h : arity ≤ args.length then
    return applyArgs F L (← node (args.take arity).toArray (by simp; omega)) (args.drop arity)
  else
    return applyArgs F L (← eta ()) args

def translateConst {n k : Nat} (pos : Nat) (us : List Export.Level) :
    Except Failure (Witnessed F L lps.length n k) := do
  let ⟨us, hus⟩ ← translateLevels lps us
  match hfe : F[pos]? with
  | some (.axiom nlevels _) | some (.opaque nlevels _) | some (.def nlevels _ _) => do
    let ⟨hls⟩ ← guardProofOr (us.size = nlevels) (Failure.reject .arity)
    pure ⟨.const pos us, WFSpec.const hfe rfl hls hus⟩
  | _ => throw .internal

def translateSpecial {n k : Nat} (us : List Export.Level)
    (args : List (Witnessed F L lps.length n k)) :
    Binding → Except Failure (Witnessed F L lps.length n k)
  | .const _ => throw .internal
  | .quot pos kind =>
    match hfe : F[pos]? with
    | some (.quot eqPos) => do
      let us ← us.mapM (translateLevel lps)
      let eta := fun () => do
        witness F L (← FExpr.quotTerm pos eqPos kind (us.map Subtype.val))
      match kind, us with
      | .type, [u] =>
        saturate F L 2 args
          (fun a h => pure ⟨.quot pos u a[0] a[1],
            WFSpec.quot hfe u.2 a[0].2 a[1].2⟩) eta
      | .ctor, [u] =>
        saturate F L 3 args
          (fun a h => pure ⟨.quotMk pos u a[0] a[1] a[2],
            WFSpec.quotMk hfe u.2 a[0].2 a[1].2 a[2].2⟩) eta
      | .lift, [u, v] =>
        saturate F L 6 args
          (fun a h => pure ⟨.quotLift pos u v a[0] a[1] a[2] a[3] a[4] a[5],
            WFSpec.quotLift hfe u.2 v.2 a[0].2 a[1].2 a[2].2 a[3].2 a[4].2 a[5].2⟩) eta
      | .ind, [u] =>
        saturate F L 5 args
          (fun a h => pure ⟨.quotInd pos u a[0] a[1] a[2] a[3] a[4],
            WFSpec.quotInd hfe u.2 a[0].2 a[1].2 a[2].2 a[3].2 a[4].2⟩) eta
      | _, _ => throw (.reject .arity)
    | _ => throw .internal
  | .ind pos s =>
    match hfe : F[pos]? with
    | some (.inductive ι fI) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hs'⟩ ← guardProofOr (s < fI.indices.size) .internal
      let ⟨us, hus⟩ ← translateLevels lps us
      let ⟨hls⟩ ← guardProofOr (us.size = ι.nlevels) (Failure.reject .arity)
      saturate F L (ι.nparams + ι.nindices ⟨s, hs⟩) args
        (fun a h =>
          pure ⟨.ind pos s us ((a.map Subtype.val).extract 0 ι.nparams)
              ((a.map Subtype.val).extract ι.nparams (a.map Subtype.val).size),
            WFSpec.ind hfe hs hls
              (by simp; omega)
              (by simp; omega)
              hus
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)⟩)
        fun _ => witness F L (indTerm fI pos s hs' us)
    | _ => throw .internal
  | .ctor pos s c metaOrder =>
    match hfe : F[pos]? with
    | some (.inductive ι fI) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hc⟩ ← guardProofOr (c < ι.nctors ⟨s, hs⟩) (.reject .shape)
      let csig := ι.ctors ⟨s, hs⟩ ⟨c, hc⟩
      let fctor ← fI.getCtor s c
      let target ← ctorTargets ι ⟨s, hs⟩ ⟨c, hc⟩ fctor
      let ⟨us, hus⟩ ← translateLevels lps us
      let ⟨hls⟩ ← guardProofOr (us.size = ι.nlevels) (Failure.reject .arity)
      saturate F L (ι.nparams + (csig.nfields + csig.nrecFields)) args
        (fun a h => do
          let some (_, πinv) := Frontend.orderMaps? metaOrder (csig.nfields + csig.nrecFields)
            | throw .internal
          let fieldArg (o : Fin (csig.nfields + csig.nrecFields)) :
              Option (Witnessed F L lps.length n k) :=
            (πinv o).bind fun j => a[ι.nparams + j.val]?
          let some fds := Fin.mapM fun f => fieldArg (f.castAdd csig.nrecFields)
            | throw .internal
          let some recFds := Fin.mapM fun r => fieldArg (Fin.natAdd csig.nfields r)
            | throw .internal
          pure ⟨.ctor pos s c us ((a.map Subtype.val).extract 0 ι.nparams)
              (Array.ofFn fun f => (fds f).val) (Array.ofFn fun r => (recFds r).val),
            WFSpec.ctor hfe hs hc hls
              (by simp; omega)
              Array.size_ofFn Array.size_ofFn hus
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)
              (arrWF_ofFn F L)
              (arrWF_ofFn F L)⟩)
        fun _ => do witness F L (← ctorTerm fI fctor pos s c us metaOrder target)
    | _ => throw .internal
  | .recr pos s orders =>
    match hfe : F[pos]? with
    | some (.inductive ι fI) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hs'⟩ ← guardProofOr (s < fI.indices.size) .internal
      let (l, rest) ←
        if fI.largeElim then
          match us with
          | u :: rest => do pure (← translateLevel lps u, rest)
          | [] => throw (.reject .arity)
        else pure (⟨FLevel.zero, ⟨.zero, .zero⟩⟩, us)
      let ⟨us, hus⟩ ← translateLevels lps rest
      let ⟨hls⟩ ← guardProofOr (us.size = ι.nlevels) (Failure.reject .arity)
      let some metaOrders := Fin.mapM fun t : Fin ι.nsorts =>
          Fin.mapM fun c : Fin (ι.nctors t) => orders[t.val]?.bind (·[c.val]?)
        | throw .internal
      let np := ι.nparams
      let ns := ι.nsorts
      let nc := Fin.sum ι.nctors
      let ni := ι.nindices ⟨s, hs⟩
      saturate F L (ι.recrEnd ⟨s, hs⟩) args
        (fun a h => do
          have h' : a.size = np + ns + nc + ni + 1 := h
          let raw := a.map Subtype.val
          let mins ← Fin.mapM fun idx : Fin nc => do
            let ⟨t, c⟩ := Fin.decodeSigma ι.nctors idx
            let fctor ← fI.getCtor t.val c.val
            let target ← ctorTargets ι t c fctor
            wrapCaseW F L lps fctor pos us (raw.extract 0 np) (raw.extract np (np + ns))
              (metaOrders t c) target a[np + ns + idx.val]
          have hps : (raw.extract 0 np).size = ι.nparams := by simp [raw]; omega
          have hms : (raw.extract np (np + ns)).size = ι.nsorts := by simp [raw]; omega
          have his : (raw.extract (np + ns + nc) (np + ns + nc + ni)).size =
              ι.nindices ⟨s, hs⟩ := by
            simp [raw]; omega
          pure ⟨.recr pos s us l.val (raw.extract 0 np) (raw.extract np (np + ns))
              (Array.ofFn fun idx => (mins idx).val) (raw.extract (np + ns + nc) (np + ns + nc + ni))
              a[np + ns + nc + ni],
            WFSpec.recr hfe hs hls hps hms Array.size_ofFn his hus l.2
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)
              (arrWF_ofFn F L)
              (arrWF_extract F L (arrWF_witnessed F L a) _ _)
              a[np + ns + nc + ni].2⟩)
        fun _ => do witness F L (← recrTerm ι fI pos s hs' us l.val metaOrders)
    | _ => throw .internal

unsafe def exprAddrImpl (e : Export.Expr) : USize :=
  ptrAddrUnsafe e

@[implemented_by exprAddrImpl]
opaque exprAddr (e : Export.Expr) : USize

def lowestBit (m : UInt64) : (fuel : Nat) → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if (m >>> i.toUInt64) &&& 1 == 1 then i else lowestBit m fuel (i + 1)

def scopeId {n : Nat} (ids : Array Nat) (e : Export.Expr) : TranslateM F L lps n Nat := do
  let m := e.looseMask
  if m == 0 then return 0
  let j := lowestBit m 64 0
  if j ≥ 63 then return ids.back?.getD 0
  return (ids[ids.size - 1 - j]?).getD 0

def mergeReach {n : Nat} (inner : Option Nat) : TranslateM F L lps n Unit :=
  modify fun st => { st with reach := match st.reach, inner with
    | some a, some b => some (min a b)
    | a, b => a <|> b }

def freshId {n : Nat} : TranslateM F L lps n Nat :=
  modifyGet fun st => (st.nextId, { st with nextId := st.nextId + 1 })

def pushLocal {n : Nat} (k : Nat) (G : LocalScope) (t : FExpr) (value : Option FExpr) :
    TranslateM F L lps n LocalScope := do
  let t' ← openMemo F L lps n k t
  let ⟨types, _⟩ ← liftCheck F L lps (pushCtx L F lps.length G.types t')
  let id ← freshId F L lps
  match value with
  | none =>
    return { G with ids := G.ids.push id, types, values := G.values.push (.fvar G.types.size) }
  | some v =>
    let v' ← resolve F L lps G (← openMemo F L lps n k v)
    return { ids := G.ids.push id, types, values := G.values.push v', letId := some id }

def substLets {n k : Nat} (m : Nat) (subst : Array FExpr)
    (w : Witnessed F L lps.length (n + k) k) :
    TranslateM F L lps n (FExpr × Witnessed F L lps.length (n + k) k) := do
  let wo ← openMemo F L lps n k w.val
  if wo.fvarRange + m ≤ n + k then return (wo, w)
  let ws := wo.instFVars subst
  let z ← closeMemo F L lps n k ws
  let ⟨hz⟩ ← liftWF F L lps (FExpr.wfM L F lps.length (n + k) k z)
  return (ws, ⟨z, hz⟩)

mutual

partial def translateWith {n k : Nat} (G : LocalScope) (ρ : Scope n)
    (args : List (Witnessed F L lps.length (n + k) k)) (e : Export.Expr) :
    TranslateM F L lps n (Witnessed F L lps.length (n + k) k) := do
  unless args.isEmpty do return ← translateCore G ρ args e
  if let some w := (← get).closed.get? (exprAddr e) then return ⟨w.1, w.2.wkNOpen k⟩
  let key := (exprAddr e, k)
  if let some ⟨k', w⟩ := (← get).cache.get? key then
    if h : k' = k then return h ▸ w
  let scopedKey := (exprAddr e, k, ← scopeId F L lps G.ids e)
  if let some ⟨k', w, depth⟩ := (← get).scoped.get? scopedKey then
    if h : k' = k then
      mergeReach F L lps (some depth)
      return h ▸ w
  let outer := (← get).reach
  modify ({ · with reach := none })
  let w ← translateCore G ρ [] e
  let inner := (← get).reach
  match inner with
  | some depth =>
    if k ≤ depth then modify fun st => { st with cache := st.cache.insert key ⟨k, w⟩ }
    else modify fun st => { st with «scoped» := st.scoped.insert scopedKey ⟨k, w, depth⟩ }
  | none =>
    if hc : w.val.data.looseBVarRange.toNat = 0 then
      if hr : w.val.fvarRange = 0 then
        modify fun st =>
          { st with closed := st.closed.insert (exprAddr e) ⟨w.val, w.2.ofClosed (by omega) hc⟩ }
      else modify fun st => { st with cache := st.cache.insert key ⟨k, w⟩ }
    else modify fun st => { st with cache := st.cache.insert key ⟨k, w⟩ }
  modify ({ · with reach := outer })
  mergeReach F L lps inner
  return w

partial def translateCore {n k : Nat} (G : LocalScope) (ρ : Scope n)
    (args : List (Witnessed F L lps.length (n + k) k)) :
    Export.Expr → TranslateM F L lps n (Witnessed F L lps.length (n + k) k)
  | .bvar i =>
    if hi : i < k then pure (applyArgs F L ⟨.bvar i, WFSpec.bvar hi (by omega)⟩ args)
    else match ρ (i - k) with
      | some v => pure (applyArgs F L ⟨.fvar v.val, WFSpec.fvar (by have := v.isLt; omega)⟩ args)
      | none => throw (.reject .unboundVariable)
  | .sort l => do
    let ⟨l, hl⟩ ← translateLevel lps l
    pure (applyArgs F L ⟨.sort l, WFSpec.sort hl⟩ args)
  | .const name us =>
    match table.get? name with
    | none => throw (.reject (.unknownName name))
    | some (.const pos) => return applyArgs F L (← translateConst F L lps pos us) args
    | some binding => translateSpecial F L lps us args binding
  | .app fn arg => do
    let arg ← translateWith G ρ [] arg
    translateWith G ρ (arg :: args) fn
  | .lam type body => do
    let ⟨t, ht⟩ ← translateWith G ρ [] type
    let ⟨b, hb⟩ ←
      translateWith (k := k + 1) (← pushLocal F L lps k G t none) ρ [] body
    pure (applyArgs F L ⟨.lam t b, WFSpec.lam ht hb⟩ args)
  | .forallE type body => do
    let ⟨t, ht⟩ ← translateWith G ρ [] type
    let ⟨b, hb⟩ ←
      translateWith (k := k + 1) (← pushLocal F L lps k G t none) ρ [] body
    pure (applyArgs F L ⟨.forallE t b, WFSpec.forallE ht hb⟩ args)
  | .letE type value body => do
    let subst : Array FExpr := Array.ofFn fun i : Fin (n + k) => .fvar i.val
    return applyArgs F L (← translateLets G ρ 0 subst (.letE type value body)) args
  | .proj name idx e => do
    let e ← translateWith G ρ [] e
    return applyArgs F L (← project F L table lps hints accel n k G name idx e) args
  | .natLit num => return applyArgs F L (← witness F L (.natLit num)) args
  | .stringLit str => return applyArgs F L (← witness F L (.strLit str)) args

partial def translateLets {n k : Nat} (G : LocalScope) (ρ : Scope n) (m : Nat)
    (subst : Array FExpr) (e : Export.Expr) :
    TranslateM F L lps n (Witnessed F L lps.length (n + k) k) := do
  match e with
  | .letE type value body =>
    let t ← translateWith G ρ [] type
    let v ← translateWith G ρ [] value
    let (_, ⟨t', ht'⟩) ← substLets F L lps (k := k) m subst t
    let (vs, ⟨v', hv'⟩) ← substLets F L lps (k := k) m subst v
    let ⟨z, hz⟩ ← translateLets (k := k + 1)
      (← pushLocal F L lps k G t.val (some v.val)) ρ (m + 1) (subst.push vs) body
    pure ⟨.app (.lam t' z) v', WFSpec.app (WFSpec.lam ht' hz) hv'⟩
  | _ =>
    let b ← translateWith G ρ [] e
    let (_, z) ← substLets F L lps (k := k) m subst b
    pure z

end

def translate {n : Nat} (G : FCtx) (ρ : Scope n) (e : Export.Expr) :
    Except Failure (Witnessed F L lps.length n 0) :=
  (translateWith F L table lps hints accel (k := 0) (.ofCtx G) ρ [] e).run' {}

def translateClosed (e : Export.Expr) : Except Failure (Witnessed F L lps.length 0 0) :=
  translate F L table lps hints accel #[] Scope.empty e

def translateClosedPair (e₁ e₂ : Export.Expr) :
    Except Failure (Witnessed F L lps.length 0 0 × Witnessed F L lps.length 0 0) :=
  (do
    let w₁ ← translateWith F L table lps hints accel (k := 0) (.ofCtx #[]) Scope.empty [] e₁
    let w₂ ← translateWith F L table lps hints accel (k := 0) (.ofCtx #[]) Scope.empty [] e₂
    pure (w₁, w₂)).run' {}

structure FPreCtor where
  ordinary : Array FExpr
  recursive : Array FRecField
  targetIndices : Array FExpr

structure FPreInductive where
  params : FCtx
  indices : Array FCtx
  level : FLevel
  ctors : Array (Array FPreCtor)

def FPreCtor.withLevels (pre : FPreCtor) (levels : Fin pre.ordinary.size → FLevel) : FCtor where
  ordinary := Array.ofFn fun f => ⟨pre.ordinary[f], levels f⟩
  recursive := pre.recursive
  targetIndices := pre.targetIndices

def FPreInductive.withLevels (pre : FPreInductive)
    (levels : (s : Fin pre.ctors.size) → (c : Fin pre.ctors[s].size) →
      Fin pre.ctors[s][c].ordinary.size → FLevel) : FInductive where
  params := pre.params
  indices := pre.indices
  level := pre.level
  ctors := Array.ofFn fun s => Array.ofFn fun c => pre.ctors[s][c].withLevels (levels s c)

structure FBlockResult where
  ι : IndSig
  pre : FPreInductive
  sortNames : List Name
  ctorNames : List (List Name)
  metaOrders : List (List (List Nat))

def buildFrom {n : Nat} (G : FCtx) (ρ : Scope n) :
    (rev : List Export.Expr) →
    Except Failure {ts : Array FExpr // ts.size = rev.length ∧
      ∀ j (hj : j < ts.size), WFSpec L F lps.length (n + j) 0 ts[j]}
  | [] => pure ⟨#[], rfl, fun j hj => absurd hj (by simp)⟩
  | t :: rest => do
    let ⟨Δ, hsize, hΔ⟩ ← buildFrom G ρ rest
    let ⟨t', ht'⟩ ← translate F L table lps hints accel (n := n + rest.length) (G ++ Δ)
      (ρ.pushN rest.length) t
    pure ⟨Δ.push t', by simp [hsize], teleWF_push F L hΔ (hsize ▸ ht')⟩

structure RecFieldPieces (F : FEnv) (L : Literals) (ℓ nparams nfields arity nindices : Nat)
    (ffd : FRecField) : Prop where
  teleSize : ffd.tele.size = arity
  teleWF : ∀ j (hj : j < ffd.tele.size),
    WFSpec L F ℓ (nparams + nfields + j) 0 ffd.tele[j]
  indicesSize : ffd.indices.size = nindices
  indicesWF : ArrWF L F ℓ (nparams + nfields + arity) 0 ffd.indices

def preRecField {nsorts : Nat} (nparams : Nat) (sd : Fin nsorts → Frontend.SortData nsorts)
    (ords : List Frontend.OrdField) (nfields : Nat) (G : Array FExpr)
    (rf : Frontend.RecField nsorts) :
    Except Failure {ffd : FRecField // RecFieldPieces F L lps.length nparams nfields
      rf.bindersRev.length (sd rf.target).indicesRev.length ffd} := do
  let ρ := Frontend.fieldScope ords nparams rf.leanPos (nparams + nfields)
  let ⟨tele, hteleSize, hteleWF⟩ ← buildFrom F L table lps hints accel (n := nparams + nfields) G ρ
    rf.bindersRev
  let is ← rf.indices.mapM fun i =>
    translate F L table lps hints accel (n := nparams + nfields + rf.bindersRev.length) (G ++ tele)
      (ρ.pushN rf.bindersRev.length) i
  let ⟨hisSize⟩ ← guardProofOr (is.length = (sd rf.target).indicesRev.length)
    (Failure.reject .arity)
  pure ⟨⟨tele, (is.map Subtype.val).toArray⟩,
    hteleSize, hteleWF, by simpa using hisSize,
    fun i hi => mem_witnessed F L (List.getElem_mem _)⟩

def ordinaryFields {nsorts : Nat} (nparams : Nat) (params : Array FExpr)
    (shape : Frontend.CtorShape nsorts) :
    (count : Nat) → count ≤ shape.ords.length →
    Except Failure {ts : Array FExpr // ts.size = count ∧
      ∀ j (hj : j < ts.size), WFSpec L F lps.length (nparams + j) 0 ts[j]}
  | 0 => fun _ => pure ⟨#[], rfl, fun j hj => absurd hj (by simp)⟩
  | count + 1 => fun h => do
    let ⟨Δ, hsize, hΔ⟩ ← ordinaryFields nparams params shape count (by omega)
    let field := shape.ords[count]
    let ⟨t, ht⟩ ← translate F L table lps hints accel (n := nparams + count) (params ++ Δ)
      (Frontend.fieldScope shape.ords nparams field.leanPos (nparams + count)) field.type
    pure ⟨Δ.push t, by simp [hsize], teleWF_push F L hΔ (hsize ▸ ht)⟩

def preCtorOf {nsorts : Nat} (nparams : Nat) (params : Array FExpr)
    (sd : Fin nsorts → Frontend.SortData nsorts) (s : Fin nsorts) (shape : Frontend.CtorShape nsorts) :
    Except Failure FPreCtor := do
  let ⟨fields, _, _⟩ ← ordinaryFields F L table lps hints accel nparams params shape
    shape.ords.length le_rfl
  let recursive ← shape.recs.mapM fun rf => do
    pure (← preRecField F L table lps hints accel nparams sd shape.ords shape.ords.length
      (params ++ fields) rf).val
  let tis ← shape.resultIndices.mapM fun i => do
    pure (← translate F L table lps hints accel (params ++ fields)
      (Frontend.fieldScope shape.ords nparams (shape.ords.length + shape.recs.length)
        (nparams + shape.ords.length)) i).val
  unless tis.length = (sd s).indicesRev.length do throw (.reject .arity)
  pure { ordinary := fields, recursive := recursive.toArray, targetIndices := tis.toArray }

def ctorSigOf {nsorts : Nat} (shape : Frontend.CtorShape nsorts) : CtorSig nsorts :=
  let arity := (shape.recs.map (·.bindersRev.length)).toArray
  let target := (shape.recs.map (·.target)).toArray
  { nfields := shape.ords.length
    nrecFields := shape.recs.length
    recursiveArity := fun r => arity[r.val]'(by simp [arity])
    recursiveTarget := fun r => target[r.val]'(by simp [target]) }

def indSigOf (nlevels nparams nsorts : Nat) (sd : Fin nsorts → Frontend.SortData nsorts) : IndSig :=
  let nindices := Array.ofFn fun s => (sd s).indicesRev.length
  let ctors := Array.ofFn fun s => ((sd s).shapes.map ctorSigOf).toArray
  { nlevels, nparams, nsorts
    nindices := fun s => nindices[s.val]'(by simp [nindices])
    nctors := fun s => (ctors[s.val]'(by simp [ctors])).size
    ctors := fun s c => (ctors[s.val]'(by simp [ctors]))[c.val]'c.isLt }

def analyzeBlock (types : List Export.InductiveType) (ctors : List Export.Constructor)
    (recNames : List Name) (defs : Export.Definitions := ∅) : Except Failure FBlockResult := do
  if hpos : 0 < types.length then
    let first := types[0]
    if types.any (·.isUnsafe) then throw (.decline .unsafe)
    if types.any (·.numNested != 0) then throw (.decline .nested)
    if recNames.length != types.length then throw (.reject .arity)
    let lps := first.levelParams
    if lps.eraseDups.length != lps.length then throw (.reject .duplicateLevelParam)
    if types.any (·.levelParams != lps) then throw (.reject .shape)
    if ctors.any (·.levelParams != lps) then throw (.reject .shape)
    if types.any (·.numParams != first.numParams) then throw (.reject .arity)
    let allCtorNames := types.flatMap (·.ctors)
    if ctors.length != allCtorNames.length then throw (.reject .shape)
    if allCtorNames.any fun cname => (ctors.find? (·.name == cname)).isNone then
      throw (.reject .shape)
    let sortIdx? : Name → Option (Fin types.length) := fun nm =>
      types.findFinIdx? (·.name == nm)
    let (paramBindersRev, _) ← Frontend.takeForallsRevWhnf defs first.numParams first.type
    let sd ← Fin.mapM fun s : Fin types.length => do
      let ty := types[s.val]
      let (_, rest) ← Frontend.takeForallsRevWhnf defs first.numParams ty.type
      let (indicesRev, .sort level) ← Frontend.takeForallsRevWhnf defs ty.numIndices rest
        | throw (.reject .shape)
      let shapes ← ty.ctors.mapM fun cname => do
        let some c := ctors.find? (·.name == cname) | throw (.reject .shape)
        Frontend.shapeCtor defs sortIdx? lps paramBindersRev.length ty.numIndices s c.type
      pure ({ indicesRev, level, shapes } : Frontend.SortData types.length)
    let levels ← Fin.mapM fun s : Fin types.length =>
      (·.val) <$> translateLevel lps (sd s).level
    let level := levels ⟨0, hpos⟩
    let some rawLevels := Fin.mapM fun s : Fin types.length => (levels s).toRaw lps.length
      | throw (.reject .unknownLevelParam)
    if ∃ s, (rawLevels s).normalize ≠ (rawLevels ⟨0, hpos⟩).normalize then throw (.reject .shape)
    let nparams := paramBindersRev.length
    let ⟨params, hparamsSize, hparamsWF⟩ ← buildFrom F L table lps hints accel #[] Scope.empty
      paramBindersRev
    let indices ← Fin.mapM fun s : Fin types.length => do
      pure (← buildFrom F L table lps hints accel params (Scope.id nparams) (sd s).indicesRev).val
    let preCtors ← Fin.mapM fun s : Fin types.length =>
      Fin.mapM fun c : Fin (sd s).shapes.length =>
        preCtorOf F L table lps hints accel nparams params sd s ((sd s).shapes[c.val]'c.isLt)
    pure {
      ι := indSigOf lps.length nparams types.length sd
      pre := {
        params
        indices := Array.ofFn indices
        level
        ctors := Array.ofFn fun s => Array.ofFn (preCtors s) }
      sortNames := types.map (·.name)
      ctorNames := types.map (·.ctors)
      metaOrders := List.ofFn fun s : Fin types.length =>
        (sd s).shapes.map fun shape => Frontend.metaOrderOf shape }
  else throw (.reject .shape)

end Metalean.FastChecker
