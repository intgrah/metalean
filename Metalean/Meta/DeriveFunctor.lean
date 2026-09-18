/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public meta import Lean.Elab.PreDefinition.Main
public meta import Lean.Meta.Tactic.Congr

/-!
`@[derive_functor T]` generates `F.functor` for the parameter `T`.
The map is named `F.map` by default.
Optional names, as in `@[derive_functor T mapT functorT]`, allow several maps on the same type.
`via category` selects a category instance explicitly.
Functors used by fields are registered with `@[functor]`.
-/

public meta section

namespace Metalean.Meta.DeriveFunctor

open Lean Meta Elab Term Tactic CategoryTheory

initialize functors : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun s (head, decl) => s.insert head ((s.find? head).getD #[] |>.push decl)
  }

initialize transports : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s decl => s.push decl
  }

initialize maps : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s decl => s.push decl
  }

/-- Register a lemma `(f : X ⟶ Y) → P X … → P Y …` carrying a field along `f` -/
initialize registerBuiltinAttribute {
  name := `transport
  descr := "lemma carrying a field along a morphism in derive_functor"
  add := fun decl stx kind => MetaM.run' do
    Attribute.Builtin.ensureNoArgs stx
    transports.add decl kind
}

def functorApp (name : Name) (f : Expr) (args : Array (Option Expr)) : MetaM Expr := do
  mkAppOptM name (((← inferType f).getAppArgs.push f).map some ++ args)

/-- Register a functor -/
initialize registerBuiltinAttribute {
  name := `functor
  descr := "functor used to map fields in derive_functor"
  add := fun decl stx kind => MetaM.run' do
    Attribute.Builtin.ensureNoArgs stx
    let value ← mkConstWithFreshMVarLevels decl
    forallTelescope (← inferType value) fun args type => do
      unless type.isAppOf ``CategoryTheory.Functor do
        throwError "[functor] expects a categorical functor"
      let f := mkAppN value args
      let obj ← functorApp ``CategoryTheory.Functor.obj f #[]
      forallTelescope (← inferType obj) fun xs _ => do
        let type ← whnf (mkAppN obj xs)
        let some head := type.getAppFn.constName? |
          throwError "[functor] expects an object family headed by a declaration, got {type}"
        functors.add (head, decl) kind
}

def findFunctor (category source target type : Expr) : MetaM Expr := do
  let type ← whnf type
  let candidates := type.getAppFn.constName?.bind (functors.getState (← getEnv)).find? |>.getD #[]
  let mut found : Option Expr := none
  for decl in candidates do
    let value? ← withoutModifyingState <| observing? do
      let value ← mkConstWithFreshMVarLevels decl
      let (args, _, _) ← forallMetaTelescope (← inferType value)
      let f := mkAppN value args
      unless ← isDefEq (← inferType f).getAppArgs[1]! category do failure
      let obj ← functorApp ``CategoryTheory.Functor.obj f #[some source]
      unless ← isDefEq obj type do failure
      let f ← instantiateMVars f
      if f.hasMVar || source.occurs f || target.occurs f then failure
      return f
    if let some f := value? then
      if found.isSome then
        throwError "derive_functor: ambiguous field functor for {type}"
      found := some f
  let some f := found |
    throwError "derive_functor: no registered functor for field type {type}"
  return f

partial def mapField (name : Name) (param : Nat) (recur category source target f value : Expr) :
    MetaM Expr := do
  let type ← inferType value
  if !source.occurs type then return value
  let type ← whnf type
  if let .forallE n domain _ bi := type then
    if source.occurs domain then
      throwError "derive_functor: function domain depends on the mapped object: {domain}"
    return ← withLocalDecl n bi domain fun x => do
      let result ← mapField name param recur category source target f (mkApp value x)
      mkLambdaFVars #[x] result
  if type.isAppOf name then
    let args := type.getAppArgs
    let next := args[param]!
    let (target, f) ← if ← isDefEq next source then pure (target, f) else do
      let shift ← findFunctor category source target next
      unless ← isDefEq (← inferType shift).getAppArgs[3]! category do
        throwError "derive_functor: recursive indices require an endofunctor"
      pure (← functorApp ``CategoryTheory.Functor.obj shift #[some target],
        ← withTransparency .instances <| whnf (← functorApp ``CategoryTheory.Functor.map shift #[none, none, some f]))
    return mkAppN recur (#[next, target, f] ++ args.eraseIdx! param |>.push value)
  if let some functor ← observing? (findFunctor category source target type) then
    let map ← functorApp ``CategoryTheory.Functor.map functor #[none, none, some f]
    let hom ← mkAppM ``CategoryTheory.ConcreteCategory.hom #[map]
    let fn ← mkAppM ``DFunLike.coe #[hom]
    return ← withTransparency .instances <| whnf (mkApp fn value)
  for lemmaName in transports.getState (← getEnv) do
    if let some carried ← observing? (mkAppM lemmaName #[f, value]) then
      return carried
  throwError "derive_functor: no functor or transport lemma for field type {type}"

def mapMatch (info : InductiveVal) (levels : List Level) (params indices : Array Expr) (x motive : Expr)
    (branch : Name → Array Expr → Expr → TermElabM Expr) : TermElabM Expr :=
    withExporting (isExporting := !isPrivateName info.name) do
  let alts ← info.ctors.mapM fun name => do
    let ctor ← getConstInfoCtor name
    let type ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams levels) params
    forallBoundedTelescope type ctor.numFields fun fields result => do
      let patterns := (result.getAppArgs.extract info.numParams result.getAppNumArgs).toList.map
        Lean.Meta.Match.Pattern.inaccessible
      let lhs : Lean.Meta.Match.AltLHS := {
        ref := ← getRef
        fvarDecls := ← fields.toList.mapM fun field => getFVarLocalDecl field
        patterns := patterns ++ [.ctor name levels params.toList (fields.toList.map fun f => .var f.fvarId!)]
      }
      let rhs ← branch name fields result
      let rhs ← if fields.isEmpty then mkFunUnit rhs else mkLambdaFVars fields rhs
      return (lhs, rhs)
  let args := indices.push x
  let matcher ← Term.mkMatcher {
    matcherName := ← withDeclNameForAuxNaming ((← getDeclName?).getD info.name) <| mkAuxDeclName `match
    matchType := ← mkForallFVars args (motive.beta args)
    discrInfos := Array.replicate args.size {}
    lhss := alts.map Prod.fst
  }
  matcher.addMatcher
  mkAppOptM' matcher.matcher ((#[motive] ++ args ++ (alts.map Prod.snd).toArray).map some)

def hom (category source target : Expr) : MetaM Expr := do
  let domain ← inferType source
  let categoryStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct #[some domain, some category]
  let quiver ← mkAppOptM ``CategoryTheory.CategoryStruct.toQuiver #[some domain, some categoryStruct]
  mkAppOptM ``Quiver.Hom #[some domain, some quiver, some source, some target]

def addDefinition (info : InductiveVal) (name : Name) (type value : Expr)
    (attrs : Array Attribute) (recursive := false) : TermElabM Expr := do
  let preDef : PreDefinition := {
    ref := ← getRef
    kind := .def
    binders := mkNullNode #[]
    levelParams := info.levelParams
    modifiers := { attrs }
    declName := name
    type
    value
    termination := .none }
  let docCtx := (← getLCtx, ← getLocalInstances)
  if recursive then addPreDefinitions docCtx #[preDef] {} else addAndCompileNonRec docCtx preDef
  return mkConst name (info.levelParams.map Level.param)

def transportSimps : MetaM Simp.Context := do
  let mut theorems ← getSimpTheorems
  for map in maps.getState (← getEnv) do
    theorems ← theorems.addDeclToUnfold map
  Simp.mkContext (config := { failIfUnchanged := false })
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)

def close (goal : MVarId) : MetaM Bool := do
  let (_, goal) ← goal.intros
  goal.withContext do
    for h in ← getLocalHyps do
      if ← commitWhen (return (← observing? (goal.apply h)) matches some []) then
        return true
    return false

def carry (simps : Simp.Context) (goal : MVarId) : MetaM Unit := do
  let (_, goal) ← goal.intros
  let attempt (goal : MVarId) : MetaM Bool := goal.withContext do
    if ← close goal then return true
    for name in transports.getState (← getEnv) do
      let transport ← mkConstWithFreshMVarLevels name
      if ← commitWhen do
          let some goals ← observing? (goal.apply transport) | return false
          goals.allM close then
        return true
    return false
  if ← attempt goal then return
  let some (_, simplified) := (← simpGoal goal simps).1 | return
  if ← attempt simplified then return
  throwError "derive_functor: no hypothesis or transport proves{indentExpr (← simplified.getType)}"

def deriveMap (info : InductiveVal) (name : Name) (param : Nat) (source : Expr)
    (args : Array Expr) (category : Expr) : TermElabM Expr := do
  let levels := info.levelParams.map Level.param
  withLocalDecl `target .implicit (← inferType source) fun target => do
    let homType ← hom category source target
    withLocalDeclD `f homType fun f => do
      let input := mkAppN (mkConst info.name levels) args
      let outArgs ← args.mapIdxM fun i a => do
        if i == param then pure target
        else if source.occurs (← inferType a) then
          mapField info.name param (mkConst name levels) category source target f a
        else pure a
      let output := mkAppN (mkConst info.name levels) outArgs
      let rest := args.eraseIdx! param
      let outer := #[source, target, f]
      withImplicitBinderInfos (← rest.filterM fun x => return !(← x.fvarId!.getBinderInfo).isInstImplicit) do
        let mapType ← mkForallFVars (outer ++ rest) (← mkArrow input output)
        withDeclName name <| withAuxDecl `map mapType name fun recur => do
          withLocalDeclD `x input fun x => do
            let indices := args.extract info.numParams args.size
            let motive ← mkLambdaFVars (indices.push x) (← mkForallFVars #[target, f] output)
            let rebuild (ctor : Name) (fields : Array Expr) (result : Expr) := do
              let source := result.getAppArgs[param]!
              unless source.isFVar do
                throwError "derive_functor: constructor result must have a variable in the selected position"
              withLocalDecl `target .implicit (← inferType source) fun target₂ => do
                withLocalDeclD `f (← hom category source target₂) fun f₂ => do
                  let params ← (result.getAppArgs.extract 0 info.numParams).mapM fun a => do
                    if a == source then pure target₂
                    else if source.occurs (← inferType a) then
                      mapField info.name param recur category source target₂ f₂ a
                    else pure (a.replaceFVar source target₂)
                  let fields ← fields.mapM fun field => do
                    if field == source then pure target₂ else
                      mapField info.name param recur category source target₂ f₂ field
                  mkLambdaFVars #[target₂, f₂] (mkAppN (mkConst ctor levels) (params ++ fields))
            let body ← if isStructure (← getEnv) info.name then do
              let ctor ← getConstInfoCtor info.ctors.head!
              rebuild ctor.name ((Array.range ctor.numFields).map (mkProj info.name · x)) input
            else
              mapMatch info levels (args.extract 0 info.numParams) indices x motive rebuild
            let body := (← instantiateMVars (mkAppN body #[target, f])).replaceFVar recur
              (mkConst name levels)
            let attr ← `(attr| implicit_reducible)
            let value ← addDefinition info name mapType
              (← mkLambdaFVars (outer ++ rest |>.push x) body)
              (if info.isRec then #[] else
                #[{ name := `implicit_reducible, stx := attr }]) info.isRec
            maps.add name .global
            return value

def shiftSimps (category : Expr) : MetaM (Option Simp.Context) := do
  let mut thms : SimpTheorems := {}
  for (_, names) in (functors.getState (← getEnv)).toArray do
    for name in names do
      let f ← mkConstWithFreshMVarLevels name
      let proofs ← forallTelescope (← inferType f) fun params type => do
        unless (← isDefEq type.getAppArgs[1]! category) && (← isDefEq type.getAppArgs[3]! category) do
          return #[]
        #[``CategoryTheory.Functor.map_id, ``CategoryTheory.Functor.map_comp].mapM fun law => do
          let proof ← functorApp law (mkAppN f params) #[]
          let type ← forallTelescope (← inferType proof) fun args type => do
            let some (_, lhs, rhs) := type.eq? | failure
            let eq ← mkEq (← withTransparency .instances <| whnf lhs)
              (← withTransparency .instances <| whnf rhs)
            mkForallFVars args eq
          mkLambdaFVars params (mkExpectedPropHint proof type)
      for proof in proofs do
        thms ← thms.add (.other (← mkFreshUserName name)) #[] proof
  if thms.lemmaNames.isEmpty then return none
  return some (← Simp.mkContext (config := { failIfUnchanged := false }) (simpTheorems := #[thms]))

partial def proveLaw (goal : MVarId) (category source target : Expr) (law : Name) (ihs : Array Expr) (simps : Option Simp.Context) : MetaM Unit := goal.withContext do
  if (← observing? goal.refl).isSome then return
  let goal? ← if let some simps := simps then do
    pure ((← simpGoal goal simps).1.map Prod.snd)
  else pure (some goal)
  let some goal := goal? | return
  for ih in ihs do
    if (← observing? do
      let [] ← goal.apply ih | failure).isSome then return
  let some (type, lhs, rhs) := (← goal.getType).eq? |
    throwError "derive_functor: expected an equality"
  let type ← whnf type
  if type.isForall then
    let [goal] ← goal.apply (← mkConstWithFreshMVarLevels ``funext) | failure
    let (_, goal) ← goal.intro1P
    proveLaw goal category source target law ihs simps
    return
  if (← observing? do
    let f ← findFunctor category target source type
    let proof := mkAppN (← mkConstWithFreshMVarLevels law) ((← inferType f).getAppArgs.push f)
    check proof
    let (args, binders, _) ← forallMetaTelescope (← inferType proof)
    synthAppInstances `derive_functor goal args binders true false
    let [] ← goal.apply (mkAppN proof args) | failure).isSome then return
  let lhs ← whnf lhs
  let rhs ← whnf rhs
  unless lhs.getAppFn == rhs.getAppFn && (← isConstructorApp lhs) do
    throwError "derive_functor: cannot derive field law{indentExpr (← goal.getType)}"
  let goal ← goal.change (← mkEq lhs rhs)
  for goal in ← goal.congrN 1 do
    proveLaw goal category source target law ihs simps

elab "derive_functor_law " value:ident source:ident target:ident law:ident " (" category:term ")" " [" vars:ident,* "]" : tactic => withMainContext do
  let value ← getFVarId value
  let source ← getFVarId source
  let target ← getFVarId target
  let law ← realizeGlobalConstNoOverloadWithInfo law
  let category ← Tactic.elabTerm category none
  let type ← whnf (← value.getType)
  let info ← getConstInfoInduct type.getAppFn.constName!
  let simps ← shiftSimps category
  let generalized ← if (type.getAppArgs.extract info.numParams type.getAppNumArgs).contains (mkFVar source) then
    vars.getElems.mapM getFVarId
  else pure #[]
  let (reverted, goal) ← (← getMainGoal).revert generalized
  let goals ← goal.induction value (mkRecName type.getAppFn.constName!)
  for goal in goals do
    let (introduced, mvarId) ← goal.mvarId.introNP reverted.size
    let subst := (reverted.zip introduced).foldl (init := goal.subst) fun subst (old, new) =>
      subst.insert old (mkFVar new)
    let ihs ← mvarId.withContext do
      goal.fields.filterM fun field => do isProp (← inferType field)
    proveLaw mvarId category (subst.apply (mkFVar source)) (subst.apply (mkFVar target)) law ihs simps
  replaceMainGoal []

/-- Derive map map_id map_comp -/
def derive (family expected category map : Expr) : TermElabM Expr := do
  let obj ← exprToSyntax family
  let category ← exprToSyntax category
  let map ← exprToSyntax map
  elabTerm (← `(by
    letI := $category
    refine {
      obj := $obj
      map := fun {X Y} f => ↾fun x => $map (source := X) (target := Y) f x
      map_id := ?_
      map_comp := ?_ }
    · intro X
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro x
      derive_functor_law x X X CategoryTheory.Functor.map_id_apply ($category) []
    · intro X Y Z f g
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro x
      derive_functor_law x X Z CategoryTheory.Functor.map_comp_apply ($category) [Y, Z])) (some expected)

/-- Rebind the telescope with the selected parameter replaced -/
partial def withSubstitutedTelescope {α : Type} (args : Array Expr) (param : Nat) (source : Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (substituted : Array Expr) : TermElabM α := do
    if h : i < args.size then
      if i == param then go (i + 1) (substituted.push source)
      else
        let arg := args[i]
        let type := (← inferType arg).replaceFVars (args.extract 0 i) substituted
        withLocalDecl (← arg.fvarId!.getUserName) (← arg.fvarId!.getBinderInfo) type fun x =>
          go (i + 1) (substituted.push x)
    else k substituted
  go 0 #[]

/-- Derive the map of a family whose indices change -/
def deriveTransport (info : InductiveVal) (name : Name) (param : Nat) (source : Expr)
    (args : Array Expr) (category : Expr) : TermElabM Unit := do
  let levels := info.levelParams.map Level.param
  withLocalDecl `target .implicit (← inferType source) fun target => do
    withLocalDeclD `f (← hom category source target) fun f => do
      let input := mkAppN (mkConst info.name levels) args
      let outArgs ← args.mapIdxM fun i a => do
        if i == param then pure target
        else if source.occurs (← inferType a) then
          mapField info.name param (mkConst name levels) category source target f a
        else pure a
      let output := mkAppN (mkConst info.name levels) outArgs
      let rest := args.eraseIdx! param
      withImplicitBinderInfos (← rest.filterM fun x =>
          return !(← x.fvarId!.getBinderInfo).isInstImplicit) do
        let type ← mkForallFVars (#[source, target, f] ++ rest) (← mkArrow input output)
        let proof ← mkFreshExprSyntheticOpaqueMVar type
        let (binders, goal) ← proof.mvarId!.intros
        let simps ← transportSimps
        let branches ← goal.induction binders.back! (mkRecName info.name)
        for branch in branches, ctorName in info.ctors.toArray do
          let (_, goal) ← branch.mvarId.intros
          let ctor ← mkConstWithFreshMVarLevels ctorName
          let premises ← match ← observing? (goal.apply ctor) with
            | some premises => pure premises
            | none =>
              let some (_, simplified) := (← simpGoal goal simps).1 | pure []
              simplified.apply ctor
          premises.forM fun premise => liftM (carry simps premise)
        addDecl (.thmDecl {
          name
          levelParams := info.levelParams
          type
          value := ← instantiateMVars proof })

/-- Derive at one parameter with others constant -/
def deriveAt (info : InductiveVal) (args : Array Expr) (param : Nat)
    (mapName functorName : Name) (category? : Option Expr) : TermElabM Unit := do
  let parameter := args[param]!
  let carried ← (args.eraseIdx! param).anyM fun arg => return parameter.occurs (← inferType arg)
  let domain ← inferType parameter
  withLocalDecl `source .implicit domain fun source => do
    if carried then
      let category ← match category? with
        | some category => pure category
        | none => do
          let category ← synthInstance (mkApp (mkConst ``CategoryTheory.Category
            [← mkFreshLevelMVar, ← getDecLevel domain]) domain)
          instantiateMVars category
      withSubstitutedTelescope args param source fun args =>
        deriveTransport info mapName param source args category
      transports.add mapName .global
      return
    let args := args.set! param source
    let family ← mkLambdaFVars #[source]
      (mkAppN (mkConst info.name (info.levelParams.map Level.param)) args)
    let codomain ← forallTelescope (← inferType family) fun _ type => pure type
    let type ← mkAppOptM ``CategoryTheory.Functor #[some domain, category?, some codomain, none]
    let category := type.getAppArgs[1]!
    let map ← deriveMap info mapName param source
      args category
    let value ← withDeclName functorName do
      let value ← derive family type category map
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value
    let params := args.eraseIdx! param
    discard <| addDefinition info functorName
      (← mkForallFVars params type) (← mkLambdaFVars params value)
      #[{ name := `reducible, stx := ← `(attr| reducible) },
        { name := `functor, stx := ← `(attr| functor) }]

syntax (name := deriveFunctorAttr) "derive_functor " ident (ident ident)? (" via " ident)? : attr

initialize registerBuiltinAttribute {
  name := `deriveFunctorAttr
  descr := "generate a map and functor for the selected parameter"
  applicationTime := .afterCompilation
  add := fun name stx _ => MetaM.run' <| TermElabM.run' <| withoutErrToSorry <|
      withExporting (isExporting := !isPrivateName name) do
    let `(attr| derive_functor $parameter $[$mapName $functorName]? $[via $via?]?) := stx |
      throwUnsupportedSyntax
    let mapName := name ++ (mapName.map (·.getId) |>.getD `map)
    let functorName := name ++ (functorName.map (·.getId) |>.getD `functor)
    let category? ← via?.mapM fun id => do mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverloadWithInfo id)
    let info ← getConstInfoInduct name
    let recursor ← getConstInfoRec (mkRecName name)
    unless recursor.numMotives == 1 do
      throwError "derive_functor: mutual and nested recursion require a supplied functor"
    withLevelNames info.levelParams do
      forallTelescope info.type fun args _ => do
        let some param ← (List.range args.size).findM? fun i => do
          return (← args[i]!.fvarId!.getUserName) == parameter.getId |
          throwError "derive_functor: unknown parameter {parameter}"
        deriveAt info args param mapName functorName category?
}

end Metalean.Meta.DeriveFunctor
