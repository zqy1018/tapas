import Tapas.Applications.Monad.EffectInference
import Tapas.LogicalRelation.Capabilities
import Tapas.Parametricity.Fixpoint

/-!
Proof-producing translation of a capability-polymorphic program. Constants are
handled by registered theorems; only reducible wrappers and instance forwarding
are unfolded automatically. Recursive definitions use functional induction;
least fixpoints additionally require an explicit admissibility premise.
-/

namespace Tapas.Parametricity

open Lean Meta Elab Command Tapas.LogicalRelation

initialize parametricExt : SimplePersistentEnvExtension (Name × Name)
    (NameMap (Array Name)) ← registerSimplePersistentEnvExtension {
  addEntryFn := fun s (source, proof) =>
    let proofs := (s.find? source).getD #[]
    s.insert source (if proofs.contains proof then proofs else proofs.push proof)
  addImportedFn := fun entries => entries.foldl (fun s es =>
    es.foldl (fun s (source, proof) =>
      let proofs := (s.find? source).getD #[]
      s.insert source (if proofs.contains proof then proofs else proofs.push proof)) s) {}
}

/-- Look up program translations, including hand-written and imported rules. -/
def getParametricRules (env : Environment) (source : Name) : Array Name :=
  (parametricExt.getState env |>.find? source).getD #[]

/-- Register a checked proof whose conclusion relates two applications of `source`.
Its premises are checked when it is applied; no equivalence or functionality law
is required of the relation. -/
def registerParametric (source proof : Name) : MetaM Unit := do
  discard <| getConstInfo source
  let info ← getConstInfo proof
  unless ← isProp info.type do
    throwError "parametricity: {proof} is not a proof"
  forallTelescope info.type fun _ body => do
    let args := body.getAppArgs
    unless body.getAppFn.isFVar && args.size == 3 &&
        args[1]!.getAppFn.constName? == some source &&
        args[2]!.getAppFn.constName? == some source do
      throwError "parametricity: {proof} must conclude `R ({source} ...) ({source} ...)`"
  modifyEnv fun env => parametricExt.addEntry env (source, proof)

private structure ProofContext where
  sourceMonad : Expr
  targetMonad : Expr
  relation : Expr

private def independent (ctx : ProofContext) (e : Expr) : Bool :=
  !ctx.sourceMonad.occurs e && !ctx.targetMonad.occurs e

private def mkRelation (ctx : ProofContext) (left right : Expr) : MetaM Expr :=
  operationRelation #[⟨ctx.sourceMonad, ctx.targetMonad, ctx.relation⟩] left right

private def endpoints? (ctx : ProofContext) (type : Expr) : Option (Expr × Expr) := do
  let args := type.getAppArgs
  if (type.getAppFn == ctx.relation || type.isAppOf ``Eq) && args.size == 3 then
    some (args[1]!, args[2]!)
  else none

/-- Remove the `let`/`have` binders at the head of `e`. -/
private partial def zetaHead (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => zetaHead (body.instantiate1 value)
  | .mdata _ e => zetaHead e
  | e => e

/-- Rules contributed by a hypothesis `self : type`: `self` when it concludes the computation
relation, otherwise the operation projections of a capability relation, also under families.
Binders are looked through, including the `have`s in functional induction hypotheses. The
flag reports whether `self` concludes the computation relation. -/
private partial def hypothesisRules (ctx : ProofContext) (self type : Expr)
    (xs : Array Expr := #[]) : MetaM (Bool × Array Expr) :=
  forallTelescope type fun ys body => do
    let xs := xs ++ ys
    let body := zetaHead body
    if body.isForall then
      return ← hypothesisRules ctx self body xs
    if body.getAppFn == ctx.relation then return (true, #[self])
    if let some name := body.getAppFn.constName? then
      if let some info := getEffectRelation? (← getEnv) name.getPrefix then
        if info.relation == name then
          let applied := mkAppN self xs
          let fields ← info.fields.mapM fun field => do
            mkLambdaFVars xs (← mkProjection applied field)
          return (false, fields)
    return (false, #[])

/-- Relational hypotheses contribute their operation projections, also under families. -/
private def localRules (ctx : ProofContext) : MetaM (Array Expr) := do
  let mut rules := #[]
  let mut hypotheses := #[]
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if ← isProp type then
      let (isHypothesis, more) ← hypothesisRules ctx decl.toExpr type
      if isHypothesis then hypotheses := hypotheses ++ more
      else rules := rules ++ more
  -- Prefer the proof of a shared local function to reproving its expanded body.
  return hypotheses ++ rules

/-- `ite` or `dite`, possibly applied to further arguments when a branch selects a function. -/
private def iteHead? (e : Expr) : Option Name :=
  if e.getAppNumArgs < 5 then none
  else if e.isAppOf ``ite then some ``ite
  else if e.isAppOf ``dite then some ``dite
  else none

private def normalizeHead (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isLet || (iteHead? e).isSome || (← matchMatcherApp? e (alsoCasesOn := true)).isSome then
    return e
  if let some name := e.getAppFn.constName? then
    unless (getParametricRules (← getEnv) name).isEmpty do return e
  -- Ordinary definitions are opaque to proof search, except exact forwarding
  -- wrappers such as `withTheReader`: a field applied only to original binders.
  let e ← if let some name := e.getAppFn.constName? then do
      if let .defnInfo info ← getConstInfo name then
        let forwards ← lambdaTelescope info.value fun xs body => do
          let some field := body.getAppFn.constName? | return false
          return (← getProjectionFnInfo? field).isSome && body.getAppArgs.all xs.contains
        if forwards then
          pure ((info.value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta e.getAppArgs)
        else pure e
      else pure e
    else pure e
  withTransparency .instances <| withConfig (fun c => { c with zeta := false, zetaDelta := false }) <|
    whnf e

private def checkSharedDiscriminants (ctx : ProofContext) (left right : Expr) : MetaM Bool := do
  if let some head := iteHead? left then
    if iteHead? right == some head then
      let a := left.getAppArgs[1]!
      let b := right.getAppArgs[1]!
      unless independent ctx a && independent ctx b && (← isDefEq a b) do
        throwError "parametricity: condition depends on the monad or differs between interpretations"
      return true
  if let some l ← matchMatcherApp? left (alsoCasesOn := true) then
    if let some r ← matchMatcherApp? right (alsoCasesOn := true) then
      unless l.discrs.size == r.discrs.size do
        throwError "parametricity: match discriminants differ between interpretations"
      for a in l.discrs, b in r.discrs do
        unless independent ctx a && independent ctx b && (← isDefEq a b) do
          throwError "parametricity: match discriminant depends on the monad or differs between interpretations"
      return true
  return false

/-- Let variables among match discriminants, following chains of let variables. `split`
cannot generalize a let variable, so their values are exposed before splitting. -/
private def letDiscriminants (discrs : Array Expr) : MetaM (Array FVarId) := do
  let mut lets := #[]
  for discr in discrs do
    let mut current := discr.consumeMData
    repeat
      let .fvar fvarId := current | break
      let some value := (← fvarId.getDecl).value? | break
      lets := lets.push fvarId
      current := value.consumeMData
  return lets

/-- `let x₁ := v₁; …; let xₙ := vₙ; b` from `fun x₁ … xₙ => b` and closed values `vᵢ`. -/
private def lambdasToLets (e : Expr) (values : Array Expr) : Expr :=
  go e 0
where
  go (e : Expr) (i : Nat) : Expr :=
    if h : i < values.size then
      match e with
      | .lam name type body _ => .letE name type values[i] (go body (i + 1)) false
      | _ => e
    else e

mutual
  private partial def provePair (ctx : ProofContext) (left right : Expr) : MetaM Expr := do
    let type ← mkRelation ctx left right
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    proveGoal ctx goal.mvarId!
    instantiateMVars goal

  private partial def proveGoal (ctx : ProofContext) (goal : MVarId) : MetaM Unit :=
    withIncRecDepth <| goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      if type.isForall then
        let (_, next) ← goal.intro1P
        proveGoal ctx next
        return
      if (← observing? <| withTransparency .instances goal.assumption).isSome then return
      if type.isAppOf ``AdmissibleRel then
        -- Instantiate a caller's admissibility premise before lifting it through
        -- the shared arguments of a recursive function.
        let mut rules := #[]
        for decl in ← getLCtx do
          if ← forallTelescope decl.type fun _ body => pure (body.isAppOf ``AdmissibleRel) then
            rules := rules.push decl.toExpr
        let args := type.getAppArgs
        if let .forallE name dom body bi ← whnf args[0]! then
          if let .forallE _ dom' body' _ ← whnf args[1]! then
            if independent ctx dom && independent ctx dom' && (← isDefEq dom dom') then
              -- Supply the families explicitly: higher-order unification cannot
              -- reliably infer the residual relation for multiple arguments.
              let rule ← withLocalDecl name bi dom fun x => do
                let a := body.instantiate1 x
                let b := body'.instantiate1 x
                let family ← withLocalDeclD `f a fun f =>
                  withLocalDeclD `g b fun g => do
                    mkLambdaFVars #[x, f, g] (← mkRelation ctx f g)
                mkAppOptM ``AdmissibleRel.pointwise
                  #[some dom, some (← mkLambdaFVars #[x] a), some (← mkLambdaFVars #[x] b),
                    none, none, some family]
              rules := rules.push rule
        for rule in rules do
          if (← observing? do
              let subgoals ← withTransparency .instances <| goal.apply rule
              for subgoal in subgoals do proveGoal ctx subgoal).isSome then return
        throwError "parametricity: missing admissibility premise:\n{type}"
      if type.isAppOf ``Eq then
        if (← observing? <| withTransparency .instances goal.refl).isSome then return
      if let some name := type.getAppFn.constName? then
        if let some info := getEffectRelation? (← getEnv) name.getPrefix then
          if info.relation == name then
            -- A helper may require a parent capability whose fields are supplied
            -- by a stronger dictionary relation in the caller's telescope.
            let ctor ← mkConstWithFreshMVarLevels (name ++ `mk)
            for fieldGoal in ← goal.apply ctor do proveGoal ctx fieldGoal
            return
      let some (left₀, right₀) := endpoints? ctx type
        | throwError "parametricity: missing relational premise:\n{type}"
      let left ← normalizeHead left₀
      let right ← normalizeHead right₀
      let goal ← if left != left₀ || right != right₀ then
          goal.replaceTargetDefEq (← mkRelation ctx left right)
        else pure goal
      -- Introduce matching lets before applying rules, so continuations and their
      -- relation proofs remain shared instead of being zeta-expanded at each use.
      if let .letE name lt lv lb nondep := left then
        if let .letE _ rt rv rb _ := right then
          if independent ctx lt && independent ctx rt &&
              (← withTransparency .instances <| isDefEq lv rv) then
            withLetDecl name lt lv fun x => do
              let proof ← provePair ctx (lb.instantiate1 x) (rb.instantiate1 x)
              goal.assign (← mkLetFVars #[x] proof (generalizeNondepLet := false))
          else
            let valueProof ← provePair ctx lv rv
            let targetName := name.appendAfter "'"
            let relationName := name.appendAfter "_rel"
            -- As in Loom's `shareJoinPoint`, prove the body for opaque local computations
            -- related by a hypothesis. A jump such as `__do_jp ()` cannot be unfolded, so
            -- only the hypothesis closes it and the continuation proof is shared.
            let opaqueBody? ← withLocalDeclD name lt fun x =>
              withLocalDeclD targetName rt fun y => do
                let l := lb.instantiate1 x
                let r := rb.instantiate1 y
                -- A dependent `let` body may need the value definitionally.
                unless nondep do
                  unless (← isTypeCorrect l) && (← isTypeCorrect r) do return none
                withLocalDeclD relationName (← mkRelation ctx x y) fun h => do
                  let proof ← provePair ctx l r
                  return some (← mkLambdaFVars #[x, y, h] proof)
            if let some body := opaqueBody? then
              goal.assign (lambdasToLets body #[lv, rv, valueProof])
            else
              withLetDecl name lt lv fun x =>
                withLetDecl targetName rt rv fun y => do
                  withLetDecl relationName (← mkRelation ctx x y) valueProof fun h => do
                    let proof ← provePair ctx (lb.instantiate1 x) (rb.instantiate1 y)
                    goal.assign (← mkLetFVars #[x, y, h] proof (generalizeNondepLet := false))
          return
      if ← checkSharedDiscriminants ctx left right then
        let mut target ← mkRelation ctx left right
        if let some app ← matchMatcherApp? left (alsoCasesOn := true) then
          let lets ← letDiscriminants app.discrs
          unless lets.isEmpty do target ← zetaDeltaFVars target lets
        let normalized ← goal.replaceTargetDefEq target
        if let some branches ← splitTarget? normalized then
          for branch in branches do
            -- A branch contradicting its context, e.g. a functional induction case
            -- hypothesis, needs no relation proof.
            let contradictory ← branch.contradictionCore
              { useDecide := false, emptyType := false, genDiseq := true }
            unless contradictory do proveGoal ctx branch
          return
        throwError "parametricity: unsupported match elimination; register a translation for the enclosing helper"
      let mut rules := #[]
      if let some source := left.getAppFn.constName? then
        if right.getAppFn.constName? == some source then
          for name in getParametricRules (← getEnv) source do
            rules := rules.push (← mkConstWithFreshMVarLevels name)
      rules := rules ++ (← localRules ctx)
      let mut failure? := none
      for rule in rules do
        let saved ← saveState
        if let some subgoals ← observing? <| withTransparency .instances <|
            goal.apply rule { newGoals := .all, synthAssignedInstances := false } then
          try
            for subgoal in subgoals do proveGoal ctx subgoal
            return
          catch ex =>
            failure? := some ex
            saved.restore
      if let some ex := failure? then throw ex
      if let some name := left.getAppFn.constName? then
        throwError "parametricity: no applicable translation for {name}; use `derive_parametric {name}` or `register_parametric {name} using theoremName`"
      throwError "parametricity: unsupported term or missing relation:\n{left}\nand\n{right}"
end

/-- Ensure relation interfaces for capability parameters, including indexed families. -/
private def ensureCapabilityRelation (m : Expr) (type : Expr) : MetaM Unit := do
  forallTelescope type fun _ body => do
    let some capability := body.getAppFn.constName?
      | return
    unless isClass (← getEnv) capability do return
    if (getEffectRelation? (← getEnv) capability).isSome then return
    let args := body.getAppArgs
    let selected := args.findIdx? (· == m)
    let some idx := selected | return
    let info ← getConstInfo capability
    forallTelescope info.type fun params _ => do
      deriveEffectRelation capability (some (← params[idx]!.fvarId!.getUserName))

/-- Order structures and monotonicity witnesses are separate semantic parameters,
not effect dictionaries whose operations should be related. -/
private def isOrderParameter (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body =>
    pure (body.isAppOf ``Order.CCPO || body.isAppOf ``Order.MonoBind)

/-- The recursive block of `source`, in the order of its induction motives, and its fixed
parameter analysis. -/
private def recursionBlock (source : Name) : MetaM (Array Name × FixedParamPerms) := do
  let env ← getEnv
  if let some info := Structural.eqnInfoExt.find? env source then
    return (info.declNames, info.fixedParamPerms)
  if let some info := WF.eqnInfoExt.find? env source then
    return (info.declNames, info.fixedParamPerms)
  throwError "parametricity: missing recursion information for {source}; register a hand-written translation"

/-- Arguments for the parameters a functional induction principle keeps before its motives.
They are a subsequence of the fixed parameters, matched in order by name and type. -/
private def keptInductionArgs (inductName : Name) (type : Expr) (numKept : Nat)
    (fixed : Array Expr) : MetaM (Array Expr) := do
  let mut type := type
  let mut kept := #[]
  let mut next := 0
  for _ in [:numKept] do
    let .forallE name dom body _ := type
      | throwError "parametricity: unexpected induction principle {inductName}"
    let mut found? := none
    for byName in [true, false] do
      let mut i := next
      while found?.isNone && i < fixed.size do
        let candidate := fixed[i]!
        let candidateName ← candidate.fvarId!.getUserName
        if !byName || candidateName.eraseMacroScopes == name.eraseMacroScopes then
          if ← isDefEq (← inferType candidate) dom then
            found? := some (i, candidate)
        i := i + 1
    let some (i, arg) := found?
      | throwError "parametricity: cannot match the parameters of {inductName} with the fixed parameters of the definition"
    kept := kept.push arg
    next := i + 1
    type := body.instantiate1 arg
  return kept

/-- The induction motive for `member`, over its varying parameters: related calls of
`member`, quantifying over related copies of monad-dependent varying parameters. -/
private def inductionMotive (ctx : ProofContext) (member : Name) (perm : FixedParamPerm)
    (fixedLeft fixedRight : Array Expr) (changeLevels : Expr → Expr) : MetaM Expr := do
  let info ← getConstInfo member
  forallTelescope (← perm.instantiateForall info.type fixedLeft) fun ys _ => do
    let rec go (i : Nat) (rightYs binders : Array Expr) : MetaM Expr := do
      if h : i < ys.size then
        let y := ys[i]
        let type ← inferType y
        if !ctx.sourceMonad.occurs type then
          go (i + 1) (rightYs.push y) binders
        else
          let decl ← y.fvarId!.getDecl
          let rightType := changeLevels
            (type.replaceFVars (fixedLeft ++ ys.extract 0 i) (fixedRight ++ rightYs))
          withLocalDecl (decl.userName.appendAfter "'") decl.binderInfo rightType fun y' => do
            let premise ← mkRelation ctx y y'
            withLocalDeclD (decl.userName.appendAfter "_rel") premise fun hy =>
              go (i + 1) (rightYs.push y') (binders ++ #[y', hy])
      else
        let left := mkAppN (mkConst member (info.levelParams.map mkLevelParam))
          (perm.buildArgs fixedLeft ys)
        let right ← mkAppOptM member ((perm.buildArgs fixedRight rightYs).map some)
        let body ← mkRelation ctx left (← instantiateMVars right)
        mkLambdaFVars ys (← mkForallFVars binders body)
    go 0 #[] #[]

/-- Introduce a case of a functional induction principle, unfold the recursive call on both
sides once, and relate the unfolded bodies. Induction hypotheses are local rules. -/
private def proveInductionCase (ctx : ProofContext) (members : Array Name) (goal : MVarId) :
    MetaM Unit := do
  let (_, goal) ← goal.intros
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    let some member := (endpoints? ctx type).bind (·.1.getAppFn.constName?)
      | throwError "parametricity: unexpected induction case:{indentExpr type}"
    unless members.contains member do
      throwError "parametricity: unexpected induction case:{indentExpr type}"
    proveGoal ctx (← unfoldTarget goal member)

/-- Prove `R (source params) (source targets)` with the functional induction principle of the
recursive block `members`. `hyps` holds the relation hypothesis of each monad-dependent
parameter; its related copy is the corresponding entry of `targets`. -/
private def proveByInduction (ctx : ProofContext) (source : Name) (members : Array Name)
    (perms : FixedParamPerms) (params targets : Array Expr) (hyps : Array (Option Expr))
    (changeLevels : Expr → Expr) : MetaM Expr := do
  let some memberIdx := members.findIdx? (· == source)
    | throwError "parametricity: {source} is missing from its recursive block"
  let perm := perms.perms[memberIdx]!
  unless perm.size == params.size do
    throwError "parametricity: unsupported parameters of the recursive definition {source}"
  let some inductName ← getFunInduct? (unfolding := false) (cases := false) source
    | throwError "parametricity: no functional induction principle for {source}; register a hand-written translation"
  let inductInfo ← getConstInfo inductName
  -- The conclusion applies the motive of `source`; the motives are consecutive, in block order.
  let (motivePos, numBinders) ← forallTelescope inductInfo.type fun xs body => do
    let some pos := xs.findIdx? (· == body.getAppFn)
      | throwError "parametricity: unexpected induction principle {inductName}"
    return (pos, xs.size)
  unless memberIdx ≤ motivePos do
    throwError "parametricity: unexpected induction principle {inductName}"
  let numKept := motivePos - memberIdx
  let fixedLeft := perm.pickFixed params
  let fixedRight := perm.pickFixed targets
  let kept ← keptInductionArgs inductName inductInfo.type numKept fixedLeft
  let motives ← members.mapIdxM fun j member =>
    inductionMotive ctx member perms.perms[j]! fixedLeft fixedRight changeLevels
  let principle := mkAppN (mkConst inductName (inductInfo.levelParams.map mkLevelParam))
    (kept ++ motives)
  let varying := (List.range params.size).filter (!perm.isFixed ·) |>.toArray
  let numCases := numBinders - numKept - members.size - varying.size
  let mut type ← inferType principle
  let mut cases := #[]
  for _ in [:numCases] do
    let .forallE _ caseType body _ := type
      | throwError "parametricity: unexpected induction principle {inductName}"
    let goal ← mkFreshExprSyntheticOpaqueMVar (← Core.betaReduce caseType)
    proveInductionCase ctx members goal.mvarId!
    let proof ← instantiateMVars goal
    cases := cases.push proof
    type := body.instantiate1 proof
  let related := varying.foldl (init := #[]) fun acc i =>
    match hyps[i]! with
    | some hyp => acc ++ #[targets[i]!, hyp]
    | none => acc
  return mkAppN principle (cases ++ varying.map (params[·]!) ++ related)

/-- Expose only the compiler's wrappers around a single least fixpoint. In particular,
do not unfold `Order.fix` or replace it with its unfolding equation. -/
private def proveByFixpoint (ctx : ProofContext) (info : PartialFixpoint.EqnInfo)
    (left right : Expr) : MetaM Expr := do
  let expose (e : Expr) := deltaExpand e fun n => n == info.declName || n == info.declNameNonRec
  let left ← expose left
  let right ← expose right
  let ls := left.getAppArgs
  let rs := right.getAppArgs
  unless left.isAppOf ``Order.fix && right.isAppOf ``Order.fix &&
      ls.size >= 4 && ls.size == rs.size do
    throwError "parametricity: unsupported least-fixpoint representation of {info.declName}"
  let args := ls.extract 4 ls.size
  for l in args, r in rs.extract 4 rs.size do
    unless independent ctx (← inferType l) && independent ctx (← inferType r) &&
        (← isDefEq l r) do
      throwError "parametricity: partial_fixpoint currently requires shared, monad-independent recursive arguments"
  withLocalDeclD `recur ls[0]! fun f =>
    withLocalDeclD `recur' rs[0]! fun g => do
      let related ← mkRelation ctx f g
      let relation ← mkLambdaFVars #[f, g] related
      let hadmGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``AdmissibleRel
        #[some ls[0]!, some rs[0]!, some ls[1]!, some rs[1]!, some relation])
      proveGoal ctx hadmGoal.mvarId!
      let hstep ← withLocalDeclD `recur_rel related fun h => do
        let proof ← provePair ctx (mkApp ls[2]! f) (mkApp rs[2]! g)
        mkLambdaFVars #[f, g, h] proof
      let proof ← mkAppOptM ``fix_rel
        (#[ls[0]!, rs[0]!, ls[1]!, rs[1]!, relation, ls[2]!, rs[2]!,
          ls[3]!, rs[3]!, ← instantiateMVars hadmGoal, hstep].map some)
      return mkAppN proof args

private def deriveMember (source : Name) (block? : Option (Array Name × FixedParamPerms))
    (fixpoint? : Option PartialFixpoint.EqnInfo) :
    MetaM Unit := do
  let .defnInfo info ← getConstInfo source
    | throwError "parametricity: expected a definition with a body: {source}"
  unless info.safety == .safe do
    throwError "parametricity: unsafe or partial definitions are unsupported: {source}"
  let theoremName := source ++ `parametric
  forallTelescope info.type fun params result => do
    let result ← whnf result
    let m := result.getAppFn
    unless params.contains m && result.getAppNumArgs == 1 do
      throwError "parametricity: the result must be `m α` for a monad parameter of {source}"
    let .forallE _ (.sort (.succ u)) (.sort (.succ v)) _ ← whnf (← inferType m)
      | throwError "parametricity: expected a monad parameter of type `Type u → Type v`"
    let mut sharedLevels := collectLevelParams {} (mkSort (.succ u))
    sharedLevels := collectLevelParams sharedLevels result.appArg!
    for param in params do
      if param != m then
        sharedLevels ← sharedComputationLevels #[m] (← inferType param) sharedLevels
    let v' := targetComputationLevel v sharedLevels info.type
    let changeLevels (e : Expr) := match v with
      | .param name => e.instantiateLevelParams [name] [v']
      | _ => e
    let nType ← mkArrow (mkSort (.succ u)) (mkSort (.succ v'))
    withLocalDecl (← m.fvarId!.getUserName <&> (·.appendAfter "'")) .implicit nType fun n => do
      withLocalDeclD `R (← mkAppM ``ComputationRelation #[m, n]) fun rel => do
        let ctx : ProofContext := ⟨m, n, rel⟩
        let rec duplicate (i : Nat) (targets extra : Array Expr) (hyps : Array (Option Expr)) :
            MetaM Unit := do
          if h : i < params.size then
            let param := params[i]
            if param == m then
              duplicate (i + 1) (targets.push n) extra (hyps.push none)
            else
              let type ← inferType param
              if !m.occurs type then
                duplicate (i + 1) (targets.push param) extra (hyps.push none)
              else
                let rightType := changeLevels (type.replaceFVars (params.extract 0 i) targets)
                let decl ← param.fvarId!.getDecl
                withLocalDecl (decl.userName.appendAfter "'") decl.binderInfo rightType fun right => do
                  if ← isOrderParameter type then
                    duplicate (i + 1) (targets.push right) (extra.push right) (hyps.push none)
                    return
                  ensureCapabilityRelation m type
                  let premise ← mkRelation ctx param right
                  withLocalDeclD (decl.userName.appendAfter "_rel") premise fun hyp =>
                    duplicate (i + 1) (targets.push right) (extra ++ #[right, hyp]) (hyps.push hyp)
          else
            let left := mkAppN (mkConst source (info.levelParams.map .param)) params
            let right ← mkAppOptM source (targets.map some)
            let right ← instantiateMVars right
            let finish (adm? : Option Expr) : MetaM Unit := do
              let proof ← if let some fixpoint := fixpoint? then
                  proveByFixpoint ctx fixpoint left right
                else match block? with
                  | none =>
                    let rightBody := info.value.instantiateLevelParams info.levelParams
                      right.getAppFn.constLevels!
                    provePair ctx (info.value.beta params) (rightBody.beta targets)
                  | some (members, perms) =>
                    proveByInduction ctx source members perms params targets hyps changeLevels
              let proof ← instantiateMVars proof
              -- Callers inherit admissibility only when the proof actually uses it.
              let binders := params ++ #[n, rel] ++ extra ++
                adm?.toArray.filter (·.occurs proof)
              let type ← instantiateMVars (← mkForallFVars binders (← mkRelation ctx left right))
              let value ← mkLambdaFVars binders proof (generalizeNondepLet := false)
              if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then
                throwError "parametricity: unresolved variables in the generated theorem"
              let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
              addDecl <| .thmDecl { name := theoremName, levelParams := levels, type, value }
              registerParametric source theoremName
            let admType? ← if ← params.anyM fun p => do isOrderParameter (← inferType p) then
                observing? <| withLocalDecl `α .implicit (mkSort (.succ u)) fun α => do
                  let type ← mkAppM ``AdmissibleRel #[mkApp rel α]
                  mkForallFVars #[α] type
              else pure none
            if let some admType := admType? then
              withLocalDeclD `R_admissible admType fun h => finish (some h)
            else if fixpoint?.isSome then
              throwError "parametricity: partial_fixpoint requires CCPO instances for every result type in both interpretations"
            else finish none
        duplicate 0 #[] #[] #[]

/-- Derive `source`, using least-fixpoint induction or a recursive block's functional induction. -/
private def deriveProgram (source : Name) : MetaM Unit := do
  let .defnInfo _ ← getConstInfo source
    | throwError "parametricity: expected a definition with a body: {source}"
  let fixpoint? := PartialFixpoint.eqnInfoExt.find? (← getEnv) source
  if let some info := fixpoint? then
    unless info.declNames.size == 1 && info.fixpointType.all (fun t => match t with
        | .partialFixpoint => true | _ => false) do
      throwError "parametricity: only single-function partial_fixpoint definitions are supported; register a hand-written translation for {source}"
  let block? ← if fixpoint?.isNone && (← isRecursiveDefinition source) then
      some <$> recursionBlock source
    else pure none
  let members := block?.map (·.1) |>.getD #[source]
  for member in #[source] ++ members.erase source do
    if (← getEnv).contains (member ++ `parametric) then
      throwError "parametricity: declaration already exists: {member ++ `parametric}"
  for member in members do
    deriveMember member block? fixpoint?

/-- Generate and register `p.parametric` from the elaborated body of `p`. Structural
and well-founded recursion derive the whole block; partial fixpoints require admissibility. -/
syntax (name := deriveParametric) "derive_parametric " ident : command

/-- Register a hand-written program translation for subsequent derivations. -/
syntax (name := registerParametricStx) "register_parametric " ident " using " ident : command

@[command_elab deriveParametric]
def elabDeriveParametric : CommandElab := fun stx => do
  let `(derive_parametric $source:ident) := stx | throwUnsupportedSyntax
  withCommandRollback <| liftTermElabM do
    deriveProgram (← realizeGlobalConstNoOverloadWithInfo source)

@[command_elab registerParametricStx]
def elabRegisterParametric : CommandElab := fun stx => do
  let `(register_parametric $source:ident using $proof:ident) := stx | throwUnsupportedSyntax
  withCommandRollback <| liftTermElabM do
    registerParametric (← realizeGlobalConstNoOverloadWithInfo source)
      (← realizeGlobalConstNoOverloadWithInfo proof)

end Tapas.Parametricity
