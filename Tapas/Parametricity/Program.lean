import Tapas.Parametricity.Proof

/-!
Generating `p.parametric`, the theorem that a program gives related results in two
interpretations of its representation.

The statement is the relation at `p`'s type, read off by `Tapas.LogicalRelation`;
what this module adds is the proof. Parameters mentioning the representation are
duplicated and related, the rest stay shared, and the body is translated
structurally: applications, `let`, branches, recursion, and constants for which a
translation is registered.

Nothing is assumed about how the program was written. A hand-written definition and
one produced by instance inference take the same path, and a constant with no
translation is an error rather than a guess.

Proof search is implemented in `Tapas.Parametricity.Proof`.
-/

namespace Tapas.Parametricity

open Lean Meta Elab Command
open Utils LogicalRelation

/-- Order structures and monotonicity witnesses are separate semantic parameters,
not interface dictionaries whose operations should be related. -/
private def isOrderParameter (type : Expr) : Bool :=
  [``Order.CCPO, ``Order.MonoBind].any type.getForallBody.isAppOf

/-- The recursive block of `source`, in the order of its induction motives, and its fixed
parameter analysis. -/
private def getRecursionBlock (source : Name) : MetaM (Array Name × FixedParamPerms) := do
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
`member`, quantifying over related copies of representation-dependent varying parameters. -/
private def inductionMotive (ctx : ProofContext) (member : Name) (perm : FixedParamPerm)
    (fixedLeft fixedRight : Array Expr) (changeLevels : Expr → Expr) : MetaM Expr := do
  let info ← getConstInfo member
  let specialize (fn : Expr) (fixed : Array Expr) : MetaM Expr := do
    forallTelescope (← perm.instantiateForall (← inferType fn) fixed) fun ys _ =>
      mkLambdaFVars ys (mkAppN fn (perm.buildArgs fixed ys))
  let fn := mkConst member (info.levelParams.map mkLevelParam)
  let left ← specialize fn fixedLeft
  let right ← specialize (changeLevels fn) fixedRight
  withRelatedTelescope ctx.representations left right ctx.selection
      (fun _ => pure true) (allowDependentBinders := true) fun t => do
    -- The induction principle takes the left arguments first; their related copies
    -- and premises are quantified inside the motive, in telescope order.
    let binders := t.binders.filter (!t.leftArgs.contains ·)
    let body ← relationAt t.representations t.left.headBeta t.right.headBeta t.selection
    mkLambdaFVars t.leftArgs (← mkForallFVars binders body)

/-- Introduce a case of a functional induction principle, unfold the recursive call on both
sides once, and relate the unfolded bodies. Induction hypotheses are local rules. -/
private def proveInductionCase (ctx : ProofContext) (members : Array Name) (goal : MVarId) :
    MetaM Unit := do
  let (_, goal) ← goal.intros
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    let some member := (← endpoints? ctx type).bind (·.1.getAppFn.constName?)
      | throwError "parametricity: unexpected induction case:{indentExpr type}"
    unless members.contains member do
      throwError "parametricity: unexpected induction case:{indentExpr type}"
    proveGoal ctx (← unfoldTarget goal member)

/-- Prove `R (source leftArgs) (source rightArgs)` with the functional induction principle of the
recursive block `members`. `premises` holds the relation hypothesis of each representation-dependent
parameter; its related copy is the corresponding entry of `rightArgs`. -/
private def proveByInduction (ctx : ProofContext) (source : Name) (members : Array Name)
    (perms : FixedParamPerms) (leftArgs rightArgs : Array Expr) (premises : Array (Option Expr))
    (changeLevels : Expr → Expr) : MetaM Expr := do
  let some memberIdx := members.findIdx? (· == source)
    | throwError "parametricity: {source} is missing from its recursive block"
  let perm := perms.perms[memberIdx]!
  unless perm.size == leftArgs.size do
    throwError "parametricity: unsupported parameters of the recursive definition {source}"
  let some inductName ← getFunInduct? (unfolding := false) (cases := false) source
    | throwError "parametricity: no functional induction principle for {source}; register a hand-written translation"
  let inductInfo ← getConstInfo inductName
  let induct := mkConst inductName (inductInfo.levelParams.map mkLevelParam)
  let fixedLeft := perm.pickFixed leftArgs
  let fixedRight := perm.pickFixed rightArgs
  -- Lean records the parameter mapping for single functions; mutual blocks still need matching.
  let kept ← if let some info ← getFunIndInfoForInduct? inductName then
      pure <| (leftArgs.zip info.params).filterMap fun (arg, kind) =>
        if kind == .param then some arg else none
    else
      -- The conclusion applies the motive of `source`; the motives are consecutive, in block order.
      let motivePos := (← getElimExprInfo induct).motivePos
      unless memberIdx ≤ motivePos do
        throwError "parametricity: unexpected induction principle {inductName}"
      keptInductionArgs inductName inductInfo.type (motivePos - memberIdx) fixedLeft
  let motives ← members.mapIdxM fun j member =>
    inductionMotive ctx member perms.perms[j]! fixedLeft fixedRight changeLevels
  let principle := mkAppN induct (kept ++ motives)
  let goal ← mkFreshExprSyntheticOpaqueMVar
    (← Core.betaReduce (mkAppN motives[memberIdx]! (perm.pickVarying leftArgs)))
  for subgoal in ← withTransparency .instances <|
      goal.mvarId!.apply principle { newGoals := .all, synthAssignedInstances := false } do
    proveInductionCase ctx members subgoal
  let related := (perm.pickVarying (rightArgs.zip premises)).foldl (init := #[]) fun acc (arg, premise) =>
    match premise with
    | some hyp => acc ++ #[arg, hyp]
    | none => acc
  return mkAppN (← instantiateMVars goal) related

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
    unless independent ctx.representations (← inferType l) && independent ctx.representations (← inferType r) &&
        (← isDefEq l r) do
      throwError "parametricity: partial_fixpoint currently requires shared, representation-independent recursive arguments"
  withLocalDeclD `recur ls[0]! fun f =>
    withLocalDeclD `recur' rs[0]! fun g => do
      let related ← mkRelation ctx f g
      let relation ← mkLambdaFVars #[f, g] related
      let hadmGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``AdmissibleRel
        #[some ls[0]!, some rs[0]!, some ls[1]!, some rs[1]!, some relation])
      proveGoal ctx hadmGoal.mvarId!
      let hstep ← withLocalDeclD `recur_rel related fun h => do
        let proof ← provePair ctx (mkApp ls[2]! f) (mkApp rs[2]! g) (some relation)
        mkLambdaFVars #[f, g, h] proof
      let proof ← mkAppOptM ``fix_rel
        (#[ls[0]!, rs[0]!, ls[1]!, rs[1]!, relation, ls[2]!, rs[2]!,
          ls[3]!, rs[3]!, ← instantiateMVars hadmGoal, hstep].map some)
      return mkAppN proof args

private def deriveMember (source : Name) (block? : Option (Array Name × FixedParamPerms))
    (fixpoint? : Option PartialFixpoint.EqnInfo) (spec? : Option ReprSpec)
    (name? : Option Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo source
    | throwError "parametricity: expected a definition with a body: {source}"
  unless info.safety == .safe do
    throwError "parametricity: unsafe or partial definitions are unsupported: {source}"
  let theoremName := name?.getD (source ++ `parametric)
  -- Identify the representation and the universes both interpretations must share.
  -- The binders the theorem quantifies over come from the walk below, so this
  -- telescope only makes those decisions.
  let (selection, targetLevels) ← forallTelescope info.type fun params result => do
    let result ← whnf result
    let spec ← match spec? with
      | some spec => pure spec
      | none => do
        let some i ← params.findIdxM? fun param => do
            let bi := (← param.fvarId!.getDecl).binderInfo
            return bi.isImplicit || bi.isStrictImplicit
          | throwError "parametricity: {source} has no implicit parameter; use `(repr := name)` to select a representation"
        pure { indices := #[i] }
    -- A program's representation is one of its own parameters, and **exactly one**
    -- (for now, this is a restriction) of
    -- them must be selected, so a position here names that parameter rather than
    -- marking it. A binder of the same name inside a parameter's type is selected
    -- too, as it is when the parameter is named outright.
    -- FIXME: Picking by name is a bit ad-hoc and could be improved
    let mut names := spec.names
    for i in spec.indices do
      let some param := params[i]?
        | throwError "parametricity: {source} has no parameter at index {i}; there are {params.size}"
      names := names.push (← param.fvarId!.getUserName)
    let selection := RepresentationSelection.markedOrNamed names
    let candidates ← params.filterM fun param => do
      return (← selection.select (← param.fvarId!.getUserName) (← inferType param)).isSome
    let #[repr] := candidates
      | throwError "parametricity: select exactly one representation parameter of {source} with `(repr := name)`"
    let mut sharedLevels ← sharedIndexLevels (← inferType repr)
    sharedLevels ← sharedRepresentationLevels #[repr] result sharedLevels selection
    -- Every dictionary relation the walk below needs has to exist already; one that
    -- does not is reported where it is met, not guessed at here.
    for param in params do
      if param != repr then
        sharedLevels ← sharedRepresentationLevels #[repr] (← inferType param) sharedLevels selection
    return (selection, (renameLevelParams info.levelParams.toArray sharedLevels).toList)
  let changeLevels (e : Expr) := e.instantiateLevelParams info.levelParams targetLevels
  let sourceConst := mkConst source (info.levelParams.map .param)
  withRelatedTelescope #[] sourceConst (mkConst source targetLevels) selection
      (fun dom => return !(isOrderParameter dom)) (allowDependentBinders := true) fun t => do
    let some pair := t.representations[0]?
      | throwError "parametricity: the selected representation was never reached"
    let ctx : ProofContext := ⟨t.representations, selection⟩
    let leftArgs := t.leftArgs
    let rightArgs := t.rightArgs
    let premises := t.premises
    let left := t.left
    let right := t.right
    -- Keep the established binder order: the shared parameters, then the second
    -- interpretation and the base relation, then the duplicates and their premises.
    let mut duplicates := #[]
    for leftArg in leftArgs, rightArg in rightArgs, hyp in premises do
      if leftArg == pair.source || leftArg == rightArg then continue
      duplicates := duplicates.push rightArg
      if let some h := hyp then duplicates := duplicates.push h
    let extra := duplicates
    let finish (adm? : Option Expr) : MetaM Unit := do
      let proof ← if let some fixpoint := fixpoint? then
          proveByFixpoint ctx fixpoint left right
        else match block? with
          | none =>
            let rightBody := info.value.instantiateLevelParams info.levelParams targetLevels
            provePair ctx (info.value.beta leftArgs) (rightBody.beta rightArgs)
          | some (members, perms) =>
            proveByInduction ctx source members perms leftArgs rightArgs premises changeLevels
      let proof ← instantiateMVars proof
      -- Callers inherit admissibility only when the proof actually uses it.
      let binders := leftArgs ++ #[pair.target, pair.relation] ++ extra ++
        adm?.toArray.filter (·.occurs proof)
      let type ← instantiateMVars (← mkForallFVars binders (← mkRelation ctx left right))
      let value ← mkLambdaFVars binders proof (generalizeNondepLet := false)
      if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then
        throwError "parametricity: unresolved variables in the generated theorem"
      let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
      addDecl <| .thmDecl { name := theoremName, levelParams := levels, type, value }
      registerParametric theoremName
    let admType? ← if ← leftArgs.anyM fun p => do pure (isOrderParameter (← inferType p)) then
        observing? <| withSharedIndices pair.source pair.target fun indices _ _ => do
          let type ← mkAppM ``AdmissibleRel #[mkAppN pair.relation indices]
          mkForallFVars indices type
      else pure none
    if let some admType := admType? then
      withLocalDeclD `R_admissible admType fun h => finish (some h)
    else if fixpoint?.isSome then
      throwError "parametricity: partial_fixpoint requires CCPO instances for every result type in both interpretations"
    else finish none

/-- Derive `source`, using least-fixpoint induction or a recursive block's functional induction. -/
private def deriveProgram (source : Name) (spec? : Option ReprSpec) (name? : Option Name) :
    MetaM Unit := do
  let .defnInfo _ ← getConstInfo source
    | throwError "parametricity: expected a definition with a body: {source}"
  let fixpoint? := PartialFixpoint.eqnInfoExt.find? (← getEnv) source
  if let some info := fixpoint? then
    unless info.declNames.size == 1 && info.fixpointType.all (fun t => match t with
        | .partialFixpoint => true | _ => false) do
      throwError "parametricity: only single-function partial_fixpoint definitions are supported; register a hand-written translation for {source}"
  let block? ← if fixpoint?.isNone && (← isRecursiveDefinition source)
    then some <$> getRecursionBlock source
    else pure none
  let members := block?.map (·.1) |>.getD #[source]
  -- Reject giving a custom name for a mutually recursive block with multiple definitions.
  if name?.isSome && members.size > 1 then
    throwError "parametricity: {source} is derived together with {members.erase source}, \
      so `as` cannot name the result"
  for member in #[source] ++ members.erase source do
    let theoremName := if member == source then name?.getD (member ++ `parametric)
      else member ++ `parametric
    if (← getEnv).contains theoremName then
      throwError "parametricity: declaration already exists: {theoremName}"
  for member in members do
    deriveMember member block? fixpoint? spec? name?

/-- Generate and register the parametricity theorem from the elaborated body of `p`. Structural
and well-founded recursion derive the whole block; partial fixpoints require
admissibility. `(repr := ...)` says which parameter to relate, by name or by position;
omitting it selects the first implicit parameter (`{...}` or `⦃...⦄`), skipping explicit
and instance parameters. A definition without an implicit parameter needs an explicit spec.
Selection is resolved separately for each member of a recursive block.

The optional `as name` gives the theorem `name` in the current namespace instead of
`p.parametric`. A mutually recursive block with multiple definitions cannot be given
a custom name with `as name`. -/
syntax (name := deriveParametric) "derive_parametric " ident
  -- `as` is a non-reserved symbol: spelling it `" as "` would put it in the token table and
  -- take the word from every identifier downstream, starting with `∀ (as : List α)` in this
  -- library. It may sit here because the alternative already leads with `derive_parametric`;
  -- see the note in `LogicalRelation/Derive/SelectionFrontend.lean` for where that fails.
  (&" as " ident)?
  (reprSpec)? : command

@[command_elab deriveParametric]
def elabDeriveParametric : CommandElab := fun stx => do
  let `(derive_parametric $source:ident $[as $name:ident]? $[$spec:reprSpec]?) := stx
    | throwUnsupportedSyntax
  let spec? ← spec.mapM elabReprSpec
  let name? ← name.mapM fun name => do pure ((← getCurrNamespace) ++ name.getId)
  liftTermElabM <| commitIfNoEx do
    deriveProgram (← realizeGlobalConstNoOverloadWithInfo source) spec? name?

end Tapas.Parametricity
