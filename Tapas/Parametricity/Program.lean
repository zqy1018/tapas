import Tapas.Parametricity.Proof

/-!
Generating `p.parametric`, the theorem that a program gives related results in two
interpretations of its representation.

For programs without order parameters, the statement is the relation at `p`'s
type, read off by `Tapas.LogicalRelation`; what this module adds is the proof.
Parameters mentioning the representation are
duplicated and related, the rest stay shared, and the body is translated
structurally: applications, `let`, branches, recursion, and constants for which a
translation is registered.

Order parameters (`CCPO` and `MonoBind`) use an extension: the two interpretations
carry their own instances without a relational premise, and proofs using least
fixpoints may additionally require admissibility of the base relation.

Nothing is assumed about how the program was written. A hand-written definition and
one produced by instance inference take the same path, and a constant with no
translation is an error rather than a guess.

Proof search is implemented in `Tapas.Parametricity.Proof`.
-/

namespace Tapas.Parametricity

open Lean Meta Elab Command
open LogicalRelation

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

/-- Arguments for the `numKept` parameters a functional induction principle takes before its
motives. Only fixed parameters can be kept, and Lean drops the ones the principle does not
need, so they are a subsequence of the fixed parameters rather than a prefix: walk the
binders of `type`, and for each one take the next matching entry of `fixed`, preferring a
match on the user name and falling back to the type alone. Used only for a mutual block,
where no `FunIndInfo` records the mapping. -/
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

/-- The induction motive for `member`, over its varying parameters. With the fixed parameters
already applied on both sides, it is

```
fun x₁ ... xₖ =>                           -- the varying parameters, left copies
  ∀ (xᵢ' ...) (hᵢ : Rᵢ xᵢ xᵢ') ...,        -- right copies and premises, where the parameter
                                           -- depends on the representation
    R (member  fixedLeft  x₁ ... xₖ)
      (member' fixedRight x₁' ... xₖ')
```

where `member'` is `member` at the second interpretation. The induction principle applies the
motive to the left arguments, so those and only those are abstracted by the lambda; the right
copies and their premises are quantified inside the body instead, and are supplied again by
the caller once induction has proved the motive. A parameter independent of the representation
is shared, so its left and right copies are the same binder, which therefore stays in the
lambda and is used on both sides. -/
private def inductionMotive (ctx : ProofContext) (member : Name) (perm : FixedParamPerm)
    (fixedLeft fixedRight : Array Expr) (changeLevels : Expr → Expr) : MetaM Expr := do
  let info ← getConstInfo member
  -- `fun ys => member fixed ys`: the fixed parameters applied, leaving a function of the
  -- varying ones alone. `buildArgs` puts the two groups back in the definition's own order.
  let specialize (fn : Expr) (fixed : Array Expr) : MetaM Expr := do
    forallTelescope (← perm.instantiateForall (← inferType fn) fixed) fun ys _ =>
      mkLambdaFVars ys (mkAppN fn (perm.buildArgs fixed ys))
  let fn := mkConst member (info.levelParams.map mkLevelParam)
  -- The two endpoints of the conclusion, `member fixedLeft ...` and `member' fixedRight ...`.
  let left ← specialize fn fixedLeft
  let right ← specialize (changeLevels fn) fixedRight
  -- Walking their shared spine introduces the varying parameters: `xᵢ` alone where the
  -- parameter is shared, `xᵢ`, `xᵢ'` and `hᵢ` where it depends on the representation. Every
  -- binder is relatable here, as order parameters are fixed and were applied above.
  withRelatedTelescope ctx.representations left right ctx.selection
      (fun _ => pure true) (allowDependentBinders := true) fun t => do
    -- Everything the telescope introduced except the left arguments: the right copies and
    -- the premises, in telescope order. A shared binder is a left argument, so it is kept out.
    let binders := t.binders.filter (!t.leftArgs.contains ·)
    -- `R (member fixedLeft x₁ ... xₖ) (member' fixedRight x₁' ... xₖ')`, the relation read off
    -- the result type. The endpoints are the specializing lambdas applied to the arguments.
    let body ← relationAt t.representations t.left.headBeta t.right.headBeta t.selection
    -- `fun x₁ ... xₖ => ∀ (xᵢ' ...) (hᵢ ...), body`.
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
  -- FIXME: Improve this error message?
  unless perm.size == leftArgs.size do
    throwError "parametricity: unsupported parameters of the recursive definition {source}"
  let some inductName ← getFunInduct? (unfolding := false) (cases := false) source
    | throwError "parametricity: no functional induction principle for {source}; register a hand-written translation"
  let inductInfo ← getConstInfo inductName
  let induct := mkConst inductName (inductInfo.levelParams.map mkLevelParam)
  let fixedLeft := perm.pickFixed leftArgs
  let fixedRight := perm.pickFixed rightArgs
  /- `source.induct` has the shape
       `∀ (kept ...) (motive₀ ... motiveₙ₋₁) (case ...) (target ...), motive_memberIdx target ...`
     where the motives are one per member of the block, in block order. `mkAppN` below
     supplies the `kept ++ motives` prefix; the arguments of the kept parameters are the
     ones computed here. They come from the fixed parameters, but not all of them: Lean
     keeps only the parameters the principle actually mentions. -/
  let kept ← if let some info ← getFunIndInfoForInduct? inductName then
      -- For a single function Lean records the mapping: `info.params` is aligned with the
      -- function's arguments and marks each one as kept, a target, or dropped.
      pure <| (leftArgs.zip info.params).filterMap fun (arg, kind) =>
        if kind == .param then some arg else none
    else
      /- A mutual block has no such record, so recover the number of kept parameters from the
      conclusion: it applies the motive of `source`, and the motives are consecutive in block
      order, so the motive's position is `numKept + memberIdx`. The check also guards the
      subtraction. -/
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
  /- Induction proves the motive, which still quantifies over the right copies of
  related varying arguments and their relation proofs. Specialize it at the current
  arguments, e.g. `h x' hx` for `hx : R x x'`. `premises` records those proofs by
  original parameter position, aligned with `rightArgs`; `localRules` only supplies
  proof-search candidates. Reusing this mapping avoids searching for the premises
  again. These are parameter-relation hypotheses, not induction hypotheses. -/
  let related := (perm.pickVarying (rightArgs.zip premises)).foldl (init := #[]) fun acc (arg, premise) =>
    match premise with
    | some hyp => acc ++ #[arg, hyp]
    | none => acc
  return mkAppN (← instantiateMVars goal) related

/-- Expose only the compiler's wrappers around a single least fixpoint. In particular,
do not unfold `Order.fix` or replace it with its unfolding equation. -/
private def proveByFixpoint (ctx : ProofContext) (info : PartialFixpoint.EqnInfo)
    (left right : Expr) : MetaM Expr := do
  -- CHECK `expose` looks relatively ad-hoc
  let expose (e : Expr) := deltaExpand e fun n => n == info.declName || n == info.declNameNonRec
  let left ← expose left
  let right ← expose right
  let ls := left.getAppArgs
  let rs := right.getAppArgs
  unless left.isAppOf ``Order.fix && right.isAppOf ``Order.fix &&
      ls.size ≥ 4 && ls.size == rs.size do
    throwError "parametricity: unsupported least-fixpoint representation of {info.declName}"
  -- `Order.fix` has 4 arguments, so the trailing arguments are for the recursive function itself
  let args := ls.drop 4
  for l in args, r in rs.drop 4 do
    unless independent ctx.representations (← inferType l) && independent ctx.representations (← inferType r) &&
        (← isDefEq l r) do
      throwError "parametricity: partial_fixpoint currently requires shared, representation-independent recursive arguments"
  let (αL, instL, fL, hmonoL) := (ls[0]!, ls[1]!, ls[2]!, ls[3]!)
  let (αR, instR, fR, hmonoR) := (rs[0]!, rs[1]!, rs[2]!, rs[3]!)
  -- The general idea here is to use `fix_rel`. For that to work, the most important
  -- part is to show its last two premises, namely
  -- 1. `AdmissibleRel R`, where `R : αL → αR → Prop`, corresponding to `hadmGoal`
  -- 2. `∀ (x : αL) (y : αR), R x y → R (f x) (g y)`, corresponding to `hstep`
  withLocalDeclD `recur αL fun f =>
    withLocalDeclD `recur' αR fun g => do
      let related ← mkRelation ctx f g
      let relation ← mkLambdaFVars #[f, g] related
      let hadmGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``AdmissibleRel
        #[some αL, some αR, some instL, some instR, some relation])
      proveGoal ctx hadmGoal.mvarId!
      let hstep ← withLocalDeclD `recur_rel related fun h => do
        let proof ← provePair ctx (mkApp fL f) (mkApp fR g) (some relation)
        mkLambdaFVars #[f, g, h] proof
      let proof ← mkAppOptM ``fix_rel
        (#[αL, αR, instL, instR, relation, fL, fR,
          hmonoL, hmonoR, ← instantiateMVars hadmGoal, hstep].map some)
      return mkAppN proof args

-- FIXME: The code here about "exactly one" representation is very weird
private def deriveMember (source : Name) (block? : Option (Array Name × FixedParamPerms))
    (fixpoint? : Option PartialFixpoint.EqnInfo) (spec? : Option ReprSpec)
    (name? : Option Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo source
    | throwError "parametricity: expected a definition with a body: {source}"
  unless info.safety == .safe do
    throwError "parametricity: unsafe or partial definitions are unsupported: {source}"
  let theoremName := name?.getD (source ++ `parametric)
  -- Resolve the frontend's selection and the order-parameter extension.
  let (selection, hasOrderParameters) ← forallTelescope info.type fun params _ => do
    let spec ← match spec? with
      | some spec => pure spec
      | none => do
        let some i ← params.findIdxM? fun param => do
            let bi := (← param.fvarId!.getDecl).binderInfo
            pure <| bi.isImplicit || bi.isStrictImplicit
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
      pure (← selection.select (← param.fvarId!.getUserName) (← inferType param)).isSome
    let #[_] := candidates
      | throwError "parametricity: select exactly one representation parameter of {source} with `(repr := name)`"
    let hasOrderParameters ← params.anyM fun param => do
      pure (isOrderParameter (← inferType param))
    pure (selection, hasOrderParameters)
  let relateBinder (dom : Expr) : MetaM Bool := pure !(isOrderParameter dom)
  let levelParamsArray := info.levelParams.toArray
  let (typeRelation, targetLevels) ← mkTypeRelation info.type levelParamsArray selection
    (relateBinder := relateBinder) (allowDependentBinders := hasOrderParameters)
  let changeLevels (e : Expr) := e.instantiateLevelParamsArray levelParamsArray targetLevels
  let sourceConst := mkConst source (info.levelParams.map .param)
  let targetConst := mkConst source targetLevels.toList
  let statement ← Meta.instantiateLambda typeRelation #[sourceConst, targetConst]
  -- FIXME: Is it possible to merge this `withRelatedTelescope` into `mkTypeRelation`?
  -- Open the endpoints only to build the proof; the statement is fixed above.
  withRelatedTelescope #[] sourceConst targetConst selection relateBinder
      (allowDependentBinders := hasOrderParameters) fun t => do
    let ⟨representations, _, left, right, leftArgs, rightArgs, premises, _⟩ := t
    let some pair := representations[0]?
      | throwError "parametricity: the selected representation was never reached"
    let ctx : ProofContext := ⟨representations, selection⟩
    let finish (adm? : Option Expr) : MetaM Unit := do
      let proof ← if let some fixpoint := fixpoint? then
          proveByFixpoint ctx fixpoint left right
        else match block? with
          | none =>
            let rightBody := info.value.instantiateLevelParamsArray levelParamsArray targetLevels
            provePair ctx (info.value.beta leftArgs) (rightBody.beta rightArgs)
          | some (members, perms) =>
            proveByInduction ctx source members perms leftArgs rightArgs premises changeLevels
      let proof ← instantiateMVars proof
      -- Callers inherit admissibility only when the proof actually uses it.
      let extra := adm?.toArray.filter (·.occurs proof)
      let binders := t.binders ++ extra
      let type ← instantiateMVars (← if extra.isEmpty then pure statement
        else mkForallFVars binders (← mkRelation ctx left right))
      let value ← mkLambdaFVars binders proof (generalizeNondepLet := false)
      if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then
        throwError "parametricity: unresolved variables in the generated theorem"
      let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
      addDecl <| .thmDecl { name := theoremName, levelParams := levels, type, value }
      registerParametric theoremName
    let admType? ← if hasOrderParameters then
        observing? <| withSharedIndices pair.source pair.target fun indices _ _ => do
          let type ← mkAppM ``AdmissibleRel #[mkAppN pair.relation indices]
          mkForallFVars indices type
      else pure none
    if let some admType := admType? then
      withLocalDeclD `R_admissible admType fun h => finish (some h)
    else if fixpoint?.isSome then
      throwError "parametricity: partial_fixpoint requires CCPO instances for every result type in both interpretations"
    else finish none

/-- The auxiliary declarations `source` was split into: constants of its body that are named under
it and have no translation yet. Matchers and internal names are excluded -/
private def auxiliaryDependencies (source : Name) (members : Array Name) : MetaM (Array Name) := do
  let .defnInfo info ← getConstInfo source | return #[]
  let env ← getEnv
  let mut result := #[]
  for name in info.value.getUsedConstants do
    if name == source || !source.isPrefixOf name then continue
    if name.isInternalDetail || members.contains name || result.contains name then continue
    unless (getParametricRules env name).isEmpty do continue
    if (← getMatcherInfo? name).isSome then continue
    let .defnInfo aux ← getConstInfo name | continue
    if aux.safety == .safe then
      result := result.push name
  return result

/-- Derive `source`, using least-fixpoint induction or a recursive block's functional induction.
`derived` are the declarations already being derived further up, which bounds the recursion
through auxiliary declarations. -/
private partial def deriveProgram (source : Name) (spec? : Option ReprSpec) (name? : Option Name)
    (derived : NameSet := {}) : MetaM Unit := do
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
  -- The auxiliary declarations come first, so that the walk over each body finds their
  -- translations registered.
  let mut seen := derived.insert source |>.insertMany members
  for member in members do
    for aux in ← auxiliaryDependencies member members do
      unless seen.contains aux do
        seen := seen.insert aux
        /- A helper the block does not actually need a translation for -- one used only where
        both interpretations agree -- must not fail the block. Its failure is reported through
        the block's own, at the position that needs it. -/
        if (← observing? (deriveProgram aux spec? none seen)).isNone then
          trace[Tapas.Parametricity] "could not derive the auxiliary declaration {aux}"
  for member in members do
    deriveMember member block? fixpoint? spec? name?

/-- Generate and register the parametricity theorem from the elaborated body of `p`. Structural
and well-founded recursion derive the whole block, and a `where` or `let rec` helper is derived
along with the definition it was split out of; partial fixpoints require
admissibility. `(repr := ...)` says which parameter to relate, by name or by position;
omitting it selects the first implicit parameter (`{...}` or `⦃...⦄`), skipping explicit
and instance parameters. A definition without an implicit parameter needs an explicit spec.
Selection is resolved separately for each member of a recursive block.

A helper is derived under the same `(repr := ...)`, so selecting by position rather than by name
can miss it; deriving the helper by hand first is always allowed, and a helper that already has a
translation is left alone.

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
