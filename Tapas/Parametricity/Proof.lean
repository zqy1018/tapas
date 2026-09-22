module

public import Tapas.LogicalRelation
public import Tapas.Parametricity.Fixpoint
public import Tapas.Parametricity.Registry
public meta import Tapas.LogicalRelation.Translation

public meta section

/-!
## Proving that two interpretations are related

`LogicalRelation.Translation` defines the relation at a type. This module constructs
its proof. Write `Δ; Γ ⊢ left ~ right` for the problem of constructing a proof of
`relationAt Δ left right selection` in the local context `Γ`. Here `Δ` records
each representation, its second interpretation and their base relation; `Γ`
contains values, interface dictionaries and the hypotheses relating them.
`ProofContext` holds `Δ` and the representation selection; Lean's local context
holds `Γ`. The construction also works relative to Lean's environment, which supplies
interface relation declarations, relators, and registered translation theorems.
We leave this fixed global environment implicit in the judgment.

The fundamental theorem of logical relations motivates this construction: related
inputs and relation-preserving primitives give related results, provided every
language construct used by the program preserves the relation interpretation.
For example, a function relation says that related arguments give related results.
Applying its proof to arguments and their relation proof establishes related
applications. A lambda introduces those arguments and proves its body instead.
Interface relation fields supply these proofs for primitive operations; registered
translations supply them for named helpers.

### Whole definitions and an existing relation environment

The general problem allows representation pairs and relational hypotheses already
in scope. Deriving a definition's parametricity theorem starts with no ambient
representation pairs: open its parameter telescope, introduce arbitrary pairs and
the required relational hypotheses, prove the instantiated bodies, then abstract
over the introduced binders. In this sense, whole-definition derivation is the
empty-initial-environment case of the same construction, not another proof procedure.

`Parametricity.Program` implements this outer construction using
`withRelatedTelescope #[]`. It passes the resulting, extended `ProofContext` to
`provePair`, which creates a relation goal and calls `proveGoal`. Calling
`proveGoal` with an empty `ProofContext` alone does not perform that telescope
construction: introducing a goal's `∀` does not extend `ctx.representations`.

This is a heuristic proof procedure for the relation interpretation supported by
`Translation`; it does not guarantee that every Lean definition is parametric or that
every true relational goal can be solved. Failure may mean missing evidence or
an unsupported construct.

### Cases and their recognition

Two independent distinctions organize this procedure. The cases below are grouped
by what they inspect: first the goal proposition and local context, then the
program terms at the two endpoints of a relation.

A separate distinction is between proof rules and search strategies.
- A proof rule justifies a proof step: `proveForall` uses universal introduction, and
  `proveApplication` applies a relational theorem to arguments and their relation
  proofs. Both groups below contain such rules.
- Search strategies determine how to expose and select applicable rules:
  `normalizeHead` chooses which definitions to
  unfold, `proveGoal` orders the cases, and individual cases choose candidate rules
  and backtracking behavior. One helper can implement both a rule and its search
  strategy; the two groups below do not separate those responsibilities.

#### Cases inspecting the goal proposition and local context

These cases start from the proposition to prove or the available evidence.
They are tried in order:

* `proveForall`: the goal is a `∀`. Introduce its next binder and prove the rest.
  The type translation has already expressed function relations, including
  higher-order premises, as these quantifiers.
* `proveAssumption`: a local hypothesis has the goal's type. Reuse its proof.
* `proveAdmissibility`: the goal is `AdmissibleRel`. Apply a local admissibility
  premise, or its pointwise lifting over shared function arguments, and prove the
  premises. This is a side condition of least-fixpoint induction, not a relation
  between two program terms.
* `proveEquality`: the goal is an `Eq`. Try reflexivity; other rules may still
  prove an equality that is not definitionally reflexive.
* `proveInterface`: the goal's head names an interface relation already generated
  and registered by `derive_interface_rel`. Prove that the two dictionaries satisfy
  this relation by applying its constructor and proving each operation field.
  The relation definition must already exist; this case only constructs its proof.

#### Cases inspecting the related program terms

Otherwise, `endpoints?` must recognize a base relation, equality or registered
relator. `normalizeHead` exposes the two terms up to definitional equality while
preserving lets, unsolved branches and heads with registered translations. The
goal is replaced with the relation on these normalized endpoints. The following
cases inspect their heads or apply available rules relating them:

* `proveLet`: both terms are lets. Prove their values related, extend `Γ` with
  two values and that proof, and prove the bodies. A representation-independent
  binding with definitionally equal values is shared. Keep bindings in the
  resulting proof so a local computation and its proof are not duplicated.
* `proveMatch`: both terms are matching `ite`/`dite` or matcher applications.
  Require shared, representation-independent discriminants, split them, and
  prove the corresponding branches. Contradictory branches close immediately.
  This implements only the shared-discriminant case of relational elimination;
  it does not eliminate a relation between different discriminants.
* `proveApplication`: try the registered translations for a common constant
  head, then direct local rules, then interface operation projections. Applying
  a rule combines its function relation with proofs of the argument relations,
  which become recursive goals. Backtrack if any premise fails.
* `proveConstructors`: both terms have the same data constructor head and the
  relation is inductive. Try each relation constructor and prove its premises,
  backtracking over the whole attempt.

#### Search order and failure behavior

Each Boolean case returns `true` only after solving the goal. An inapplicable
case returns `false`. Once `proveForall`, `proveAdmissibility`, `proveInterface`,
`proveLet` or `proveMatch` applies, failure is an error. Assumption, equality and
constructor attempts instead roll back and allow later alternatives.
`proveApplication` also retains the last error from proving a rule's premises,
so `reportFailure` can prefer it to a generic missing-rule message.
Lets and branches precede application deliberately: applying a rule first could
close over a whole continuation and duplicate its proof.

Enable `set_option trace.Tapas.Parametricity true` to inspect the goal tree,
endpoint normalization, and branch splitting. Application, admissibility and
relation-constructor attempts record failures before backtracking. Branches closed
by contradiction are also recorded.

### Recursive definitions

Recursion requires an induction principle, not repeated unfolding. `Program`
uses functional induction for recursive definitions, putting the induction
hypotheses into `Γ` as local rules before proving each unfolded case. For a
`partial_fixpoint`, it uses `fix_rel`: assume recursive calls are related, prove
the bodies related, and discharge admissibility. Both return to this procedure
for the bodies. An admissibility premise is retained in the generated theorem
only when the proof uses it.
-/

namespace Tapas.Parametricity

open Lean Meta
open LogicalRelation Utils

initialize registerTraceClass `Tapas.Parametricity

structure ProofContext where
  representations : Array RelatedRepresentation
  selection : RepresentationSelection

def mkRelation (ctx : ProofContext) (left right : Expr) : MetaM Expr :=
  relationAt ctx.representations left right ctx.selection

/-- Recover endpoints only for the chosen base relation, equality, or a registered
relator. Container relations are first-class proof goals, not just field premises. -/
def endpoints? (ctx : ProofContext) (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let args := type.getAppArgs
  if h : args.size < 2 then return none
  else
    let left := args[args.size - 2]
    let right := args[args.size - 1]
    -- Corresponding to a relation in the context
    if ctx.representations.any (fun p => type.getAppFn == p.relation) || type.isAppOf ``Eq then return some (left, right)
    -- Corresponding to a relator
    if let some typeConstructor := (← whnf (← inferType left)).getAppFn.constName? then
      if let some info := getRelator? (← getEnv) typeConstructor then
        if type.isAppOf info.relator then return some (left, right)
    return none

private inductive HypothesisRuleCase where
  | direct (hyp : Expr)
  | projection (rules : Array Expr)
  | none

/-- Rules contributed by a hypothesis `hyp : type`: `hyp` when it concludes a supported
relation, otherwise the operation projections of an interface relation, also under families.
Binders are looked through, including the `have`s in functional induction hypotheses. The
flag reports whether `hyp` concludes a supported relation. -/
private partial def hypothesisRules (ctx : ProofContext) (hyp type : Expr)
    (xs : Array Expr := #[]) : MetaM HypothesisRuleCase :=
  forallTelescope type fun ys body => do
    let xs := xs ++ ys
    -- Preserve the conclusion's relation head; a reducing telescope also unfolds definitions.
    let body := zetaHead body
    if body.isForall then
      return ← hypothesisRules ctx hyp body xs
    -- A direct proof for a relation
    if (← endpoints? ctx body).isSome then return HypothesisRuleCase.direct hyp
    -- Otherwise, check if it is an interface relation and generate operation projections
    if let some name := body.getAppFn.constName? then
      if let some info := getInterfaceRelation? (← getEnv) name.getPrefix then
        if info.relation == name then
          let applied := mkAppN hyp xs
          let fields ← info.fields.mapM fun field => do
            mkLambdaFVars xs (← mkProjection applied field)
          return HypothesisRuleCase.projection fields
    return HypothesisRuleCase.none

/-- Local hypotheses contribute direct rules or operation projections, also under families. -/
private def localRules (ctx : ProofContext) : MetaM (Array Expr) := do
  let mut projectionRules := #[]
  let mut directRules := #[]
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if ← isProp type then
      match ← hypothesisRules ctx decl.toExpr type with
      | .direct hyp => directRules := directRules.push hyp
      | .projection rules => projectionRules := projectionRules ++ rules
      | .none => pure ()
  -- Prefer the proof of a shared local function to reproving its expanded body.
  return directRules ++ projectionRules

/-- Expose the outer form of a relation endpoint so proof search can choose its next case.
Simplify function applications and wrappers while retaining lets for sharing, branches
for case splitting, and registered function names for applying their translation rules. -/
private def normalizeHead (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isLet || (iteHead? e).isSome then return e
  if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
    -- Held back for the branching step, unless the discriminants already say which
    -- branch is taken, in which case it reduces away. Reducing unconditionally
    -- would unfold `casesOn` to `rec` and lose the branching step altogether.
    if ← app.discrs.allM (Meta.isConstructorApp ·) then
      return ← whnfCore e
    return e
  -- A head with a registered translation is
  -- also left intact, so `proveApplication` can find that rule by name.
  let fn := e.getAppFn
  let fnName? := fn.const?
  if let some (name, _) := fnName? then
    unless (getParametricRules (← getEnv) name).isEmpty do return e
  -- Ordinary definitions are opaque to proof search, except exact forwarding
  -- wrappers such as `withTheReader`: a field applied only to original binders.
  -- For the wrappers, we unfold them.
  -- NOTE: This is more like a heuristic
  let e ← if let some (name, levels) := fnName? then do
      if let .defnInfo info ← getConstInfo name then
        let forwards ← lambdaTelescope info.value fun xs body => do
          let some field := body.getAppFn.constName? | return false
          pure <| (← isProjectionFn field) && body.getAppArgs.all xs.contains
        if forwards then
          pure ((info.value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs)
        else pure e
      else pure e
    else pure e
  -- Exposing operations hidden by wrappers or instance projections while
  -- keeping bindings available to `proveLet`, which preserves sharing in the proof.
  withTransparency .instances <| withConfig (fun c => { c with zeta := false, zetaDelta := false }) <|
    whnf e

/-- Recognize conditionals or matches that branch on definitionally equal,
representation-independent discriminants. Return `false` for unrecognized pairs;
report an error when a recognized pair fails the discriminant check. -/
private def checkSharedDiscriminants (ctx : ProofContext) (left right : Expr) : MetaM Bool := do
  if let some head := iteHead? left then
    if iteHead? right == some head then
      let a := left.getAppArgs[1]!
      let b := right.getAppArgs[1]!
      trace[Tapas.Parametricity] "conditional discriminants:\nleft: {a}\nright: {b}"
      unless independent ctx.representations a && independent ctx.representations b && (← isDefEq a b) do
        throwError "parametricity: condition depends on the representation or differs between interpretations"
      return true
  if let some l ← matchMatcherApp? left (alsoCasesOn := true) then
    if let some r ← matchMatcherApp? right (alsoCasesOn := true) then
      trace[Tapas.Parametricity] "match discriminants:\nleft: {l.discrs}\nright: {r.discrs}"
      unless l.discrs.size == r.discrs.size do
        throwError "parametricity: match discriminants differ between interpretations"
      for a in l.discrs, b in r.discrs do
        unless independent ctx.representations a && independent ctx.representations b && (← isDefEq a b) do
          throwError "parametricity: match discriminant depends on the representation or differs between interpretations"
      return true
  return false

/-- Reuse a local proof of the goal. -/
private def proveAssumption (goal : MVarId) : MetaM Bool := do
  return (← observing? <| withTransparency .instances goal.assumption).isSome

/-- Close a definitionally reflexive equality. -/
private def proveEquality (goal : MVarId) (target : Expr) : MetaM Bool := do
  if !target.isAppOf ``Eq then return false
  return (← observing? <| withTransparency .instances goal.refl).isSome

private def reportFailure (left right : Expr) (failure? : Option Exception) : MetaM Unit := do
  if let some ex := failure? then throw ex
  if let some name := left.getAppFn.constName? then
    throwError "parametricity: no applicable translation for {name}; use `derive_parametric {name}` or `attribute [parametric] theoremName`"
  throwError "parametricity: unsupported term or missing relation:\n{left}\nand\n{right}"

mutual

/-- Prove a quantified goal under its next binder. -/
private partial def proveForall (ctx : ProofContext) (goal : MVarId) (target : Expr) : MetaM Bool := do
  if !target.isForall then return false
  let (_, next) ← goal.intro1P
  proveGoal ctx next
  return true

/-- Prove a least-fixpoint admissibility premise from the local hypotheses. -/
private partial def proveAdmissibility (ctx : ProofContext) (goal : MVarId) (target : Expr) : MetaM Bool := do
  if !target.isAppOfArity' ``AdmissibleRel 5 then return false
  -- Instantiate a caller's admissibility premise before lifting it through
  -- the shared arguments of a recursive function.
  let mut rules := #[]
  for decl in ← getLCtx do
    if decl.type.getForallBody.isAppOf ``AdmissibleRel then
      rules := rules.push decl.toExpr
  let args := target.getAppArgs
  let (α, β) := (args[0]!, args[1]!)
  if let .forallE name dom body bi ← whnf α then
    if let .forallE _ dom' body' _ ← whnf β then
      if independent ctx.representations dom && independent ctx.representations dom' && (← isDefEq dom dom') then
        -- Supply the families `∀ (i : ι), AdmissibleRel (R i)` explicitly:
        -- higher-order unification cannot reliably infer the residual relation
        -- for multiple arguments.
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
    if (← observing? <| withTraceNode `Tapas.Parametricity (fun
        | .ok _ => return m!"admissibility rule {rule}"
        | .error ex => return m!"admissibility rule {rule} failed\n{ex.toMessageData}") do
        let subgoals ← withTransparency .instances <| goal.apply rule
        for subgoal in subgoals do proveGoal ctx subgoal).isSome then return true
  throwError "parametricity: missing admissibility premise:\n{target}"

/-- Prove an existing interface relation from its operation fields. -/
private partial def proveInterface (ctx : ProofContext) (goal : MVarId) (target : Expr) : MetaM Bool := do
  let some name := target.getAppFn.constName? | return false
  let some info := getInterfaceRelation? (← getEnv) name.getPrefix | return false
  if info.relation != name then return false
  -- A helper may require a parent class whose fields are supplied
  -- by a stronger dictionary relation in the caller's telescope.
  for fieldGoal in ← goal.constructor do proveGoal ctx fieldGoal
  return true

/-- Prove let bodies under a shared value or a pair of related values. -/
private partial def proveLet (ctx : ProofContext) (goal : MVarId) (left right : Expr) : MetaM Bool := do
  let .letE name lt lv lb nondep := left | return false
  let .letE _ rt rv rb _ := right | return false
  let bodyRelation := (← goal.getType).getBoundedAppFn 2
  if independent ctx.representations lt && independent ctx.representations rt &&
      (← withTransparency .instances <| isDefEq lv rv) then
    goal.assign (← mapLetDecl name lt lv fun x =>
      provePair ctx (lb.instantiate1 x) (rb.instantiate1 x) (some bodyRelation))
  else
    let valueProof ← provePair ctx lv rv
    let targetName := name.appendAfter "'"
    let relationName := name.appendAfter "_rel"
    -- Prove the body for opaque local computations
    -- related by a hypothesis. A jump such as `__do_jp ()` cannot be unfolded, so
    -- only the hypothesis closes it and the continuation proof is shared.
    let opaqueBody? : Option (Array Expr → Expr) ← withLocalDeclD name lt fun x =>
      withLocalDeclD targetName rt fun y => do
        let l := lb.instantiate1 x
        let r := rb.instantiate1 y
        -- A dependent `let` body may need the value definitionally.
        unless nondep do
          unless (← isTypeCorrect l) && (← isTypeCorrect r) do return none
        /- NOTE: An opaque value can change the body's result type, even when the body
        remains well-typed. Reuse the outer relation only for unchanged types.

        For a monad `m`, consider `let k := 2 ; pure (fun x : Fin k => x)`.
        The whole expression has type `m (Fin 2 → Fin 2)`. Replacing the let-bound
        `k` with an opaque `k : Nat` leaves the body well-typed, but its type is now
        `m (Fin k → Fin k)`. An outer computation relation instantiated at
        `Fin 2 → Fin 2` cannot be reused at this new type. Thus `isTypeCorrect`
        alone does not justify reusing `bodyRelation`; the check below
        conservatively requires the result types not to mention the opaque values.

        (This example is just for illustrating the type change.
        The actual `k := 2` binding would take the shared-let branch above.) -/
        let relation? :=
          -- CHECK Rewrite this using `occurs`?
          if (← inferType l).containsFVar x.fvarId! || (← inferType r).containsFVar y.fvarId!
          then none
          else some bodyRelation
        withLocalDeclD relationName (← mkRelation ctx x y) fun h => do
          let proof ← provePair ctx l r relation?
          -- CHECK Is there a better way to implement this thing?
          -- Abstract the opaque variables before leaving their scope; the caller
          -- supplies the values for the final let bindings after proof search.
          let proof ← proof.abstractM #[x, y, h]
          let relationType ← (← inferType h).abstractM #[x, y]
          let lt ← instantiateMVars lt
          let rt ← instantiateMVars rt
          return some fun values =>
            mkLet name lt values[0]! <|
              mkLet targetName rt values[1]! <|
                mkLet relationName relationType values[2]! proof
    if let some body := opaqueBody? then
      goal.assign (body #[lv, rv, valueProof])
    else
      -- Fallback specifically for dependent lets whose bodies need the value
      -- definitions to type-check; retain those definitions as local lets.
      goal.assign (← mapLetDecl name lt lv fun x =>
        mapLetDecl targetName rt rv fun y => do
          mapLetDecl relationName (← mkRelation ctx x y) valueProof fun _ =>
            provePair ctx (lb.instantiate1 x) (rb.instantiate1 y) (some bodyRelation))
  return true

/-- Prove corresponding branches of a shared conditional or match. -/
private partial def proveMatch (ctx : ProofContext) (goal : MVarId) (left right : Expr) : MetaM Bool := do
  unless ← checkSharedDiscriminants ctx left right do return false
  -- `proveGoal` has already put the normalized endpoints into this target.
  let mut target ← goal.getType
  if let some app ← matchMatcherApp? left (alsoCasesOn := true) then
    let lets ← letDiscriminants app.discrs
    unless lets.isEmpty do target ← zetaDeltaFVars target lets
  let normalized ← goal.replaceTargetDefEq target
  -- A branch contradicting its context, e.g. a functional induction case
  -- hypothesis, needs no relation proof.
  let proveBranch (branch : MVarId) : MetaM Unit :=
      withTraceNodeBefore `Tapas.Parametricity (fun _ => return m!"branch:\n{branch}") do
    let contradictory ← branch.contradictionCore
      { useDecide := false, emptyType := false, genDiseq := true }
    if contradictory then
      trace[Tapas.Parametricity] "closed by contradiction"
    else
      proveGoal ctx branch
  -- FIXME: There are some corner cases where `splitTarget?` might not handle
  -- CHECK What is `useNewSemantics`?
  if let some branches ← splitTarget? normalized then
    trace[Tapas.Parametricity] "split: {branches.length} branches"
    for branch in branches do proveBranch branch
    return true
  -- `split` does not eliminate a bare `casesOn`, which `matchMatcherApp?`
  -- nonetheless recognises above. Destructing a discriminant that is a shared
  -- free variable reduces it away instead.
  trace[Tapas.Parametricity] "split declined; trying cases on a shared discriminant"
  if let some app ← matchMatcherApp? left (alsoCasesOn := true) then
    for discr in app.discrs do
      if let .fvar fvarId := discr.consumeMData then
        if let some subgoals ← observing? <| withTraceNode `Tapas.Parametricity (fun
            | .ok goals => return m!"cases {discr}: {goals.size} branches"
            | .error ex => return m!"cases {discr} failed\n{ex.toMessageData}") <|
            normalized.cases fvarId then
          for subgoal in subgoals do proveBranch subgoal.mvarId
          return true
  throwError "parametricity: unsupported match elimination; register a translation for the enclosing helper"

/-- Prove an application using a registered or local relational rule. -/
private partial def proveApplication (ctx : ProofContext) (goal : MVarId) (left right : Expr) :
    MetaM (Bool × Option Exception) := do
  let mut rules := #[]
  if let some source := left.getAppFn.constName? then
    if right.getAppFn.constName? == some source then
      for name in getParametricRules (← getEnv) source do
        rules := rules.push (← mkConstWithFreshMVarLevels name)
  rules := rules ++ (← localRules ctx)
  let mut failure? := none
  -- Try each rule in turn, committing if it solves the goal without exceptions.
  for rule in rules do
    try
      -- Record the result before `commitIfNoEx` restores metavariable assignments.
      let solved ← commitIfNoEx <| withTraceNode `Tapas.Parametricity (fun
          | .ok true => return m!"rule {rule}"
          | .ok false => return m!"rule {rule}: not applicable"
          | .error ex => return m!"rule {rule}: premise failed\n{ex.toMessageData}") do
        let some subgoals ← observing? <| withTraceNode `Tapas.Parametricity (fun
            | .ok goals => return m!"application: {goals.length} subgoals"
            | .error ex => return m!"application failed: {ex.toMessageData}") <|
            withTransparency .instances <|
            goal.apply rule { newGoals := .all, synthAssignedInstances := false }
          | return false
        for subgoal in subgoals do proveGoal ctx subgoal
        return true
      if solved then return (true, none)
    catch ex =>
      failure? := some ex
  return (false, failure?)

/-- Relate matching data constructors using a constructor of their relation. -/
private partial def proveConstructors (ctx : ProofContext) (goal : MVarId) (type left right : Expr) :
    MetaM Bool := do
  let some relationName := type.getAppFn.constName? | return false
  let some leftName := left.getAppFn.constName? | return false
  if right.getAppFn.constName? != some leftName then return false
  let .ctorInfo _ ← getConstInfo leftName | return false
  let .inductInfo info ← getConstInfo relationName | return false
  for ctor in info.ctors do
    if (← observing? <| withTraceNode `Tapas.Parametricity (fun
        | .ok _ => return m!"relation constructor {ctor}"
        | .error ex => return m!"relation constructor {ctor} failed\n{ex.toMessageData}") do
        let rule ← mkConstWithFreshMVarLevels ctor
        for subgoal in ← goal.apply rule do proveGoal ctx subgoal).isSome then
      return true
  return false

/-- Prove that two terms are related, using the supplied binary relation or deriving
one from their types in the current relation environment. -/
partial def provePair (ctx : ProofContext) (left right : Expr)
    (relation? : Option Expr := none) : MetaM Expr := do
  let target ← match relation? with
    -- Reduce a lambda relation so function relations expose their quantifiers.
    | some relation => pure ((mkApp2 relation left right).headBeta)
    | none => mkRelation ctx left right
  let goal ← mkFreshExprSyntheticOpaqueMVar target
  proveGoal ctx goal.mvarId!
  instantiateMVars goal

/-- Prove a relational goal using the available hypotheses and translation rules. -/
partial def proveGoal (ctx : ProofContext) (goal : MVarId) : MetaM Unit :=
  withIncRecDepth <| goal.withContext <|
      withTraceNodeBefore `Tapas.Parametricity (fun _ => return m!"goal:\n{goal}") do
    let target ← instantiateMVars (← goal.getType)
    if ← proveForall ctx goal target then return
    if ← proveAssumption goal then return
    if ← proveAdmissibility ctx goal target then return
    if ← proveEquality goal target then return
    if ← proveInterface ctx goal target then return
    let some (left₀, right₀) ← endpoints? ctx target
      | throwError "parametricity: missing relational premise:\n{target}"
    let left ← normalizeHead left₀
    let right ← normalizeHead right₀
    if left != left₀ then
      trace[Tapas.Parametricity] "normalize left:\n{left₀}\n↦ {left}"
    if right != right₀ then
      trace[Tapas.Parametricity] "normalize right:\n{right₀}\n↦ {right}"
    let goal ← goal.replaceTargetDefEq (mkApp2 (target.getBoundedAppFn 2) left right)
    if ← proveLet ctx goal left right then return
    if ← proveMatch ctx goal left right then return
    -- FIXME: It's a bit weird to just report the last exception
    let (solved, failure?) ← proveApplication ctx goal left right
    if solved then return
    if ← proveConstructors ctx goal target left right then return
    reportFailure left right failure?

end

end Tapas.Parametricity
