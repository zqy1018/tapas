import Tapas.TaglessFinal.AbstractTC

/-!
(The two words are kept apart throughout. An *argument* is an instance the body
needs at a use site, which elaboration leaves unresolved; a *parameter* is a
binder of the term produced. Deciding which arguments become parameters is what
this module does.)

Infer the typeclass instance arguments a body needs, under parameters the caller
names explicitly, and abstract both as parameters of the result.

`infer_final% (A : Type) => body` elaborates `body` with `A` introduced as a local
hypothesis rather than a metavariable -- *rigid*, in the sense that elaboration
cannot quietly solve it to a concrete interpretation. It then collects the class
constraints that remain unresolved because `A` is unknown, and abstracts both
around the result:

```lean
class Literal (A : Type) where
  lit : Nat → A

class Arithmetic (A : Type) extends Literal A where
  add : A → A → A

def sample := infer_final% (A : Type) =>
  [Arithmetic.add (A := A) (Literal.lit 1) (Literal.lit 2)]

example : {A : Type} → [Arithmetic A] → List A := @sample
```

The signature binds the selected parameters implicitly, in the order written,
followed by the retained constraints as instance-implicit parameters. Here the
two `Literal A` arguments are merged into one and then dropped, because
`Arithmetic A` synthesizes its parent. The result is a `List A` rather than an
`A`: selecting a parameter says nothing about the body's type.

## Representation parameters

A selected parameter is meant to be a *representation parameter*: the parameter
deciding how the object language's expressions are represented, and the one
allowed to differ between two interpretations of the same program. Above, `A` is
the representation and `Arithmetic A` is the interface it must implement, so
`A := Nat` evaluates the program, `A := String` prints it, and an AST type
reifies it.

This module neither defines nor detects that notion. `inferInterfaceBody` takes a
predicate on class constraints, and `infer_final%` builds that predicate from the
parameters the caller names. A representation parameter therefore has exactly one
role here: being rigid during elaboration, it is what leaves a constraint
unresolved, and mentioning it is what selects that constraint for abstraction.

Its other roles belong to later layers -- which parameters a logical relation
duplicates and relates, and what a parametricity theorem quantifies over. Those
layers take the same choice as `(repr := A)` in `Tapas.LogicalRelation` and
`Tapas.Parametricity`. Nothing checks that all three layers were given the same
parameter.

The choice is written down rather than inferred, because the code does not
determine it. For a client of `Store (Key Value : Type) (m : Type → Type)`,
varying `m` while `Key` and `Value` stay shared, and comparing two `Value`
representations, are both legitimate; they are different theorems. Kind is not a
usable signal either, so no parameter is treated as a representation until it is
named.

Nothing further is required of a selected parameter. Its kind is arbitrary: a
carrier `A : Type u`, an indexed family `repr : Ty → Type u`, a monad
`m : Type u → Type v`, or a value such as `n : Nat`. Later parameters may have
kinds mentioning earlier ones. The body need not return a value in the
representation, or use the parameter at all.

## What is abstracted

A constraint is abstracted when its head is a class *and* its type mentions at
least one selected parameter. Everything else keeps its ordinary meaning:
instances available in the environment are used as usual, unrelated missing
instances remain errors, and an ordinary unsolved hole remains an error instead
of silently becoming a parameter.

The primitive extraction and abstraction mechanism lives in
`Tapas.TaglessFinal.AbstractTC`: `abstractTCArgsCore` elaborates the body,
collects the selected missing constraints, and prepares their metavariables for
abstraction; its `abstractTCargs%` frontend exposes that step alone. This module
adds normalization, deduplication, minimization, and the checks below. Both
layers work with general typeclass constraints; monadic effect inference is one
application of the mechanism, not a requirement of either layer.

## Algorithm

Steps 1–2 are delegated to `abstractTCArgsCore`; steps 3–6 are added here, and
each is named by the function implementing it. Steps 3–5 run in the order listed
inside `inferInterfaceBody`.

1. Elaborate the body, allowing unresolved typeclass goals while still reporting
   ordinary elaboration errors. Existing instances are used normally, and
   synthetic metavariables are synthesized before collection. Delayed assignments
   left behind are carried out, so that the unresolved goals are the only thing
   keeping the body from instantiating.
2. Order the remaining metavariables by their type dependencies and retain the
   selected class goals. Simplify their telescopes by removing unused local
   arguments while preserving dependencies between the arguments that remain.
3. `normalizeConstraint`, over each constraint in turn: normalize a selected
   constraint carrying an `outParam` when an instance expresses it in terms of
   fully determined
   selected prerequisites; a `MonadState` view, for instance, becomes its
   `MonadStateOf` basis. Follow such rewrites recursively, and never introduce
   an undetermined type or value argument. A view is discharged by *finding*
   its `outParam`, so it stops being synthesizable as soon as a second
   constraint shares the class; its basis does not.
4. `deduplicateConstraints`: merge the metavariables of constraints that unify,
   which also solves arguments one requirement leaves undetermined and another
   fixes. Then `minimizeConstraints`: try to remove each requirement by
   synthesizing it from the others as local instances, replacing the removed
   metavariable with an expression built from the retained ones.
5. `inferInterfaceBody`: check the body, its type, and the retained constraint
   types for unresolved expression metavariables other than the selected ones.
   `throwUnresolved` reports whatever is left at the operation it came from,
   rather than at the frontend's token.
6. `inferInterfaceBody` abstracts the retained constraints as instance-implicit
   parameters. `elabInferFinal`, the `infer_final%` frontend, then abstracts its
   selected parameters as implicit ones and checks the whole expression against
   any surrounding expected type.

Both halves of step 4 depend on traversal order. Deduplication solves an
undetermined argument from whichever requirement it reaches first, and
minimization is greedy and uses the available instance search, so it guarantees
neither a unique choice nor a globally smallest set of constraints.

## Boundaries

No expected type is pushed into the body, and the frontend never guesses `A` or
`repr ?i` as one. When elaboration needs help choosing a type, annotate the body
or pass the parameter explicitly at an operation's use site, as
`Literal.lit (A := A) 1` does above; the surrounding expected type is checked
after abstraction. A caller that does want to constrain the body -- such as the
Monad frontend, which fixes the result shape `m ?α` -- calls `inferInterfaceBody`
directly, passing its own expected type and introducing its own parameters and
local instances beforehand.

This module produces a Lean term with instance parameters. It neither chooses a
logical relation nor proves parametricity; those operations consume the resulting
declaration in their own modules.
-/
namespace TaglessFinal

open Lean Meta Elab Term

/- NOTE: `isDefEq` is used as unification here, not only as a test. When two requirements
differ just in arguments the body left undetermined, matching them solves those
arguments: `Choose ?σ A` next to `Choose Nat A` becomes one `Choose Nat A`, while
the first requirement on its own would have been reported as an unresolved
argument in step 5. The value always comes from another requirement of the same
body, never from an ambient instance, but which requirement supplies it depends
on the order the constraints are traversed. -/
/-- Merge the metavariables of class constraints that unify. -/
private def deduplicateConstraints
    (args : Array AbstractTCArg) : TermElabM (Array AbstractTCArg) := do
  let mut unique := #[]
  for arg in args do
    let type ← instantiateMVars arg.type
    let mut duplicate? := none
    for other in unique do
      if ← isDefEq type other.type then
        duplicate? := some other.mvar
        break
    match duplicate? with
    | some otherMVar => arg.mvar.mvarId!.assign otherMVar
    | none => unique := unique.push { arg with type }
  return unique

/-- Rewrite a class constraint into the prerequisites of an instance that produces
it, when unifying with that instance leaves nothing undetermined except further
selected constraints.

A goal `C …` is rewritten to the prerequisites of an instance `inst` when every
rule below holds. Candidates are tried in instance-search order and the first
match wins; if none matches, the goal is left alone.

1. `C` has an `outParam`. Such a class is a view on a more primitive one
   (`MonadState` on `MonadStateOf`), and Lean discharges it by *finding* the
   `outParam` rather than by matching the one in the goal. As soon as a second
   constraint shares the class the view stops being synthesizable, so as a
   parameter it is a requirement no concrete interpretation can discharge; the
   basis it is derived from always is.
2. The conclusion of `inst` unifies with the goal. Arguments fixed by that
   unification are not prerequisites.
3. Every argument left undetermined is itself a selected class constraint, as
   judged by `isConstraint`, and not an ordinary type or value argument.
4. The type of each such argument has no remaining metavariables, so the
   unification determined it fully.
5. At least one argument is left undetermined. An instance that discharges the
   goal outright is not a rewrite, and applying it here would silently commit
   the program to one concrete interpretation.

Rules 3 and 4 are what keep the rewrite from trading a known requirement for an
unknown one. Failing any of rules 2–5 rejects that candidate only, not the
rewrite as a whole. -/
private def unfoldConstraint (isConstraint : Expr → Bool) (type : Expr) :
    MetaM (Option (Expr × Array Expr)) := do
  let some className := type.getAppFn'.constName? | return none
  unless Lean.hasOutParams (← getEnv) className do return none
  -- `getInstances` sorts by ascending priority, and instance search tries the last
  -- candidate first.
  --
  -- Each `inst.val` is the instance as a term: the declaring constant for a global
  -- instance, the fvar for a local one, with universe levels already refreshed. Its
  -- type is therefore a telescope ending in the class, `∀ {α} …, [D α] → … → C α …`,
  -- which is a Horn clause: the conclusion is the head and the instance binders are
  -- the subgoals. The body of this loop is one resolution step against that clause,
  -- except that the subgoals are kept as requirements instead of being solved.
  for inst in (← SynthInstance.getInstances type).reverse do
    let result? ← observing? do
      -- Rename the clause apart: every binder becomes a fresh metavariable, so
      -- `conclusion` is its head and `args` holds the ordinary arguments and the
      -- subgoals alike. `Reducing` exposes binders behind reducible definitions.
      let (args, _, conclusion) ← Meta.forallMetaTelescopeReducing (← Meta.inferType inst.val)
      -- Head unification, and the only step that connects the clause to this goal:
      -- retrieval does not attempt it, since the discrimination tree is approximate
      -- and every local instance of the class is returned without its arguments
      -- being looked at. It also does the real work here. Solving the metavariables
      -- just created is what makes the survivors below exactly the subgoals this goal
      -- leaves open, and what makes `mkAppN inst.val args` a term of type `type` —
      -- required, because `normalizeConstraint` assigns it to the goal.
      unless ← isDefEq conclusion type do failure
      let mut premises := #[]
      for arg in args do
        let arg ← instantiateMVars arg
        unless arg.isMVar do continue       -- already fixed by unifying with the goal
        let premiseType ← instantiateMVars (← Meta.inferType arg)
        -- Anything else would trade a known requirement for an unknown one.
        unless isConstraint premiseType && !premiseType.hasExprMVar do failure
        premises := premises.push arg
      if premises.isEmpty then failure
      return (← instantiateMVars (mkAppN inst.val args), premises)
    if let some result := result? then return result
  return none

/-- Drive `unfoldConstraint`, whose docstring lists the rewrite rules, to a
fixpoint: replace a class constraint by the instance prerequisites that
synthesize it, then normalize those prerequisites in turn. Stop when no rewrite
applies; the recursion is bounded by `maxRecDepth` like other meta-level
recursion.

The first prerequisite inherits the binder name of the constraint it replaces,
and later ones append `_1`, `_2`, and so on, so one requirement in the body
stays recognizable in the generated signature. -/
private partial def normalizeConstraint (isConstraint : Expr → Bool)
    (arg : AbstractTCArg) : TermElabM (Array AbstractTCArg) :=
  withIncRecDepth do
    let some (value, premises) ← unfoldConstraint isConstraint arg.type | return #[arg]
    let userName := (← arg.mvar.mvarId!.getDecl).userName
    arg.mvar.mvarId!.assign value
    let mut result := #[]
    for h : i in [0 : premises.size] do
      let premise := premises[i]
      premise.mvarId!.setUserName <|
        if i == 0 then userName else userName.appendAfter s!"_{i}"
      let premiseType ← instantiateMVars (← inferType premise)
      result := result ++
        (← normalizeConstraint isConstraint { type := premiseType, mvar := premise })
    return result

/-- Remove a class constraint when the retained ones can synthesize it. -/
private def minimizeConstraints
    (args : Array AbstractTCArg) : TermElabM (Array AbstractTCArg) := do
  let mut kept := args
  let mut i := 0
  while h : i < kept.size do
    let candidate := kept[i]
    let others := kept.eraseIdx i
    let replacement? ← withLocalDecls
        (others.mapIdx fun i other =>
          (.mkSimple s!"otherInterface{i}", .instImplicit, fun _ => pure other.type)) fun locals => do
      match ← trySynthInstance candidate.type with
      | .undef => return none
      | .none => return none
      | .some inst =>
        let abstraction ← Meta.mkLambdaFVars locals inst
        return some (mkAppN abstraction (others.map (·.mvar)))
    match replacement? with
    | some replacement =>
      candidate.mvar.mvarId!.assign replacement
      kept := others
    | none =>
      i := i + 1
  return kept

/- `logUnassignedUsingErrorInfos` is the path Lean itself takes for metavariables
left unassigned at the end of a declaration: it recovers the syntax each one came
from and the application it is an argument of. Reusing it is what puts the error
on the offending operation instead of on the `infer_final%` token. The extra
message carries what only this module knows -- whether the metavariable blocks a
constraint that was about to become a parameter, and whether it is itself an
instance that was never selected for abstraction. -/
/-- Report the metavariables that survived inference, at the positions they came
from. -/
private def throwUnresolved (selected : MessageData) (args : Array AbstractTCArg)
    (bad : Array MVarId) : TermElabM α := do
  let env ← getEnv
  let mut extra := m!""
  for arg in args do
    let type ← instantiateMVars (← inferType arg.mvar)
    if (← getMVars type).any bad.contains then
      extra := extra ++ .note m!"the inferred requirement{indentExpr type}\n\
        still has an undetermined argument, so it cannot become an instance parameter: \
        no caller could supply one."
  for id in bad do
    let type ← instantiateMVars (← inferType (.mvar id))
    if type.getAppFn'.constName?.any (Lean.isClass env) then
      extra := extra ++ .note m!"`{type}` does not mention {selected}, so it is not abstracted \
        and must be synthesized from the environment."
  unless ← Term.logUnassignedUsingErrorInfos bad (extraMsg? := some extra) do
    throwError m!"interface inference: unresolved argument of type\
      {indentExpr (← inferType (.mvar bad[0]!))}{extra}"
  throwAbortTerm

/-- Elaborate `body` and abstract the missing instance arguments that `select`
accepts, as instance-implicit parameters of the returned term.

This runs in the caller's local context, so the parameters the constraints are
selected by -- representation parameters, and anything else the caller wants
shared -- must already be introduced, along with any local instances to use. A
constraint qualifies when its head is a class and `select` accepts its type;
`infer_final%` passes "mentions one of the named parameters", while the Monad
frontend passes "mentions `m`"; `selected` names that choice for the error
message reporting a constraint that was not abstracted.

`expectedType?` is the expected type for elaborating the body, which the caller
supplies when it wants to fix the result shape; `nameGen` names the generated
binders. Neither parameter kinds nor the result type are restricted here.
Unresolved non-class holes remain errors instead of quietly becoming instance
parameters. -/
def inferInterfaceBody (body : Term) (select : Expr → Bool)
    (selected : MessageData := m!"a selected parameter")
    (expectedType? : Option Expr := none) (nameGen : String := "interface") : TermElabM Expr := do
  let env ← getEnv
  let isInterface (type : Expr) :=
    type.getAppFn'.constName?.any (Lean.isClass env) && select type
  let (args, e) ← abstractTCArgsCore body isInterface nameGen
    { simplifyType := true } expectedType?
  let args ← args.flatMapM (normalizeConstraint isInterface)
  let args ← deduplicateConstraints args
  let args ← minimizeConstraints args
  let interfaceMVars := args.map (·.mvar)
  let unresolved ← getMVars (← instantiateMVars e)
  let unresolvedType ← getMVars (← instantiateMVars (← inferType e))
  let unresolvedArgs ← args.flatMapM fun arg => do getMVars (← instantiateMVars (← inferType arg.mvar))
  let bad := (unresolved ++ unresolvedType ++ unresolvedArgs).toList.filter
    fun id => !interfaceMVars.contains (.mvar id)
  unless bad.isEmpty do throwUnresolved selected args bad.eraseDups.toArray
  Meta.mkLambdaFVars interfaceMVars e (binderInfoForMVars := .instImplicit)

/-- `infer_final% (A : kindA) (B : kindB) => body` infers the interface `body`
requires of the named parameters.

Each parameter is introduced as a rigid local hypothesis; see the module docstring for what that
means and why they are named rather than inferred.

The signature binds the parameters implicitly, in the order written, then the
inferred arguments as instance-implicit parameters:

```lean
infer_final% (A : Type u) => (body : A)   -- {A : Type u} → [C A] → … → A
```

Kinds are arbitrary and may mention earlier parameters. The body may have any
type, need not use the parameters, and receives no expected type from this
frontend; annotate it or pass a parameter explicitly at an operation's use site
when elaboration needs help. Any surrounding expected type is checked only after
abstraction. -/
syntax (name := inferFinalStx) "infer_final% " ("(" ident " : " term ")")+ " => " term : term

@[term_elab inferFinalStx]
def elabInferFinal : TermElab := fun stx expectedType? => do
  let `(infer_final% $[($names:ident : $kinds:term)]* => $body:term) := stx
    | throwUnsupportedSyntax
  let e ← withLocalDecls
      ((names.zip kinds).map fun (name, kind) =>
        (name.getId, .implicit, fun _ => Term.elabType kind)) fun params => do
    let e ← inferInterfaceBody body (fun type => params.any (·.occurs type))
      (MessageData.orList (names.toList.map fun name => m!"`{name.getId}`"))
    mkLambdaFVars params e
  Term.ensureHasType expectedType? e

end TaglessFinal
