module

public import Tapas
public import TapasTest.Applications.Monad.StackSuggestion.Orderings
public meta import TapasTest.Applications.Monad.StackSuggestion.Orderings

public meta section

/-!
`#suggest_stack`, the concrete monads that can run a program whose capabilities were
inferred.

This is a case study on top of `infer_effects`, not part of `Tapas`. The library is
about relating two interpretations of a program; choosing one is a separate question,
and this file answers it with a report rather than a proof. It uses `Tapas` only for
`typeConstructorUniverses?`; everything else is Lean's own elaborator API.

`infer_effects` leaves a program polymorphic in `m` with one instance parameter per
capability, and running it needs a concrete `m`. The capabilities do not determine one:
several monads discharge the same set, and they do not all return the same thing. The
command therefore lists them instead of choosing.

Three notions are used throughout.

* A **layer** is a monad transformer applied to everything but its monad argument, such
  as `StateT Nat`. Layers are found by matching a capability against the instances in
  scope, so a class written by the user is covered as soon as it has an instance of the
  shape `C args (T args' m)`. Nothing has to be registered.
* A **stack** is a sequence of distinct layers applied to `Id`.
* The **observation** of a stack is what `Stack α` reduces to, for a value type `α` the
  stack does not fix. It is what a completed run returns.

Candidates are grouped by observation, up to the order in which a run takes its
arguments and the nesting of the products it returns, which are differences a caller
can undo. Stacks in different groups return different information, and the printed
observations say how. This compares the results of complete runs; it is not a proof that
two stacks agree on a program, which is what `derive_parametric` establishes.
-/

/- NOTE: A layer has to discharge its capability *on its own*. Checking this against `Id`
rather than against a monad variable is what tells a layer apart from a forwarding
instance such as `MonadExceptOf ε (OptionT m)`, which needs `MonadExceptOf ε m` again
below it and so supplies nothing. Both have a conclusion of the accepted shape.

The same check is what keeps `Id` out of the capability list: `Monad m`, and anything
else an empty stack already satisfies, needs no layer. -/

namespace TapasTest.Applications.Monad.StackSuggestion.Basic

open Lean Meta Elab Command Tapas.Utils

/-- The position of the only parameter of monadic kind in `type`, when there is exactly
one. A capability class names its monad this way. -/
private def uniqueMonadParamIdx? (type : Expr) : MetaM (Option Nat) :=
  forallTelescope type fun xs _ => do
    let candidates ← xs.zipIdx.filterM fun (x, _) => do
      return (← typeConstructorUniverses? (← inferType x)).isSome
    let #[(_, idx)] := candidates | return none
    return some idx

/-- Everything a program leaves for a concrete monad to supply. -/
structure CapabilityRequirements where
  /-- The monad parameter the capabilities are stated over. -/
  monad : Expr
  /-- The instance parameters mentioning `monad` that `Id` does not already satisfy. -/
  capabilities : Array Expr

/-- The capabilities of `declName`, read off its signature. `k` runs with them in scope. -/
def withCapabilityRequirements (declName : Name)
    (k : CapabilityRequirements → MetaM α) : MetaM α := do
  -- Fresh level metavariables, so that a stack may fix the universe the monad lives in.
  let type ← inferType (← mkConstWithFreshMVarLevels declName)
  forallTelescopeReducing type fun binders _ => do
    let monads ← binders.filterM fun binder => do
      return (← typeConstructorUniverses? (← inferType binder)).isSome
    let some monad := monads[0]?
      | throwError "suggest_stack: {declName} has no parameter of monadic kind"
    let mut capabilities := #[]
    for binder in binders do
      unless (← binder.fvarId!.getBinderInfo) == .instImplicit do continue
      let capability ← instantiateMVars (← inferType binder)
      unless capability.containsFVar monad.fvarId! do continue
      -- An empty stack already satisfies it, so no layer has to supply it.
      if (← dischargedBy? monad capability (mkConst ``Id [Level.zero])).isSome then continue
      capabilities := capabilities.push capability
    k { monad, capabilities }
where
  /-- `capability` with `monad` replaced by `candidate`, synthesized. -/
  dischargedBy? (monad capability candidate : Expr) : MetaM (Option Expr) := do
    let goal := capability.replaceFVar monad candidate
    if !(← isTypeCorrect goal) then return none
    try synthInstance? goal catch _ => return none

/-! ## Layers -/

/-- The universes of the monad a layer takes. -/
def layerUniverses? (layer : Expr) : MetaM (Option (Level × Level)) := do
  let .forallE _ inner _ _ ← whnf (← inferType layer) | return none
  typeConstructorUniverses? inner

/-- A layer applied to `Id`, the shortest stack containing it. -/
def layerOverId? (layer : Expr) : MetaM (Option Expr) := do
  let some (u, _) ← layerUniverses? layer | return none
  let stack := mkApp layer (mkConst ``Id [u])
  return if ← isTypeCorrect stack then some stack else none

/- The conclusion of an instance names the transformer and fixes its arguments, but only
those the capability determines. `MonadExceptOf ε₁ (ExceptT ε₂ m)` leaves `ε₂` free, so
matching it would invent an error type; such an instance is passed over, as is one whose
monad argument is not in fact a monad, as in `MonadStateOf σ (EStateM ε σ)`. -/
/-- The transformer an instance of a capability supplies, when it supplies one. -/
private def instanceLayer? (className : Name) (monadIdx : Nat) (capabilityArgs : Array Expr)
    (inst : SynthInstance.Instance) : MetaM (Option Expr) :=
  observing? do
    let (instanceArgs, _, conclusion) ← forallMetaTelescopeReducing (← inferType inst.val)
    guard (conclusion.getAppFn.constName? == some className)
    let conclusionArgs := conclusion.getAppArgs
    guard (conclusionArgs.size == capabilityArgs.size)
    for i in [:capabilityArgs.size] do
      if i != monadIdx then guard (← isDefEq conclusionArgs[i]! capabilityArgs[i]!)
    let transformed ← instantiateMVars conclusionArgs[monadIdx]!
    guard transformed.getAppFn.isConst
    let args := transformed.getAppArgs
    guard (args.size ≥ 1)
    let inner := args[args.size - 1]!
    guard (instanceArgs.contains inner)
    guard !(← inner.mvarId!.isAssigned)
    guard (← typeConstructorUniverses? (← inferType inner)).isSome
    let layerArgs ← args[:args.size - 1].toArray.mapM instantiateMVars
    guard (!layerArgs.any (·.hasExprMVar))
    return mkAppN transformed.getAppFn layerArgs

/- The instances are looked up against the capability with its monad replaced by a
metavariable. An instance supplies a transformer exactly where that position may still
become one, and the parameter of a program is rigid: searching for `MonadStateOf Nat m`
itself finds only what a variable monad already satisfies. -/
/-- The layers that discharge `capability` by themselves, where `monad` is the parameter
the capability is stated over. -/
def capabilityLayers (monad capability : Expr) : MetaM (Array Expr) := do
  let some className := capability.getAppFn.constName? | return #[]
  let some monadIdx ← uniqueMonadParamIdx? (← getConstInfo className).type | return #[]
  let monadType ← inferType monad
  let probe := capability.replaceFVar monad (← mkFreshExprMVar monadType)
  if monadIdx ≥ probe.getAppNumArgs then return #[]
  let mut layers := #[]
  for inst in ← SynthInstance.getInstances probe do
    -- A position of its own for each instance, so that matching one cannot constrain
    -- what the next is matched against.
    let capabilityArgs := (capability.replaceFVar monad (← mkFreshExprMVar monadType)).getAppArgs
    let some layer ← instanceLayer? className monadIdx capabilityArgs inst | continue
    let some overId ← layerOverId? layer | continue
    let goal := mkAppN capability.getAppFn (capabilityArgs.set! monadIdx overId)
    unless ← isTypeCorrect goal do continue
    unless (← try synthInstance? goal catch _ => pure none).isSome do continue
    unless ← layers.anyM (isDefEq · layer) do layers := layers.push layer
  return layers

/-! ## Stacks -/

/-- The layers applied outside-in to `Id`, when their kinds line up. -/
def stackOf? (layers : Array Expr) : MetaM (Option Expr) := do
  let some first := layers[0]? | return none
  let some (u, _) ← layerUniverses? first | return none
  let mut stack := mkConst ``Id [u]
  for layer in layers.reverse do
    let applied := mkApp layer stack
    unless ← isTypeCorrect applied do return none
    stack := applied
  return some stack

/-- What a complete run of `stack` returns, as a function of the value type. -/
def observationOf? (stack : Expr) : MetaM (Option Expr) := do
  let some (u, _) ← typeConstructorUniverses? (← inferType stack) | return none
  withLocalDeclD `α (mkSort (.succ u)) fun α => do
    let result ← Meta.reduce (mkApp stack α) (skipTypes := false)
    return some (← mkForallFVars #[α] result)

/-! ## Grouping observations -/

/-- The components of a nested product, in the order they are written. -/
private partial def productComponents (type : Expr) : Array Expr :=
  if type.isAppOfArity ``Prod 2 then
    let args := type.getAppArgs
    productComponents args[0]! ++ productComponents args[1]!
  else #[type]

/-- A description of `type` that forgets how its products are nested. -/
private partial def resultKey (type : Expr) : String :=
  let components := productComponents type
  if components.size > 1 then
    "(" ++ " × ".intercalate ((components.map resultKey).qsort (· < ·)).toList ++ ")"
  else
    type.withApp fun f args =>
      if args.isEmpty then toString f
      else "(" ++ toString f ++ " " ++ " ".intercalate (args.map resultKey).toList ++ ")"

/- An observation is closed, so the value type is a loose bound variable and its key is
the same for every candidate. A binder is an argument of the run exactly when the rest
of the type does not mention it. -/
/-- The arguments a run takes and the result it returns. -/
private partial def runArguments (type : Expr) (arguments : Array Expr := #[]) :
    Array Expr × Expr :=
  match type with
  | .forallE _ argument body _ =>
    if body.hasLooseBVar 0 then (arguments, type)
    else runArguments (body.lowerLooseBVars 1 1) (arguments.push argument)
  | _ => (arguments, type)

/-- A description of an observation that forgets the order of a run's arguments and the
nesting of the products it returns. -/
def observationKey (observation : Expr) : String :=
  let body := match observation with
    | .forallE _ _ body _ => body
    | _ => observation
  let (arguments, result) := runArguments body
  " → ".intercalate ((arguments.map resultKey).qsort (· < ·)).toList ++ " ⊢ " ++ resultKey result

/-! ## The command -/

/-- A stack that discharges every capability, with what a run of it returns. -/
structure StackCandidate where
  /-- The stack itself, a sequence of layers applied to `Id`. -/
  stack : Expr
  /-- What a complete run returns, as a function of the value type. -/
  observation : Expr

/-- Above this many candidates the list stops being a menu, and is refused. -/
private def candidateLimit : Nat := 720

/-- The stacks built from `layerChoices`, one layer per capability, that discharge every
capability of `requirements`. -/
def stackCandidates (requirements : CapabilityRequirements) (layerChoices : Array (Array Expr)) :
    MetaM (Array StackCandidate) := do
  let mut layerSets : Array (Array Expr) := #[#[]]
  for choices in layerChoices do
    let mut extended := #[]
    for layers in layerSets do
      for layer in choices do
        -- Two capabilities can ask for the same layer, as a reader and its local
        -- adaptation do; the layer is placed once.
        if ← layers.anyM (isDefEq · layer) then
          unless ← extended.anyM (fun s => return s == layers) do extended := extended.push layers
        else extended := extended.push (layers.push layer)
    layerSets := extended
  let total := layerSets.foldl (fun n layers => n + (List.range layers.size).foldl (· * ·.succ) 1) 0
  if total > candidateLimit then
    throwError "suggest_stack: {total} candidate stacks is too many to list"
  let mut candidates := #[]
  for layers in layerSets do
    for order in orderings layers.toList do
      let some stack ← stackOf? order.toArray | continue
      let discharged ← requirements.capabilities.allM fun capability => do
        let goal := capability.replaceFVar requirements.monad stack
        if !(← isTypeCorrect goal) then return false
        return (← try synthInstance? goal catch _ => pure none).isSome
      unless discharged do continue
      let some observation ← observationOf? stack | continue
      candidates := candidates.push { stack, observation }
  return candidates

/- The monad and the capabilities are binders of `declName`, so the report has to be
given its local context before the telescope closes; `logInfo` would otherwise print
them as inaccessible free variables. -/
/-- Report the stacks that can run `declName`. -/
def suggestStack (declName : Name) : MetaM MessageData :=
  withCapabilityRequirements declName fun requirements => do
    if requirements.capabilities.isEmpty then
      return m!"{.ofConstName declName} needs no capability beyond `Monad`; any monad runs it."
    let layerChoices ← requirements.capabilities.mapM (capabilityLayers requirements.monad)
    let mut unsupplied := #[]
    for capability in requirements.capabilities, layers in layerChoices do
      if layers.isEmpty then unsupplied := unsupplied.push capability
    unless unsupplied.isEmpty do
      throwError "suggest_stack: no transformer in scope supplies{
        indentD (MessageData.joinSep (unsupplied.toList.map toMessageData) "\n")}"
    let requires := m!"{.ofConstName declName} requires {requirements.capabilities.size} \
      capabilit{if requirements.capabilities.size == 1 then "y" else "ies"} of `\
      {requirements.monad}`:{indentD (MessageData.joinSep
        (requirements.capabilities.toList.zipWith
          (fun capability layers =>
            m!"{capability}  ←  {MessageData.joinSep (layers.toList.map toMessageData) " | "}")
          layerChoices.toList) "\n")}"
    let candidates ← stackCandidates requirements layerChoices
    if candidates.isEmpty then
      return ← addMessageContext m!"{requires}\n\n\
        No ordering of those layers discharges every capability."
    -- Candidates that return the same information are one group of the menu.
    let mut groups : Array (String × Array StackCandidate) := #[]
    for candidate in candidates do
      let key := observationKey candidate.observation
      match groups.findIdx? (fun (groupKey, _) => groupKey == key) with
      | some i => groups := groups.modify i fun (k, cs) => (k, cs.push candidate)
      | none => groups := groups.push (key, #[candidate])
    -- Each stack is written with its own result rather than its group's: two stacks
    -- return the same thing without having to write it the same way, as a reader placed
    -- above and below a state does. One group needs no heading; the summary says it.
    let stackEntry := fun (candidate : StackCandidate) =>
      m!"{candidate.stack}{indentD m!"unfolds to {candidate.observation}"}"
    let entries :=
      if groups.size == 1 then groups.toList.flatMap fun (_, group) => group.toList.map stackEntry
      else groups.toList.mapIdx fun i (_, group) =>
        m!"result {i + 1}:{indentD (MessageData.joinSep (group.toList.map stackEntry) "\n")}"
    let summary :=
      if candidates.size == 1 then m!"1 stack discharges all of them"
      else if groups.size == 1 then
        m!"{candidates.size} stacks discharge all of them, and all return the same result\n\
          (up to the order of a run's arguments and the nesting of its products)"
      else
        m!"{candidates.size} stacks discharge all of them, returning {groups.size} \
          different results\n\
          (up to the order of a run's arguments and the nesting of its products)"
    addMessageContext m!"{requires}\n\n{summary}:{indentD (MessageData.joinSep entries "\n")}"

/--
`#suggest_stack f` lists the concrete monads that discharge every capability `f` was
inferred to need, grouped by what a complete run of each returns.

The capabilities are the instance parameters mentioning `f`'s first parameter of monadic
kind that `Id` does not already satisfy.

Each stack is printed with the type it unfolds to, which is what a complete run of it
returns. Stacks in one group return the same thing, up to the order of a run's arguments
and the nesting of the products it returns, so choosing between them does not change what
`f` computes; two such stacks can still write that result differently, which is why every
stack carries its own. Stacks in different groups do return different things.
-/
syntax (name := suggestStackStx) "#suggest_stack " ident : command

@[command_elab suggestStackStx]
def elabSuggestStack : CommandElab := fun stx => do
  let `(#suggest_stack $declName:ident) := stx | throwUnsupportedSyntax
  liftTermElabM do
    logInfo (← suggestStack (← realizeGlobalConstNoOverloadWithInfo declName))

end TapasTest.Applications.Monad.StackSuggestion.Basic
