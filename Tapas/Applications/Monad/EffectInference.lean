import Tapas.TaglessFinal.AbstractTC

namespace Tapas

open Lean Meta Elab Term TaglessFinal

/-- Merge independently-created metavariables for definitionally equal capabilities. -/
private def deduplicateCapabilities
    (args : Array (Expr × Expr)) : TermElabM (Array (Expr × Expr)) := do
  let mut unique := #[]
  for (type, mvar) in args do
    let type ← instantiateMVars type
    let mut duplicate? := none
    for (otherType, otherMVar) in unique do
      if ← isDefEq type otherType then
        duplicate? := some otherMVar
        break
    match duplicate? with
    | some otherMVar => mvar.mvarId!.assign otherMVar
    | none => unique := unique.push (type, mvar)
  return unique

private partial def withCapabilityInstances
    (args : Array (Expr × Expr)) (k : Array Expr → TermElabM α) : TermElabM α :=
  go 0 #[]
where
  go (i : Nat) (locals : Array Expr) : TermElabM α := do
    if h : i < args.size then
      let (type, _) := args[i]
      Meta.withLocalDecl (.mkSimple s!"otherEffect{i}") .instImplicit type fun localInst =>
        go (i + 1) (locals.push localInst)
    else
      k locals

/-- Rewrite a capability goal into the hypotheses of an instance that produces it,
when unifying with that instance leaves nothing undetermined.

Only classes with an `outParam` are rewritten. Such a class is a view on a more
primitive one (`MonadState` on `MonadStateOf`), and Lean discharges it by *finding*
the `outParam` rather than by matching the one in the goal. As soon as a second
capability shares the class the view stops being synthesizable, so as a binder it is
a requirement no concrete monad can discharge; the basis it is derived from always
is. -/
private def unfoldCapability (isCapability : Expr → Bool) (type : Expr) :
    MetaM (Option (Expr × Array Expr)) := do
  let some className := type.getAppFn'.constName? | return none
  unless Lean.hasOutParams (← getEnv) className do return none
  -- `getInstances` sorts by ascending priority, and instance search tries the last
  -- candidate first.
  for inst in (← SynthInstance.getInstances type).reverse do
    let result? ← observing? do
      let (args, _, conclusion) ← Meta.forallMetaTelescopeReducing (← Meta.inferType inst.val)
      unless ← isDefEq conclusion type do failure
      let mut premises := #[]
      for arg in args do
        let arg ← instantiateMVars arg
        unless arg.isMVar do continue       -- already fixed by unifying with the goal
        let premiseType ← instantiateMVars (← Meta.inferType arg)
        -- Anything else would trade a known requirement for an unknown one.
        unless isCapability premiseType && !premiseType.hasExprMVar do failure
        premises := premises.push arg
      if premises.isEmpty then failure
      return (← instantiateMVars (mkAppN inst.val args), premises)
    if let some result := result? then return result
  return none

/-- Replace a capability by the basis it is derived from, and the hypotheses of that
step by theirs. A basis is normally already a fixpoint; a chain of views is followed
until one is reached, bounded by `maxRecDepth` like any other meta-level recursion. -/
private partial def normalizeCapability (isCapability : Expr → Bool)
    (type : Expr) (mvar : Expr) : TermElabM (Array (Expr × Expr)) :=
  withIncRecDepth do
    let some (value, premises) ← unfoldCapability isCapability type | return #[(type, mvar)]
    let userName := (← mvar.mvarId!.getDecl).userName
    mvar.mvarId!.assign value
    let mut result := #[]
    for h : i in [0 : premises.size] do
      let premise := premises[i]
      premise.mvarId!.setUserName <|
        if i == 0 then userName else userName.appendAfter s!"_{i}"
      let premiseType ← instantiateMVars (← inferType premise)
      result := result ++ (← normalizeCapability isCapability premiseType premise)
    return result

/-- Replace the `outParam` views among the capabilities by the bases they are
derived from, so that they stay usable when several capabilities share a class. -/
private def normalizeCapabilities (isCapability : Expr → Bool)
    (args : Array (Expr × Expr)) : TermElabM (Array (Expr × Expr)) := do
  let mut normalized := #[]
  for (type, mvar) in args do
    normalized := normalized ++ (← normalizeCapability isCapability type mvar)
  return normalized

/-- Remove a capability when the remaining capabilities can synthesize it. -/
private def minimizeCapabilities
    (args : Array (Expr × Expr)) : TermElabM (Array (Expr × Expr)) := do
  let mut kept := args
  let mut i := 0
  while i < kept.size do
    let (candidateType, candidateMVar) := kept[i]!
    let others := kept.eraseIdx! i
    let replacement? ← withCapabilityInstances others fun locals => do
      match ← trySynthInstance candidateType with
      | .undef => return none
      | .none => return none
      | .some inst =>
        let abstraction ← Meta.mkLambdaFVars locals inst
        let (_, otherMVars) := others.unzip
        return some (mkAppN abstraction otherMVars)
    match replacement? with
    | some replacement =>
      candidateMVar.mvarId!.assign replacement
      kept := others
    | none =>
      i := i + 1
  return kept

/--
Elaborate a body under an already selected monad and abstract its missing effect
dictionaries. Semantic parameters and their local instances are supplied by the caller.
-/
def inferEffectBody (body : Term) (m expectedType : Expr) : TermElabM Expr := do
  let env ← getEnv
  -- No effect registry is used: any unresolved class constraint that
  -- mentions the generated monad is treated as a capability requirement.
  let isMonadCapability (type : Expr) :=
    type.getAppFn'.constName?.any (Lean.isClass env) && m.occurs type
  let (args, e) ← abstractTCArgsCore body isMonadCapability "effect"
    { simplifyType := true } (some expectedType)
  let args ← normalizeCapabilities isMonadCapability args
  let args ← deduplicateCapabilities args
  let args ← minimizeCapabilities args
  let (_, effectMVars) := args.unzip
  Meta.mkLambdaFVars effectMVars e (binderInfoForMVars := .instImplicit)

/--
Elaborate a monadic term under a fresh monad `m`, then abstract `m`, `Monad m`,
and every unresolved capability instance used by the term.
-/
syntax (name := inferEffectsStx) "inferEffects% " term : term

@[term_elab inferEffectsStx]
def elabInferEffects : TermElab := fun stx _ => do
  let `(inferEffects% $body:term) := stx | throwUnsupportedSyntax
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let valueType := mkSort (.succ u)
  let computationType := mkSort (.succ v)
  let monadType ← mkArrow valueType computationType
  Meta.withLocalDecl `m .implicit monadType fun m => do
    let monadInstType ← Meta.mkAppM ``Monad #[m]
    Meta.withLocalDecl `instMonad .instImplicit monadInstType fun instMonad => do
      let resultType ← Meta.mkFreshExprMVar valueType
      let expectedType := mkApp m resultType
      let e ← inferEffectBody body m expectedType
      Meta.mkLambdaFVars #[m, instMonad] e

end Tapas
