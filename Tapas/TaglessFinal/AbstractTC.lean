import Lean
open Lean Meta Elab Term

namespace TaglessFinal

structure AbstractTCArgsConfig where
  allowMVarDependency : Bool := true
  simplifyType : Bool := false
deriving Inhabited

declare_term_config_elab elabAbstractTCArgsConfig AbstractTCArgsConfig

/-- A missing typeclass argument that has been abstracted out of a term. -/
structure AbstractTCArg where
  /-- The class constraint the argument must satisfy, simplified when
  `AbstractTCArgsConfig.simplifyType` is set. -/
  type : Expr
  /-- The fresh metavariable standing for the instance, in place of the one the
  elaborator left behind. Abstracting it turns the argument into a binder. -/
  mvar : Expr
deriving Inhabited

-- TODO This is overlapping with `simplifyMVarType` in `Veil/Util/Meta.lean`
-- except for the delaboration and some further simplification there;
-- consider merging once this is tested to be OK

/-- Simplify the type of the given metavariable `mv`, and abstract it as a new
metavariable with the given `mvname`. -/
def simplifyAndAbstractMVar (mv : Expr)
  (mvname : Name) (keepBodyIf : Expr → TermElabM Bool := fun _ => return true)
  (cfg : AbstractTCArgsConfig := {}) : TermElabM (Option AbstractTCArg) := do
  let ty ← /- Meta.reduce (skipTypes := false) $ ← -/ Meta.inferType mv
  Meta.forallTelescope ty fun ys body => do
    -- IMPORTANT: `body` can still hold an assigned metavariable applied to the binders
    -- it was abstracted over (`MonadStateOf (?σ n) m` with `?σ := fun _ => Nat`), so the
    -- binders it really depends on only show up after instantiation.
    let body ← instantiateMVars (← whnf body)
    if !(← keepBodyIf body) then return none
    -- `usedYs` is what `mkForallFVars (usedOnly := true)` would keep: `removeUnused`
    -- closes the used set under the types of the binders it keeps. Deriving both the
    -- abstracted type and its application below from it keeps the two telescopes in sync.
    let (_, _, usedYs) ← Meta.removeUnused ys (← body.collectFVars.run {}).2
    let type' ← if cfg.simplifyType then Meta.mkForallFVars usedYs body else pure ty
    -- Create a new mvar to replace the old one
    let decl ← mv.mvarId!.getDecl
    let mv' ← Meta.mkFreshExprMVar (.some type') (kind := decl.kind) (userName := mvname)
    -- Assign the old mvar, to get rid of it
    let mv_pf ← do
      -- NOTE: `mkLambdaFVars` can behave unexpectedly when handling mvars
      -- (e.g., automatically applying them to the body); we workaround this
      -- by using a dummy fvar and then doing replacement
      Meta.withLocalDeclD decl.userName type' fun z => do
        let tmp ← if cfg.simplifyType then Meta.mkLambdaFVars ys $ mkAppN z usedYs else pure z
        pure $ tmp.replaceFVar z mv'
    mv.mvarId!.assign mv_pf
    -- IMPORTANT: the type might have _delayed assignment metavariables_; here
    -- we don't handle this.
    let tyMVars ← Meta.getMVars type'
    unless tyMVars.isEmpty || cfg.allowMVarDependency do
      throwError "(type still has mvars after simplification):\n{type'}"
    return some { type := type', mvar := mv' }

-- taken from the function introduced in https://github.com/leanprover/lean4/pull/8621
open Meta Grind in
private partial def topsortMVars? (ms : Array Expr) : MetaM (Option (Array Expr)) := do
  let (some _, s) ← go.run.run {} | return none
  return some s.result
where
  go : TopSortM Unit := do
    for m in ms do
      visit m

  visit (m : Expr) : TopSortM Unit := do
    if (← get).permMark.contains m then
      return ()
    if (← get).tempMark.contains m then
      failure
    modify fun s => { s with tempMark := s.tempMark.insert m }
    visitTypeOf m
    modify fun s => { s with
      result := s.result.push m
      permMark := s.permMark.insert m
    }

  visitTypeOf (m : Expr) : TopSortM Unit := do
    let type ← instantiateMVars (← inferType m)
    type.forEach' fun e => do
      if e.hasExprMVar then
        if e.isMVar && ms.contains e then
          visit e
        return true
      else
        return false

/- A delayed assignment `?m #[xs] := ?pending` stands for `?m := fun xs => ?pending`.
Lean only carries it out once the value of `?pending` is *ground*, because a metavariable
still sitting in that value could later be assigned a term mentioning `xs`, which the
abstraction would put out of scope. The values here are final -- elaboration is over, and
nothing else will assign into them -- and the metavariables they still hold are the target
instances, which are passed explicitly rather than assigned. Carrying the assignments out
is therefore the abstraction Lean would itself perform, and leaving them would leave the
body uninstantiable for good.

Leaving one behind would also break `simplifyAndAbstractMVar`, which says outright that it
does not handle delayed assignments. -/
/-- Carry out the delayed assignments whose value is already known, so that
`instantiateMVars` can eliminate them. -/
private partial def collapseDelayedAssignments (e : Expr) : MetaM Unit := do
  let mut progress := false
  for mvarId in ← Meta.getMVars e do
    unless ← mvarId.isAssigned do
      let some delayed ← getDelayedMVarAssignment? mvarId | continue
      unless ← delayed.mvarIdPending.isAssigned do continue
      mvarId.assign (← delayed.mvarIdPending.withContext do
        Meta.mkLambdaFVars delayed.fvars (← instantiateMVars (.mvar delayed.mvarIdPending)))
      progress := true
  -- Collapsing one assignment can expose another nested in its value.
  if progress then collapseDelayedAssignments e

-- TODO This is overlapping with `getRequiredDecidableInstances` in `Veil/Util/Meta.lean`
def abstractTCArgsCore (stx : Term)
  (targetTC : Expr → Bool)
  (nameGen : String := "arg")
  (cfg : AbstractTCArgsConfig := {})
  (expectedType? : Option Expr := none) : TermElabM (Array AbstractTCArg × Expr) := do
  /- We want to throw an error if anything fails or is missing during
  elaboration. -/
  Term.withoutErrToSorry $ do
  -- We elaborate the `stx` ignoring typeclass inference failures, but ensuring we
  -- do synthesize all the metavariables that we can (not postponing them). This
  -- is to ensure the resulting expression is 'complete' (i.e. doesn't have holes,
  -- except for the `targetTC` instances, which will be passed explicitly).
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
  let e ← Term.elabTerm stx expectedType?
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  collapseDelayedAssignments e
  let mvars ← Array.map Expr.mvar <$> Meta.getMVars e
  -- there might be dependencies between the metavariables
  let some mvars ← topsortMVars? mvars | throwError "cyclic dependencies between metavariables detected"
  let mut nameCounter := 0
  let mut nextName := getNextName nameCounter
  let mut res : Array AbstractTCArg := #[]
  for mv in mvars do
    if let some tmp ← simplifyAndAbstractMVar mv nextName isBodyTarget cfg then
      res := res.push tmp
      nameCounter := nameCounter + 1
      nextName := getNextName nameCounter
  return (res, e)
where
  isBodyTarget (body : Expr) : TermElabM Bool := do
    return targetTC (← instantiateMVars body)
  getNextName (n : Nat) : Name :=
    .mkSimple <| nameGen ++ toString n

/-- `abstractTCargs% [TC1, TC2, ...] t` collects all missing arguments in `t`
that are instances of any typeclass in `TC1`, `TC2`, ... , and abstracts them
as arguments. The result will be like `fun [arg0 : TC1 ... , argk : TCm] => t`.
If no typeclass list is given, every argument elaboration left behind is
abstracted, whether or not its type is a class.

The `TCi` in the list can be either a constant name or a local typeclass
declaration in the local context. The leading configuration sets the fields of
`AbstractTCArgsConfig`. -/
syntax (name := abstractTCargsStx) "abstractTCargs% " optConfig ("[" ident,* "]")? term : term

@[term_elab abstractTCargsStx]
def elabAbstractTCargs : TermElab := fun stx _ => do
  match stx with
  | `(abstractTCargs% $cfg:optConfig $[[ $[$tcs:ident],* ]]? $t:term) => do
    let cfg ← elabAbstractTCArgsConfig cfg
    let parsedList ← tcs.mapM parseTCList
    let targetTC e := match parsedList with
      | none => true
      | some (constTCNames, targetFVars) =>
        let head := e.getAppFn'
        head.constName?.elim (targetFVars.contains head) constTCNames.contains
    let (args, e) ← abstractTCArgsCore t targetTC (cfg := cfg)
    let e ← Meta.mkLambdaFVars (args.map (·.mvar)) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    pure e
  | _ => throwUnsupportedSyntax
where
  parseTCList (tcs : Array (TSyntax `ident)) : TermElabM (Array Name × Array Expr) := do
    let mut constTCNames : Array Name := #[]
    let mut targetFVars : Array Expr := #[]
    for i in tcs do
      try
        let n ← resolveGlobalConstNoOverload i
        constTCNames := constTCNames.push n
      catch _ =>
        let ldecl? := (← getLCtx).findFromUserName? i.getId
        match ldecl? with
        | some ldecl =>
          targetFVars := targetFVars.push ldecl.toExpr
        | none =>
          throwError "unknown typeclass or local declaration: {i}"
    return (constTCNames, targetFVars)

end TaglessFinal
