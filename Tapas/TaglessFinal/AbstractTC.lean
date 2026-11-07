module

public meta import Lean
public meta import Lean.Meta.Tactic.Grind.EqResolution
import Lean.Elab.ConfigEval.Commands
import Lean.Exception
public import Lean.Expr

public meta section
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
  -- Local lets can hide further binders, such as a named branch's hypothesis.
  Meta.forallTelescopeReducing ty fun ys body => do
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

/- Tolerant elaboration can leave `?m #[xs] := ?pending` with an assigned `?pending`
whose value still contains missing typeclass instances. `instantiateMVars` only expands
this delayed substitution once the value is ground (no unassigned expression metavariables).
Here those holes must become parameters, so the delayed assignment remains stuck;
`simplifyAndAbstractMVar` does not handle such assignments either.

We replace it with an ordinary assignment by abstracting `xs` from the known value.
`mkLambdaFVars` also abstracts the remaining metavariables' dependencies on `xs`, so later
assignments cannot introduce out-of-scope references to these variables. This lets
`instantiateMVars` expose the value for instance abstraction. Local let variables in `xs`
need an extra argument binder, as explained below. -/
/-- Carry out the delayed assignments whose value is already known, so that
`instantiateMVars` can eliminate them. -/
private partial def collapseDelayedAssignments (e : Expr) : MetaM Unit := do
  let mut progress := false
  for mvarId in ← Meta.getMVars e do
    unless ← mvarId.isAssigned do
      let some delayed ← getDelayedMVarAssignment? mvarId | continue
      unless ← delayed.mvarIdPending.isAssigned do continue
      mvarId.assign (← delayed.mvarIdPending.withContext do
        /- Here `?m` denotes `Expr.mvar mvarId`, and `delayed` is its delayed-assignment
        record. As above, `?pending` denotes `Expr.mvar delayed.mvarIdPending`.
        `delayed.fvars` records the local variables of `?pending` that must be supplied
        as arguments to `?m`. These variables are absent from `?m`'s own local context.
        An entry may be a variable defined by a local `let`.

        For example, suppose `?pending : x = 0` has the local definition `x : Nat := 0`,
        and `delayed.fvars = #[x]`. Then `?m` has type
        ```
        Nat → (let x : Nat := 0; x = 0)
        ```
        Lean represents `?pending` by the application `?m x`. If `body` is the assigned
        value of `?pending`, `mkLambdaFVars #[x] body` produces `let x := 0; body`, binding
        the occurrences of the original local `x` in `body`. This is a proof, not a
        function accepting the argument in `?m x`. We instead assign
        ```
        ?m := fun (x : Nat) => let x : Nat := 0; body
        ```
        This is the general pattern for local let declarations: the extra lambda
        parameter is unused. `mkLambdaFVars` binds the original occurrences of `x`
        in `body` to the inner let, which shadows the outer `x` in the displayed term.
        The lambda only accepts the argument in `?m x`. The let keeps `x` definitionally
        equal to `0`, which `body` may rely on; using `fun x => body` instead would
        lose this equality.

        Processing binders from right to left preserves their dependencies.
        This mirrors `mkAuxMVarType` in `MetavarContext.lean`, which inserts a forall
        before the let for `syntheticOpaque` metavariables. `decl.isLet` excludes `have`
        (`nondep := true`), which `mkLambdaFVars` already turns into an ordinary lambda. -/
        let value ← instantiateMVars (.mvar delayed.mvarIdPending)
        let hasLet ← delayed.fvars.anyM fun fvar => do
          return fvar.isFVar && (← fvar.fvarId!.getDecl).isLet
        if !hasLet then
          Meta.mkLambdaFVars delayed.fvars value
        else
          delayed.fvars.foldrM (init := value) fun fvar value => do
            let value ← Meta.mkLambdaFVars #[fvar] value
            if fvar.isFVar then
              let decl ← fvar.fvarId!.getDecl
              if decl.isLet then
                -- The extra lambda must not capture existing bound-variable references.
                return Lean.mkLambda decl.userName .default decl.type (value.liftLooseBVars 0 1)
            return value)
      progress := true
  -- Collapsing one assignment can expose another nested in its value.
  if progress then collapseDelayedAssignments e

-- TODO This is overlapping with `getRequiredDecidableInstances` in `Veil/Util/Meta.lean`
/-- Collect the metavariables of `es` that `targetTC` accepts, and replace each by a fresh
metavariable prepared for abstraction.

The results are ordered so that a metavariable occurring in the type of another precedes it.
`es` are the expressions the arguments were left in; several are passed together when one
signature is to be shared, as by the definitions of a `mutual` block. -/
def abstractTCMVars (es : Array Expr)
  (targetTC : Expr → Bool)
  (nameGen : String := "arg")
  (cfg : AbstractTCArgsConfig := {}) : TermElabM (Array AbstractTCArg) := do
  es.forM fun e => collapseDelayedAssignments e
  let mut collected : Array Expr := #[]
  for e in es do
    for mvarId in ← Meta.getMVars e do
      unless collected.contains (.mvar mvarId) do collected := collected.push (.mvar mvarId)
  -- there might be dependencies between the metavariables
  let some mvars ← topsortMVars? collected | throwError "cyclic dependencies between metavariables detected"
  let mut nameCounter := 0
  let mut nextName := getNextName nameCounter
  let mut res : Array AbstractTCArg := #[]
  for mv in mvars do
    if let some tmp ← simplifyAndAbstractMVar mv nextName isBodyTarget cfg then
      res := res.push tmp
      nameCounter := nameCounter + 1
      nextName := getNextName nameCounter
  return res
where
  isBodyTarget (body : Expr) : TermElabM Bool := do
    return targetTC (← instantiateMVars body)
  getNextName (n : Nat) : Name :=
    .mkSimple <| nameGen ++ toString n

/-- Run `k` with elaboration tolerating unresolved typeclass goals.

Ordinary elaboration errors are still reported. `k` is expected to synthesize every metavariable
it can, so that the only holes left for `abstractTCMVars` to collect are the tolerated ones. -/
def withTolerantElaboration (k : TermElabM α) : TermElabM α :=
  /- We want to throw an error if anything fails or is missing during
  elaboration. -/
  Term.withoutErrToSorry <|
  -- We elaborate ignoring typeclass inference failures, but ensuring we
  -- do synthesize all the metavariables that we can (not postponing them). This
  -- is to ensure the resulting expression is 'complete' (i.e. doesn't have holes,
  -- except for the `targetTC` instances, which will be passed explicitly).
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) k

def abstractTCArgsCore (stx : Term)
  (targetTC : Expr → Bool)
  (nameGen : String := "arg")
  (cfg : AbstractTCArgsConfig := {})
  (expectedType? : Option Expr := none) : TermElabM (Array AbstractTCArg × Expr) :=
  withTolerantElaboration do
    let e ← Term.elabTerm stx expectedType?
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    return (← abstractTCMVars #[e] targetTC nameGen cfg, e)

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
