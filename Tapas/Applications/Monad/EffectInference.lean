import Tapas.TaglessFinal.RecursiveInference

namespace Tapas

open Lean Meta Elab Term Command TaglessFinal

/--
Elaborate a body under an already selected monad and abstract its missing effect
dictionaries. Semantic parameters and their local instances are supplied by the caller.
-/
def inferEffectBody (body : Term) (m expectedType : Expr) : TermElabM Expr :=
  -- No effect registry is used: any unresolved class constraint that
  -- mentions the generated monad is treated as a capability requirement.
  inferInterfaceBody body (m.occurs ·) m!"the monad `{m}`" (some expectedType) "effect"

/-- Elaborate `views` as one block of declarations under an already selected monad and abstract their
missing effect dictionaries. -/
def addInferredEffectDefinitions (views : Array DefView) (vars : Array Expr)
    (m valueType : Expr) (params : Array Expr) (optParams : Array Expr := #[])
    (post : Expr → TermElabM Expr := pure) : TermElabM Unit :=
  addInferredDefinitions views vars params optParams (select := (m.occurs ·))
    (selected := m!"the monad `{m}`") (post := post)
    (defaultDefType := some do return mkApp m (← mkFreshExprMVar valueType))
    (nameGen := "effect")

/-- Introduce a fresh monad `m` with `[Monad m]`, and run `k` with them.

`k` is handed `m`, the sort `m` takes its values in, and the two parameters, in the order a
signature binds them. -/
def withMonadParam (k : (m : Expr) → (valueType : Expr) → (params : Array Expr) → TermElabM α) :
    TermElabM α := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let valueType := mkSort (.succ u)
  let monadType ← mkArrow valueType (mkSort (.succ v))
  withLocalDecl `m .implicit monadType fun m => do
    withLocalDecl `instMonad .instImplicit (← mkAppM ``Monad #[m]) fun instMonad =>
      k m valueType #[m, instMonad]

/-- Elaborate `body` under a fresh monad `m` with `[Monad m]`, and abstract both.

`under` is handed `m`, the sort `m` takes its values in, and an action elaborating
`body` at `m`'s expected type. It may introduce further binders around that action,
which is how a loop instance becomes visible while the body is elaborated, and is
responsible for abstracting whatever it introduced. -/
def withInferredMonad (body : Term)
    (under : (m : Expr) → (valueType : Expr) → TermElabM Expr → TermElabM Expr) :
    TermElabM Expr :=
  withMonadParam fun m valueType params => do
    let elaborated := do
      let resultType ← mkFreshExprMVar valueType
      inferEffectBody body m (mkApp m resultType)
    mkLambdaFVars params (← under m valueType elaborated)

/--
`infer_effects% body` elaborates a monadic term under a fresh monad `m`, then abstracts
`m`, `Monad m`, and every unresolved capability instance the term used.

A body containing `while` or `repeat` elaborates, but its result cannot be related;
reach for `infer_effects_partial%` when it is meant to be derived. A recursive definition is not
one term, so it uses the command form `infer_effects def ...` instead.

**Note:** An operation appearing inside a tactic block cannot contribute a capability; write the
signature out instead of inferring it.
-/
/- NOTE: A tactic block is elaborated by `Lean.Elab.Term.runTactic`, which finishes with its own
`synthesizeSyntheticMVars` at the default `ignoreStuckTC := false`. The capability
requirements an operation leaves behind are therefore reported as stuck instances at the end
of the block, before the tolerant synthesis in `abstractTCArgsCore` can collect them. -/
syntax (name := inferEffectsStx) "infer_effects% " term : term

@[term_elab inferEffectsStx]
def elabInferEffects : TermElab := fun stx _ => do
  let `(infer_effects% $body:term) := stx | throwUnsupportedSyntax
  withInferredMonad body fun _ _ elaborated => elaborated

/--
`infer_effects def f ...` is `infer_effects%` for a declaration: it elaborates the definition
under a fresh monad `m`, then adds `m`, `Monad m` and every unresolved capability instance its
body used to the signature.

Unlike `infer_effects%` it applies to a recursive definition, and to a `mutual` block of them,
which then share one set of capability parameters:

```lean
infer_effects
def countDown : Nat → m Unit
  | 0 => pure ()
  | k + 1 => do set k; countDown k
-- {m : Type → Type v} → [Monad m] → [MonadStateOf Nat m] → Nat → m Unit
```

A body containing `while` or `repeat` elaborates, but its result cannot be related; reach for
`infer_effects_partial` when it is meant to be derived.

**Note:** An operation appearing inside a tactic block cannot contribute a capability; write the
signature out instead of inferring it.
-/
syntax (name := inferEffectsDeclStx) "infer_effects " command : command

@[command_elab inferEffectsDeclStx]
def elabInferEffectsDecl : CommandElab := fun stx => do
  let views ← inferredDeclViews stx[1]
  runTermElabM fun vars =>
    withMonadParam fun m valueType params =>
      addInferredEffectDefinitions views vars m valueType params

end Tapas
