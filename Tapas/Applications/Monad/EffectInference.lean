import Tapas.TaglessFinal.Inference

namespace Tapas

open Lean Meta Elab Term TaglessFinal

/--
Elaborate a body under an already selected monad and abstract its missing effect
dictionaries. Semantic parameters and their local instances are supplied by the caller.
-/
def inferEffectBody (body : Term) (m expectedType : Expr) : TermElabM Expr := do
  -- No effect registry is used: any unresolved class constraint that
  -- mentions the generated monad is treated as a capability requirement.
  inferInterfaceBody body (m.occurs ·) m!"the monad `{m}`" (some expectedType) "effect"

/-- Elaborate `body` under a fresh monad `m` with `[Monad m]`, and abstract both.

`under` is handed `m`, the sort `m` takes its values in, and an action elaborating
`body` at `m`'s expected type. It may introduce further binders around that action,
which is how a loop instance becomes visible while the body is elaborated, and is
responsible for abstracting whatever it introduced. -/
def withInferredMonad (body : Term)
    (under : (m : Expr) → (valueType : Expr) → TermElabM Expr → TermElabM Expr) :
    TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let valueType := mkSort (.succ u)
  let monadType ← mkArrow valueType (mkSort (.succ v))
  withLocalDecl `m .implicit monadType fun m => do
    withLocalDecl `instMonad .instImplicit (← mkAppM ``Monad #[m]) fun instMonad => do
      let elaborated := do
        let resultType ← mkFreshExprMVar valueType
        inferEffectBody body m (mkApp m resultType)
      mkLambdaFVars #[m, instMonad] (← under m valueType elaborated)

/--
`infer_effects% body` elaborates a monadic term under a fresh monad `m`, then abstracts
`m`, `Monad m`, and every unresolved capability instance the term used.

A body containing `while` or `repeat` elaborates, but its result cannot be related;
reach for `infer_effects_partial%` when it is meant to be derived.

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

end Tapas
