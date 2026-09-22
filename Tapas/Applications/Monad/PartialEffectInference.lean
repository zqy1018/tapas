module

public import Tapas.Applications.Monad.EffectInference
public import Tapas.Applications.Monad.Loop

public meta section

namespace Tapas

open Lean Meta Elab Term Command TaglessFinal

/--
`infer_effects_partial% body` is `infer_effects% body` with least-fixpoint semantics for
`while` and `repeat`, which is what lets `derive_parametric` relate the result.

It adds the two order parameters a least fixpoint needs, `[∀ α, CCPO (m α)]` and
`[MonoBind m]`, and keeps them only where the body actually loops: a loop-free body
gets the signature `infer_effects%` would have given it. A recursive definition is not one term,
so it uses the command form `infer_effects_partial def ...` instead.
-/

/- NOTE: `while` and `repeat` expand to `ForIn` over `Lean.Loop`, whose standard
instance admits no relation. The least-fixpoint loop is selected by introducing
`Parametricity.PartialLoop.instForIn` as a let-bound local instance, so the choice
reaches this term only and no instance in the surrounding environment changes. -/
syntax (name := inferPartialEffectsStx) "infer_effects_partial% " term : term

/-- Introduce the two order parameters a least fixpoint needs, select the loop they support, and
run `k` with them and an action spending the selection.

`k` is handed the two parameters, which it binds only where the block uses them, and a function
inlining the selected loop into an elaborated term. -/
private def withPartialLoop (m valueType : Expr)
    (k : (orderParams : Array Expr) → (spend : Expr → TermElabM Expr) → TermElabM α) :
    TermElabM α := do
  let ccpoType ← withLocalDeclD `α valueType fun α => do
    mkForallFVars #[α] (← mkAppOptM ``Order.CCPO #[some (mkApp m α)])
  withLocalDecl `instCCPO .instImplicit ccpoType fun ccpo => do
    withLocalDecl `instMonoBind .instImplicit
        (← mkAppOptM ``Order.MonoBind #[some m, none, none]) fun mono => do
      -- `Monad m` is left to synthesis: the monad frontend put it in scope.
      let loopInst ← mkAppOptM ``Parametricity.PartialLoop.instForIn
        #[some m, none, some ccpo, some mono]
      -- A local instance takes precedence over the standard loop, without
      -- changing any scoped instances in the surrounding environment.
      withLetDecl `instPartialLoop (← inferType loopInst) loopInst fun localLoop =>
        -- The binding is spent once the body is elaborated, and is inlined rather than
        -- kept: its type mentions `m`, so a surviving `let` would leave a
        -- representation-dependent dictionary in the body, where the translation looks
        -- for a relation for `ForIn` and finds none. Solved metavariables can hide a
        -- reference to it, so they are instantiated first.
        k #[ccpo, mono] fun e => return (← instantiateMVars e).replaceFVar localLoop loopInst

@[term_elab inferPartialEffectsStx]
def elabInferPartialEffects : TermElab := fun stx _ => do
  let `(infer_effects_partial% $body:term) := stx | throwUnsupportedSyntax
  withInferredMonad body fun m valueType elaborated =>
    withPartialLoop m valueType fun orderParams spend => do
      mkLambdaFVars orderParams (← spend (← elaborated)) (usedOnly := true)

/--
`infer_effects_partial def f ...` is `infer_effects def f ...` with least-fixpoint semantics for
`while` and `repeat`, which is what lets `derive_parametric` relate the result.

It adds the two order parameters a least fixpoint needs, `[∀ α, CCPO (m α)]` and `[MonoBind m]`,
and keeps them only where the block actually loops: a loop-free block gets the signature
`infer_effects` would have given it. A block whose recursion is a `partial_fixpoint` needs them
for that fixpoint rather than for anything in its bodies, so it keeps them either way.
-/
syntax (name := inferPartialEffectsDeclStx) "infer_effects_partial " command : command

@[command_elab inferPartialEffectsDeclStx]
def elabInferPartialEffectsDecl : CommandElab := fun stx => do
  let views ← inferredDeclViews stx[1]
  -- A `partial_fixpoint` is built from the order parameters after the bodies are elaborated, so
  -- nothing in a body records that it needs them.
  let isFixpoint ← views.anyM fun view => do
    pure (← declValTerminationHints view.value).partialFixpoint?.isSome
  runTermElabM fun vars =>
    withMonadParam fun m valueType params =>
      withPartialLoop m valueType fun orderParams spend =>
        -- Bound unconditionally when the fixpoint needs them, optional otherwise.
        addInferredEffectDefinitions views vars m valueType
          (params ++ if isFixpoint then orderParams else #[])
          (if isFixpoint then #[] else orderParams) (post := spend)

end Tapas
