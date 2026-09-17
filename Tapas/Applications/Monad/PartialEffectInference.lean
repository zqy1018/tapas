import Tapas.Applications.Monad.EffectInference
import Tapas.Applications.Monad.Loop

namespace Tapas

open Lean Meta Elab Term

/--
`infer_effects_partial% body` is `infer_effects% body` with least-fixpoint semantics for
`while` and `repeat`, which is what lets `derive_parametric` relate the result.

It adds the two order parameters a least fixpoint needs, `[∀ α, CCPO (m α)]` and
`[MonoBind m]`, and keeps them only where the body actually loops: a loop-free body
gets the signature `infer_effects%` would have given it.
-/

/- NOTE: `while` and `repeat` expand to `ForIn` over `Lean.Loop`, whose standard
instance admits no relation. The least-fixpoint loop is selected by introducing
`Parametricity.PartialLoop.instForIn` as a let-bound local instance, so the choice
reaches this term only and no instance in the surrounding environment changes. -/
syntax (name := inferPartialEffectsStx) "infer_effects_partial% " term : term

@[term_elab inferPartialEffectsStx]
def elabInferPartialEffects : TermElab := fun stx _ => do
  let `(infer_effects_partial% $body:term) := stx | throwUnsupportedSyntax
  withInferredMonad body fun m valueType elaborated => do
    let ccpoType ← withLocalDeclD `α valueType fun α => do
      mkForallFVars #[α] (← mkAppOptM ``Order.CCPO #[some (mkApp m α)])
    withLocalDecl `instCCPO .instImplicit ccpoType fun ccpo => do
      withLocalDecl `instMonoBind .instImplicit
          (← mkAppOptM ``Order.MonoBind #[some m, none, none]) fun mono => do
        -- `Monad m` is left to synthesis: `withInferredMonad` put it in scope.
        let loopInst ← mkAppOptM ``Parametricity.PartialLoop.instForIn
          #[some m, none, some ccpo, some mono]
        -- A local instance takes precedence over the standard loop, without
        -- changing any scoped instances in the surrounding environment.
        withLetDecl `instPartialLoop (← inferType loopInst) loopInst fun localLoop => do
          -- The binding is spent once the body is elaborated, and is inlined rather than
          -- kept: its type mentions `m`, so a surviving `let` would leave a
          -- representation-dependent dictionary in the body, where the translation looks
          -- for a relation for `ForIn` and finds none. Solved metavariables can hide a
          -- reference to it, so they are instantiated first.
          let e := (← instantiateMVars (← elaborated)).replaceFVar localLoop loopInst
          mkLambdaFVars #[ccpo, mono] e (usedOnly := true)

end Tapas
