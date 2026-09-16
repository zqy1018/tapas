import Tapas.Parametricity.Loop

namespace Tapas

open Lean Meta Elab Term

/-- Infer effects with least-fixpoint `while`/`repeat` semantics. Order parameters
are available during elaboration and retained only when used by the resulting term. -/
syntax (name := inferPartialEffectsStx) "inferPartialEffects% " term : term

@[term_elab inferPartialEffectsStx]
def elabInferPartialEffects : TermElab := fun stx _ => do
  let `(inferPartialEffects% $body:term) := stx | throwUnsupportedSyntax
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let valueType := mkSort (.succ u)
  let monadType ← mkArrow valueType (mkSort (.succ v))
  withLocalDecl `m .implicit monadType fun m => do
    withLocalDecl `instMonad .instImplicit (← mkAppM ``Monad #[m]) fun instMonad => do
      let ccpoType ← withLocalDeclD `α valueType fun α => do
        mkForallFVars #[α] (← mkAppOptM ``Order.CCPO #[some (mkApp m α)])
      withLocalDecl `instCCPO .instImplicit ccpoType fun ccpo => do
        withLocalDecl `instMonoBind .instImplicit
            (← mkAppOptM ``Order.MonoBind #[some m, none, none]) fun mono => do
          let loopInst ← mkAppOptM ``Parametricity.PartialLoop.instForIn
            (#[m, instMonad, ccpo, mono].map some)
          -- A local instance takes precedence over the standard loop, without
          -- changing any scoped instances in the surrounding environment.
          withLetDecl `instPartialLoop (← inferType loopInst) loopInst fun localLoop => do
            let resultType ← mkFreshExprMVar valueType
            let e ← inferEffectBody body m (mkApp m resultType)
            let e := (← instantiateMVars e).replaceFVar localLoop loopInst
            let e ← mkLambdaFVars #[ccpo, mono] e (usedOnly := true)
            mkLambdaFVars #[m, instMonad] e

end Tapas
