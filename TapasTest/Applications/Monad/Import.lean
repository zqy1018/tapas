module

import TapasTest.Applications.Monad.Program
import TapasTest.Applications.Monad.EffectRelation

open Tapas.Parametricity Tapas.LogicalRelation TapasTest.Applications.Monad.Program

namespace TapasTest.Applications.Monad.Import

-- Both generated and hand-written rules survive module import.
def fromImported := infer_effects% do
  let a ← usesUnknown
  let b ← unknownHelper
  pure (a + b)
derive_parametric fromImported

def executable : Option Nat := fromImported (m := Option)

theorem certificate : some (fromImported (m := Id)).run = executable :=
  fromImported.parametric _ TapasTest.Applications.Monad.EffectRelation.idToOption

example : executable = some 74 := rfl
example : some (fromImported (m := Id)).run = executable := certificate

open Lean in
run_cmd do
  let env ← getEnv
  unless (getParametricRules env ``usesUnknown).contains ``usesUnknown.parametric &&
      (getParametricRules env ``unknownHelper).contains ``manualTranslation &&
      (getInterfaceRelation? env ``Choose).isSome do
    throwError "imported parametricity metadata is missing"

#guard_axioms fromImported.parametric ⊆ []
#guard_axioms certificate ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Import
