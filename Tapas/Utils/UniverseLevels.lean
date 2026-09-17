import Lean

namespace Tapas.Utils

open Lean

/-- Keep shared universe parameters and rename `params`, avoiding existing names. -/
def renameLevelParams (params : Array Name) (sharedLevels : CollectLevelParams.State)
    (notFreshLevels : CollectLevelParams.State := {}) : Array Level := Id.run do
  -- Reserve shared and source names before choosing any target name.
  -- CHECK Will there be a more efficient union operation?
  let mut notFreshLevels := (sharedLevels.params ++ params).foldl (init := notFreshLevels) fun s param =>
    CollectLevelParams.visitLevel (.param param) s
  let mut levels := #[]
  for param in params do
    let level := if sharedLevels.params.contains param then Level.param param
      else notFreshLevels.getUnusedLevelParam (param.appendAfter "_target")
    -- CHECK Can this be partially reduced?
    notFreshLevels := CollectLevelParams.visitLevel level notFreshLevels
    levels := levels.push level
  return levels

end Tapas.Utils
