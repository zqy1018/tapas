module

import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.BenchmarkCases
import all TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Models
import TapasTest.TestingUtils

set_option experimental.vcgen true
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open TapasTest.Applications.Monad.SpecMonad Std.WP

-- The abstract flip uses precisely the two original partial contracts, in every tier.
#guard_uses VCGenComparison.flipp_negates ⊇
  [PurePrecond.Spec.flipp_true, PurePrecond.Spec.flipp_false]
#guard_uses VCGenComparison.flip_sound, VCGenComparison.CustomMonad.flip_sound ⊇
  [VCGenComparison.flipp_negates]

-- The harness also checks each tier's spec use, the final execution goal, and single VCs against
-- vcgen's. Upstream's Sym solver fails at n = 1, whose only step adds and subtracts 0: nothing is
-- left to cancel.
#eval VCGenComparison.Harness.runTwo VCGenComparison.cases [2, 3]
