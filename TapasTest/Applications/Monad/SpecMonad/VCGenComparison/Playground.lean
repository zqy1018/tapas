module

import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.BenchmarkCases
import TapasTest.Applications.Monad.SpecMonad.Normalizer

/-!
# vcgen and normalization, side by side

Each section proves one upstream goal several ways, with the tactics a user would write:

* vcgen: unfold the program, run `vcgen` with the case's specs, then `grind` on each VC.
* Normalization: apply the case's soundness bridge, proved once for every `n` by parametricity;
  normalize the VC in a specification monad with `normalize_spec`; then call `grind` once.

These follow the benchmark's `vcgen`, `vcgen-finish-simp`, and `normalize` routes in the
hand-written-specs tier, and for the two add/sub cases also in the library tier (see
[PROTOCOL.md](PROTOCOL.md)), except that `simp only` unfolds the program, and without the
benchmark's timers and audits. `#time` reports each example's time, kernel checking included.
The examples run one after another, so each time is its own; opening the file runs all of them,
in about 35 s on the machine that measured the times in the comments. Change `n` to try other
sizes. At a large `n`, keep the cursor out of the proofs: the goal view would print every VC.
-/

set_option experimental.vcgen true
-- Check each proof before the next command starts, so that `#time` includes kernel checking.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Playground

-- vcgen needs `Std.WP`'s scoped instances; `normalize_spec` is scoped in `Normalizer`.
open Std.WP Normalizer

/-! ## AddSubCancel: normalization is faster, more so without hand-written specs

Each step adds and subtracts the same value, and both routes leave the same single VC. Upstream
wrote the specs of `get` and `set` by hand so that vcgen skips the small steps of lifting Lean's
own specs through `StateT`. Without them, vcgen slows down, while normalization with Lean's own
`PredTrans` instances is as fast as with hand-written ones. -/

-- vcgen with upstream's specs: about 1.6 s.
#time example : AddSubCancel.Goal 2200 := by
  unfold AddSubCancel.Goal
  intro post
  simp only [AddSubCancel.loop, AddSubCancel.step]
  vcgen [AddSubCancel.spec_get_StateT, AddSubCancel.spec_set_StateT']
  all_goals grind

-- vcgen with Lean's own specs: about 4.1 s. LetBinding registers the same two specs, so both
-- copies are erased.
#time example : AddSubCancel.Goal 2200 := by
  unfold AddSubCancel.Goal
  intro post
  simp only [AddSubCancel.loop, AddSubCancel.step]
  vcgen [-AddSubCancel.spec_get_StateT, -AddSubCancel.spec_set_StateT',
    -LetBinding.spec_get_StateT, -LetBinding.spec_set_StateT']
  all_goals grind

-- Normalization with hand-written `PredTrans` instances: about 0.7 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : AddSubCancel.Goal 2200 := by
  apply HandWrittenSpecs.plain_sound
  intro post s hs
  normalize_spec Lean.Order.PredTrans
  grind

-- Normalization with Lean's own `PredTrans` instances: about 0.7 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : AddSubCancel.Goal 2200 := by
  apply Library.plain_sound
  intro post s hs
  normalize_spec Lean.Order.PredTrans
  grind

/-! ## AddSubCancelDeep: the same loop in a deeper monad stack

The stack has six transformers. Without upstream's specs of `getThe` and `set`, vcgen lifts Lean's
own specs through the layers above the `Nat` state at every operation; normalization is again as
fast with Lean's own `PredTrans` instances as with hand-written ones. -/

-- vcgen with upstream's specs: about 0.4 s.
#time example : AddSubCancelDeep.Goal 500 := by
  unfold AddSubCancelDeep.Goal
  intro post
  simp only [AddSubCancelDeep.loop, AddSubCancelDeep.step]
  vcgen [AddSubCancelDeep.Spec.M_getThe_Nat, AddSubCancelDeep.Spec.M_set_Nat]
  all_goals grind

-- vcgen with Lean's own specs: about 5.7 s. AddSubCancel's and LetBinding's `StateT` specs would
-- apply to the `Nat` state, so they are erased too.
#time example : AddSubCancelDeep.Goal 500 := by
  unfold AddSubCancelDeep.Goal
  intro post
  simp only [AddSubCancelDeep.loop, AddSubCancelDeep.step]
  vcgen [-AddSubCancelDeep.Spec.M_getThe_Nat, -AddSubCancelDeep.Spec.M_set_Nat,
    -AddSubCancel.spec_get_StateT, -AddSubCancel.spec_set_StateT',
    -LetBinding.spec_get_StateT, -LetBinding.spec_set_StateT']
  all_goals grind

-- Normalization with hand-written `PredTrans` instances: about 0.2 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : AddSubCancelDeep.Goal 500 := by
  apply HandWrittenSpecs.deep_sound
  intro post r s u hs
  normalize_spec Lean.Order.PredTrans
  grind

-- Normalization with Lean's own `PredTrans` instances: about 0.2 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : AddSubCancelDeep.Goal 500 := by
  apply Library.deep_sound
  intro post r s u hs
  normalize_spec Lean.Order.PredTrans
  grind

/-! ## MatchSplit: normalization is faster

`step` matches on the state, which is symbolic, so vcgen splits at every step and leaves `n + 1`
VCs, each proved by its own `grind` call. Normalization leaves one proposition with the `match`es
inside, which one `grind` call proves. To read the VCs, put the cursor after `vcgen` or
`normalize_spec` in the first pair, at `n = 2`. -/

example : MatchSplit.Goal 2 := by
  unfold MatchSplit.Goal
  simp only [MatchSplit.loop, MatchSplit.step]
  vcgen [MatchSplit.spec_get, MatchSplit.spec_set, MatchSplit.spec_throw]
  all_goals grind

-- The scoped rules are the `if` rules that the benchmark gives `grind` for normalized VCs.
open scoped Control.FunctionApplication Control.PredTrans in
example : MatchSplit.Goal 2 := by
  apply HandWrittenSpecs.match_sound
  intro s hs
  normalize_spec Lean.Order.PredTrans
  grind

-- vcgen: about 5.2 s.
#time example : MatchSplit.Goal 80 := by
  unfold MatchSplit.Goal
  simp only [MatchSplit.loop, MatchSplit.step]
  vcgen [MatchSplit.spec_get, MatchSplit.spec_set, MatchSplit.spec_throw]
  all_goals grind

-- Normalization: about 0.04 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : MatchSplit.Goal 80 := by
  apply HandWrittenSpecs.match_sound
  intro s hs
  normalize_spec Lean.Order.PredTrans
  grind

/-! ## PurePrecond: vcgen is faster

`flipp`'s two contracts hold only under a pure precondition on the state. vcgen proves each
precondition while it generates and leaves no VC. Normalization keeps the contracts as `flipp`'s
specification, so its one VC is a conjunction of `2 * n + 1` facts such as `(!true) = false`,
which one `grind` call proves, slowly at a large `n`. -/

-- vcgen: about 0.2 s.
#time example : PurePrecond.Goal 1000 := by
  unfold PurePrecond.Goal
  simp only [PurePrecond.loop, PurePrecond.step]
  vcgen [PurePrecond.Spec.flipp_true, PurePrecond.Spec.flipp_false]
  all_goals grind

-- Normalization: about 6.6 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : PurePrecond.Goal 1000 := by
  apply Pure.sound
  intro s hs
  normalize_spec Lean.Order.PredTrans
  grind

/-! ## GetThrowSet: vcgen with `finish` is faster

Each step throws if the state exceeds a bound, which never happens here. Plain vcgen leaves
`n + 1` VCs, as in MatchSplit; normalization leaves one proposition with `n` nested `if`s for
`grind` to split. `vcgen … with finish` runs `grind` during generation, sharing its E-graph
across the branches and dropping the unreachable throws; upstream adds
`simplifying_assumptions [Nat.add_assoc]`. -/

-- vcgen, then `grind` on each VC: about 2.8 s.
#time example : GetThrowSet.Goal 80 := by
  unfold GetThrowSet.Goal
  simp only [GetThrowSet.loop, GetThrowSet.step]
  vcgen [GetThrowSet.spec_get, GetThrowSet.spec_set, GetThrowSet.spec_throw]
  all_goals grind

-- vcgen with `finish`: about 0.2 s.
#time example : GetThrowSet.Goal 80 := by
  unfold GetThrowSet.Goal
  simp only [GetThrowSet.loop, GetThrowSet.step]
  vcgen [GetThrowSet.spec_get, GetThrowSet.spec_set, GetThrowSet.spec_throw]
    simplifying_assumptions [Nat.add_assoc] with finish

-- Normalization: about 4.2 s.
open scoped Control.FunctionApplication Control.PredTrans in
#time example : GetThrowSet.Goal 80 := by
  apply HandWrittenSpecs.throw_set_sound
  intro s hs
  normalize_spec Lean.Order.PredTrans
  grind

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Playground
