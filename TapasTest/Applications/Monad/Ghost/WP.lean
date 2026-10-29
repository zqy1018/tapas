module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Ghost.Basic
meta import TapasTest.Applications.Monad.Ghost.Basic -- shake: keep (required by #guard/#eval)
import Std.Tactic.Do
import Std.WP
import Std.Tactic.BVDecide.Normalize

set_option experimental.vcgen true

/-!
Verify loops with invariants that observe their ghost state. The programs use only
`MonadGhostOf` updates; the state is visible to assertions through the standard `StateT` WP.
Parametricity transfers the proved results to interpretations that erase the updates: `Id`
for the for loop and `Option` for the while loop, whose semantics can represent nontermination.
-/

namespace TapasTest.Applications.Monad.Ghost.WP

open Std.WP Lean.Order Basic

/-- A ghost update changes the state seen by assertions. -/
@[spec]
theorem ghost_spec {I σ : Type u} [GhostUpdateStep I σ]
    {m : Type u → Type v} [Monad m] {Pred EPred : Type u}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (i : I) (Q : PUnit → σ → Pred) (E : EPred) :
    ⦃fun g => Q ⟨⟩ (GhostUpdateStep.step i g)⦄
    (MonadGhostOf.ghost i : StateT σ m PUnit) ⦃Q; E⦄ := by
  change Triple (modifyGet (m := StateT σ m) fun g => (PUnit.unit, GhostUpdateStep.step i g)) _ Q E
  exact Spec.modifyGet_StateT _ _

-- Keep the program polymorphic in the interpretation of its ghost updates.
attribute [-instance] erasedGhost in
/-- Count iterations, recording two ghost ticks per iteration. -/
def countLoop (n : Nat) := infer_effects% do
  let mut acc := 0
  for _ in [0:n] do
    MonadGhostOf.ghost (I := Nat) 2
    acc := acc + 1
  pure acc

derive_parametric countLoop

local instance countedStep : GhostUpdateStep Nat Nat where
  step n g := g + n

/-- The ghost counter records twice the number of completed iterations. -/
theorem countLoop_spec (n initial : Nat) :
    ⦃fun g => g = initial⦄ countLoop (m := StateT Nat Id) n
      ⦃fun result g => result = n ∧ g = initial + 2 * result⦄ := by
  vcgen [countLoop] invariants
  | inv1 => fun pref suff acc g =>
      (acc = pref.length ∧ g = initial + 2 * acc)
  all_goals (simp [GhostUpdateStep.step] at * <;> omega)

/-- The WP proof also establishes the result of the execution with no ghost state. -/
theorem countLoop_erased_result (n : Nat) : (countLoop (m := Id) n).run = n := by
  have hwp := (countLoop_spec n 0).le_wp 0 rfl
  have herase := Erase.run_eq
    (countLoop.parametric n (Erase Nat Id) Erase.monadRel Erase.ghostRel) 0
  exact herase ▸ hwp.1

#guard (countLoop (m := StateT Nat Id) 0 7).run == (0, 7)
#guard (countLoop (m := StateT Nat Id) 5 7).run == (5, 17)
#guard (countLoop (m := Id) 5).run == 5

#guard_uses type countLoop ⊇ [MonadGhostOf]
#guard_uses countLoop_spec ⊇ [ghost_spec]
#guard_uses countLoop_erased_result ⊇ [countLoop_spec, countLoop.parametric, Erase.run_eq]
#guard_axioms ghost_spec, countLoop.parametric, countLoop_spec, countLoop_erased_result
  ⊆ [propext, Classical.choice, Quot.sound]

/-! The least-fixpoint loop needs its own WP rule. For this experiment the termination
measure depends only on the mutable loop variables; the invariant may also read ghost state. -/

open Lean.Order Tapas.Parametricity

-- CHECK This thing seems general
open scoped Tapas.Parametricity.PartialLoop in
/-- A decreasing measure and a preserved invariant verify a terminating partial loop. -/
@[spec]
theorem partialLoop_spec {β : Type u} {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [Heyting Pred]
    {l : Lean.Loop} {init : β} {body : Unit → β → m (ForInStep β)}
    (variant : Variant β Pred) (inv : WhileInvariant β Pred) (einv : EPred)
    (step : ∀ b (mb : variant.γ), Triple (body () b) (variant.EvalsTo b mb ⊓ inv false b)
      (fun r => match r with
        | .yield b' => variant.EvalsBelow b' mb ⊓ inv false b'
        | .done b' => inv true b') einv) :
    Triple (forIn l init body) (inv false init) (fun b => inv true b) einv := by
  change Triple (PartialLoop.loop body init) _ _ _
  refine Triple.intro <| variant.le_of_total_le init ?_
  refine iSup_le _ _ fun minit => ?_
  suffices key : ∀ n, Acc variant.rel n → ∀ b,
      Triple (PartialLoop.loop body b) (variant.EvalsTo b n ⊓ inv false b)
        (fun b' => inv true b') einv from
    (key minit (variant.wf.apply minit) init).le_wp
  intro n hacc
  induction hacc with
  | intro n _ ih =>
    intro b
    rw [PartialLoop.loop.eq_def]
    refine Triple.bind (body () b) _ _ (step b n) ?_
    intro r
    cases r with
    | done b' => exact Triple.pure b' PartialOrder.rel_refl
    | yield b' =>
      refine Triple.intro <| iSup_meet_le fun mb' => ?_
      rw [meet_comm (P := variant.EvalsTo b' mb'), meet_assoc]
      exact ofProp_meet_le_left fun hlt => (ih mb' hlt b').le_wp

attribute [-instance] erasedGhost in
/-- Count with a while loop, recording two ghost ticks per iteration. -/
def countWhile (n : Nat) := infer_effects_partial% do
  let mut acc := 0
  while acc < n do
    MonadGhostOf.ghost (I := Nat) 2
    acc := acc + 1
  pure acc

derive_parametric countWhile

/-- The while invariant relates its mutable counter to the current ghost value. -/
theorem countWhile_spec (n initial : Nat) :
    ⦃fun g => g = initial⦄ countWhile (m := StateT Nat Option) n
      ⦃fun result g => result = n ∧ g = initial + 2 * result⦄ := by
  vcgen [countWhile] invariants
  | inv2 => Variant.ofMeasure fun acc => n - acc
  | inv1 => fun
    | false, acc, g => acc ≤ n ∧ g = initial + 2 * acc
    | true, acc, g => acc = n ∧ g = initial + 2 * acc
  all_goals (simp [GhostUpdateStep.step] at * <;> omega)

#guard countWhile (m := StateT Nat Option) 0 7 == some (0, 7)
#guard countWhile (m := StateT Nat Option) 5 7 == some (5, 17)
#guard countWhile (m := Option) 5 == some 5

/-- Erasing the while loop's ghost state preserves its terminating result. -/
theorem countWhile_erased_result (n : Nat) : countWhile (m := Option) n = some n := by
  have herase : Prod.fst <$> (countWhile (m := StateT Nat Option) n).run 0 =
      countWhile (m := Option) n := Erase.run_eq
    (countWhile.parametric n (Erase Nat Option) Erase.monadRel Erase.ghostRel
      (fun {_} => Erase.admissible)) 0
  -- Use erasure to turn the result equality into a WP goal for the projected run.
  -- The computation is still in `Option`: `Prod.fst <$> (countWhile ...).run 0`.
  apply Std.WP.Option.of_eq_wp herase (fun result => result = some n)
  -- Move the postcondition through `map` and `run`, obtaining the `StateT Nat Option`
  -- WP goal for `countWhile` with initial ghost state 0.
  apply WPMonad.map_le_wp_map (m := Option) Prod.fst _ _ _
  change wp (countWhile (m := StateT Nat Option) n)
    (fun result _ => some result = some n) (fun _ => none = some n) 0
  -- Reuse the loop specification. The remaining conditions establish the initial
  -- state and deduce the result equality from the stronger postcondition about result and ghost state.
  have hspec := countWhile_spec n 0
  vcgen [hspec]
  all_goals simp_all

#guard_uses type countWhile ⊇ [MonadGhostOf]
#guard_uses countWhile_spec ⊇ [partialLoop_spec, ghost_spec]
#guard_uses countWhile_erased_result ⊇ [countWhile_spec, countWhile.parametric, Erase.run_eq]
#guard_axioms partialLoop_spec, countWhile.parametric, countWhile_spec, countWhile_erased_result
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Ghost.WP
