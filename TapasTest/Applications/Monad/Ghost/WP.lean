module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Ghost.Basic
meta import TapasTest.Applications.Monad.Ghost.Basic -- shake: keep (required by #guard/#eval)
import Std.Tactic.Do
import Std.Internal.Do
import Std.Tactic.BVDecide.Normalize

/-!
Verify loops with invariants that observe their ghost state. The programs use only
`MonadGhostOf` updates; the state is visible to assertions through the standard `StateT` WP.
Parametricity transfers the proved results to interpretations that erase the updates: `Id`
for the for loop and `Option` for the while loop, whose semantics can represent nontermination.
-/

namespace TapasTest.Applications.Monad.Ghost.WP

open Std.Do Basic

/-- A ghost update changes the state seen by assertions. -/
@[spec]
theorem ghost_spec {I σ : Type u} [GhostUpdateStep I σ]
    {m : Type u → Type v} [Monad m] {ps : PostShape} [WPMonad m ps]
    (i : I) (Q : PostCond PUnit (.arg σ ps)) :
    ⦃(spred(fun g => Q.1 ⟨⟩ (GhostUpdateStep.step i g)))⦄
    (MonadGhostOf.ghost i : StateT σ m PUnit)
    ⦃Q⦄ := by
  change Triple (modifyGet fun g => (PUnit.unit, GhostUpdateStep.step i g)) _ Q
  exact Spec.modifyGet_StateT

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

set_option mvcgen.warning false in
/-- The ghost counter records twice the number of completed iterations. -/
theorem countLoop_spec (n initial : Nat) :
    ⦃fun g => ⌜g = initial⌝⦄ countLoop (m := StateT Nat Id) n
      ⦃⇓ result g => ⌜result = n ∧ g = initial + 2 * result⌝⦄ := by
  mvcgen [countLoop] invariants
  | inv1 => ⇓ (cursor, acc) g =>
      ⌜acc = cursor.prefix.length ∧ g = initial + 2 * acc⌝
  all_goals (mleave; simp_all [GhostUpdateStep.step] <;> omega)

/-- The WP proof also establishes the result of the execution with no ghost state. -/
theorem countLoop_erased_result (n : Nat) : (countLoop (m := Id) n).run = n := by
  have hwp := countLoop_spec n 0 0 rfl
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

open scoped Tapas.Parametricity.PartialLoop in
/-- A decreasing measure and a preserved invariant verify a terminating partial loop. -/
@[spec]
theorem partialLoop_spec {β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [∀ α, CCPO (m α)] [MonoBind m] [WPMonad m ps]
    {l : Lean.Loop} {init : β} {body : Unit → β → m (ForInStep β)}
    (variant : WhileVariant β .pure) (inv : WhileInvariant β β ps)
    (step : ∀ b, Triple (body () b) (inv.1 (.inl b))
      (fun r => match r with
        | .yield b' => spred(⌜(variant b').down < (variant b).down⌝ ∧ inv.1 (.inl b'))
        | .done b' => inv.1 (.inr b'), inv.2)) :
    Triple (forIn l init body) (inv.1 (.inl init))
      (fun b => inv.1 (.inr b), inv.2) := by
  change Triple (PartialLoop.loop body init) _ _
  induction init using (measure fun b => (variant b).down).wf.induction with
  | h b ih =>
    rw [PartialLoop.loop.eq_def]
    refine Triple.bind (body () b) _ (step b) ?_
    intro r
    cases r with
    | done b' => apply Triple.pure; exact SPred.entails.refl _
    | yield b' =>
      apply Triple.iff.mpr
      apply SPred.pure_elim SPred.and_elim_l
      intro hlt
      exact SPred.and_elim_r.trans (ih b' hlt)

attribute [-instance] erasedGhost in
/-- Count with a while loop, recording two ghost ticks per iteration. -/
def countWhile (n : Nat) := infer_effects_partial% do
  let mut acc := 0
  while acc < n do
    MonadGhostOf.ghost (I := Nat) 2
    acc := acc + 1
  pure acc

derive_parametric countWhile

set_option mvcgen.warning false in
/-- The while invariant relates its mutable counter to the current ghost value. -/
theorem countWhile_spec (n initial : Nat) :
    ⦃fun g => ⌜g = initial⌝⦄ countWhile (m := StateT Nat Option) n
      ⦃⇓ result g => ⌜result = n ∧ g = initial + 2 * result⌝⦄ := by
  mvcgen [countWhile] invariants
  | inv1 => fun acc => ⟨n - acc⟩
  | inv2 => ⇓ cursor g => ⌜match cursor with
      | .inl acc => acc ≤ n ∧ g = initial + 2 * acc
      | .inr result => result = n ∧ g = initial + 2 * result⌝
  all_goals (mleave; simp_all [GhostUpdateStep.step] <;> omega)

#guard countWhile (m := StateT Nat Option) 0 7 == some (0, 7)
#guard countWhile (m := StateT Nat Option) 5 7 == some (5, 17)
#guard countWhile (m := Option) 5 == some 5

set_option mvcgen.warning false in
/-- Erasing the while loop's ghost state preserves its terminating result. -/
theorem countWhile_erased_result (n : Nat) : countWhile (m := Option) n = some n := by
  have herase : Prod.fst <$> (countWhile (m := StateT Nat Option) n).run 0 =
      countWhile (m := Option) n := Erase.run_eq
    (countWhile.parametric n (Erase Nat Option) Erase.monadRel Erase.ghostRel
      (fun {_} => Erase.admissible)) 0
  -- Use erasure to turn the result equality into a WP goal for the projected run.
  -- The computation is still in `Option`: `Prod.fst <$> (countWhile ...).run 0`.
  apply Std.Do.Option.of_wp_eq herase (fun result => result = some n)
  -- Move the postcondition through `map` and `run`, obtaining the `StateT Nat Option`
  -- WP goal for `countWhile` with initial ghost state 0.
  simp only [WP.map, WP.StateT_run]
  -- Reuse the loop specification. The remaining conditions establish the initial
  -- state and deduce the result equality from the stronger postcondition about result and ghost state.
  have hspec := countWhile_spec n 0
  mvcgen [hspec]
  all_goals (mleave; simp_all)

#guard_uses type countWhile ⊇ [MonadGhostOf]
#guard_uses countWhile_spec ⊇ [partialLoop_spec, ghost_spec]
#guard_uses countWhile_erased_result ⊇ [countWhile_spec, countWhile.parametric, Erase.run_eq]
#guard_axioms partialLoop_spec, countWhile.parametric, countWhile_spec, countWhile_erased_result
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Ghost.WP
