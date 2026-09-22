module

import TapasTest.Applications.Monad.PartialFixpoint
public import Tapas.Applications.Monad.Loop
import all Tapas.Applications.Monad.Loop -- inspect the imported certificate's proof
import all Init.Internal.Order.Basic -- proofs unfold FlatOrder.mk
import Std.Tactic.BVDecide.Normalize

/-!
The scoped least-fixpoint loop instance, reached by `open scoped Tapas.Parametricity.PartialLoop`
and a signature that binds the order parameters by hand. This is the mechanism underneath
`infer_effects_partial`, which infers those parameters instead; `PartialEffectInference.lean`
covers that route. The signatures below are written out because which instance a `while` loop
elaborates with, inside the scope and outside it, is the subject.
-/

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order

namespace TapasTest.Applications.Monad.Loop

-- Importing the module leaves the standard loop implementation selected.
def standard {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : m Nat := do
  let mut n := 0
  while n < 3 do
    n := n + 1
  pure n

/-- error: parametricity: no applicable translation for Lean.Loop.forIn; use `derive_parametric Lean.Loop.forIn` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric standard

section
open scoped Tapas.Parametricity.PartialLoop

def countUntil {m : Type → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (keepGoing : Nat → m Bool) (initial : Nat) : m Nat := do
  let mut n := initial
  while ← keepGoing n do
    n := n + 1
  pure n

derive_parametric countUntil

def control {m : Type → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (limit : Nat) (early : m Bool) : m Nat := do
  let mut n := 0
  let mut acc := 0
  while n < limit do
    n := n + 1
    if n % 2 == 0 then continue
    if n > 5 then break
    acc := acc + n
    if ← early then return acc + 100
  pure acc

derive_parametric control

-- Effect inference alone cannot supply the uniform CCPO family, so even inside
-- the scope this elaborates with the standard instance and remains unsupported.
def inferred := infer_effects% do
  let mut n := 0
  while n < 3 do
    n := n + 1
  pure n

/-- error: parametricity: no applicable translation for Lean.Loop.forIn; use `derive_parametric Lean.Loop.forIn` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric inferred

end

-- The scope does not leak past its section, even where order instances exist.
example {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (init : Nat) (body : Unit → Nat → m (ForInStep Nat)) :
    ForIn.forIn (m := m) Lean.Loop.mk init body = Lean.Loop.forIn Lean.Loop.mk init body := rfl

open TapasTest.Applications.Monad.PartialFixpoint

-- Positive configurations bound the counter; zero makes the loop run forever.
def sourceCondition (n : Nat) : Source Bool := fun cfg => some (cfg == 0 || decide (n < cfg))
def targetCondition (n : Nat) : Target Bool := fun cfg => some (cfg.1 == 0 || decide (n < cfg.1))

theorem conditions_related (n : Nat) : R (sourceCondition n) (targetCondition n) := by
  rintro cfg cfg' rfl
  rfl

theorem countUntil_related (initial : Nat) :
    R (countUntil sourceCondition initial) (countUntil targetCondition initial) :=
  countUntil.parametric R monadRel sourceCondition targetCondition conditions_related initial
    relation_admissible

private def countBody {m : Type → Type} [Monad m]
    (p : Nat → m Bool) (_ : Unit) (n : Nat) : m (ForInStep Nat) := do
  if ← p n then pure (.yield (n + 1)) else pure (.done n)

private theorem countUntil_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    [∀ α, CCPO (m α)] [MonoBind m] (p : Nat → m Bool) (n : Nat) :
    countUntil p n = PartialLoop.loop (countBody p) n := by
  simp only [countUntil, ForIn.forIn, PartialLoop.forIn, bind_pure]
  rfl

-- Prove divergence by least-fixpoint induction; never execute the infinite case.
theorem source_diverges (initial : Nat) : countUntil sourceCondition initial 0 = none := by
  rw [countUntil_eq]
  have h : ∀ n, PartialLoop.loop (countBody sourceCondition) n 0 = none := by
    apply PartialLoop.loop.fixpoint_induct (m := Source) (body := countBody sourceCondition)
      (motive := fun recur => ∀ n, recur n 0 = none)
    · exact admissible_pi_apply (fun _ (f : Source Nat) => f 0 = none) (fun _ =>
        admissible_apply (fun _ (x : Option Nat) => x = none) 0
          (admissible_flatOrder _ rfl))
    · intro recur ih n
      simpa [countBody, sourceCondition, bind, ReaderT.bind, pure, ReaderT.pure] using ih (n + 1)
  exact h initial

theorem target_diverges (initial : Nat) (flag : Bool) :
    countUntil targetCondition initial (0, flag) = none :=
  (countUntil_related initial 0 (0, flag) rfl).symm.trans (source_diverges initial)

-- Both normal exit and the control-flow cases execute under the selected least fixpoint.
#guard countUntil sourceCondition 1 4 == some 4
#guard countUntil targetCondition 1 (4, true) == some 4
#guard countUntil sourceCondition 7 4 == some 7
#guard control 10 (some false) == some 9
#guard control 10 (some true) == some 101
#guard control 0 (some true) == some 0
#guard control 10 (none : Option Bool) == none

-- A standard loop is given no least-fixpoint certificate, and the partial loop instance
-- does not leak into one.
#guard_no_parametric standard, inferred
#guard_uses standard, inferred ∩ [PartialLoop.instForIn] = ∅

-- The programs inside the scope elaborate with the partial loop instance, and their
-- translations reuse the imported loop certificate rather than re-deriving it.
#guard_uses countUntil, control ⊇ [PartialLoop.instForIn]
#guard_uses countUntil.parametric, control.parametric ⊇ [PartialLoop.forIn.parametric]

-- That certificate is itself proved by least-fixpoint induction.
#guard_uses PartialLoop.loop.parametric ⊇ [fix_rel]

#guard_axioms PartialLoop.loop.parametric, PartialLoop.forIn.parametric,
  countUntil.parametric, control.parametric, countUntil_related, source_diverges,
  target_diverges ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Loop
