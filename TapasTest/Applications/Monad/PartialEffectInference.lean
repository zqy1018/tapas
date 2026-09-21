import TapasTest.TestingUtils

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order

namespace TapasTest.Applications.Monad.PartialEffectInference

-- No explicit monad, capability, order parameters, or open-scoped command.
def advance (stop : Nat) := infer_effects_partial% do
  let bound ← readThe Nat
  while (← getThe Nat) < bound do
    let n ← getThe Nat
    set (n + 1)
    if n + 1 == stop then return n + 1
  getThe Nat

derive_parametric advance

-- Order requirements are retained when calling an already inferred loop program.
def caller (stop : Nat) := infer_effects_partial% do
  let n ← advance stop
  pure (n + 10)

derive_parametric caller

def nested (limit : Nat) := infer_effects_partial% do
  let mut count := 0
  let mut i := 0
  while i < limit do
    let mut j := 0
    while j < i do
      j := j + 1
      if j == 2 then continue
      count := count + 1
      if count == 4 then break
    i := i + 1
  pure count

derive_parametric nested

def repeatUntil (limit : Nat) := infer_effects_partial% do
  let mut n := 0
  repeat
    n := n + 1
  until n ≥ limit
  pure n

derive_parametric repeatUntil

def pureProgram {α : Type u} (a : α) := infer_effects_partial% pure a
derive_parametric pureProgram (repr := m)

example {α : Type u} {m : Type u → Type v} [Monad m] (a : α) :
    pureProgram (m := m) a = pure a := rfl

def tick := infer_effects_partial% do
  let n ← getThe Nat
  set (n + 1)
  pure n

derive_parametric tick

example {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] [MonadStateOf Nat m] [MonadStateOf Nat n]
    (R : ComputationRelation m n) (hm : Monad.Rel R) (hs : MonadStateOf.Rel (σ := Nat) R) :
    R (tick (m := m)) (tick (m := n)) := tick.parametric R hm hs

-- Even an error inside the new entry point must not affect subsequent elaboration.
/-- error: Unknown identifier `missingPartialEffect` -/
#guard_msgs in
#check infer_effects_partial% missingPartialEffect

def oldInferred := infer_effects% do
  let mut n := 0
  while n < 3 do
    n := n + 1
  pure n

/-- error: parametricity: no applicable translation for Lean.Loop.forIn; use `derive_parametric Lean.Loop.forIn` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric oldInferred

abbrev Source := ReaderT Nat (StateT Nat Option)
abbrev Target := ReaderT (Nat × Bool) (StateT Nat Option)

local instance targetReader : MonadReaderOf Nat Target where
  read := fun cfg => pure cfg.1

def R : ComputationRelation Source Target := fun {_} x y =>
  ∀ cfg cfg', cfg = cfg'.1 → x cfg = y cfg'

theorem relation_admissible ⦃α : Type⦄ : AdmissibleRel (R (α := α)) :=
  AdmissibleRel.pi (fun _ _ _ => AdmissibleRel.eq)

theorem monadRel : Monad.Rel R :=
  Monad.Rel.ofPureBind R (fun _ _ _ _ => rfl) (by
    intro α β x y f g hxy hfg cfg cfg' hcfg
    funext s
    change (x cfg s).bind (fun (a, s') => f a cfg s') =
      (y cfg' s).bind (fun (a, s') => g a cfg' s')
    rw [congrFun (hxy cfg cfg' hcfg) s]
    cases y cfg' s with
    | none => rfl
    | some result => exact congrFun (hfg result.1 cfg cfg' hcfg) result.2)

theorem readerRel : MonadReaderOf.Rel (right := targetReader) R where
  read := by rintro cfg cfg' rfl; rfl

theorem stateRel : MonadStateOf.Rel (σ := Nat) R where
  get := by intro cfg cfg' _; rfl
  set := by intro n cfg cfg' _; rfl
  modifyGet := by intro α f cfg cfg' _; rfl

theorem advance_related (stop : Nat) : R (advance (m := Source) stop) (advance (m := Target) stop) :=
  advance.parametric stop R monadRel readerRel stateRel relation_admissible

theorem caller_related (stop : Nat) : R (caller (m := Source) stop) (caller (m := Target) stop) :=
  caller.parametric stop R monadRel readerRel stateRel relation_admissible

#guard advance (m := Source) 3 5 0 == some (3, 3)
#guard advance (m := Target) 3 (5, true) 0 == some (3, 3)
#guard advance (m := Source) 9 5 0 == some (5, 5)
#guard advance (m := Target) 9 (5, false) 0 == some (5, 5)
#guard advance (m := Source) 3 5 7 == some (7, 7)
#guard caller (m := Target) 3 (5, true) 0 == some (13, 3)
#guard nested (m := Option) 4 == some 4
#guard repeatUntil (m := Option) 0 == some 1
#guard repeatUntil (m := Option) 4 == some 4
#guard (pureProgram (m := Id) (7 : Nat)).run == 7
#guard (tick (m := StateM Nat) 4).run == (4, 5)

-- The new entry point selects the least-fixpoint loop, does not fall back to a standard one
-- silently, and its translations reuse the shipped loop certificate.
#guard_uses advance, nested, repeatUntil ⊇ [PartialLoop.instForIn]
#guard_uses advance, nested, repeatUntil ∩ [Lean.instForInLoopUnitOfMonad] = ∅
#guard_uses advance.parametric, nested.parametric, repeatUntil.parametric ⊇
  [PartialLoop.forIn.parametric]

-- A caller reuses the inferred program's certificate.
#guard_uses caller.parametric ⊇ [advance.parametric]

-- A program that does not loop gains no order parameter.
#guard_uses type pureProgram, tick, oldInferred ∩ [CCPO, MonoBind] = ∅

-- Using the new entry point does not change what `infer_effects%` elaborates to. A
-- hand-written standard-loop signature is `Loop.lean`'s subject, not this file's.
#guard_no_parametric oldInferred
#guard_uses oldInferred ∩ [PartialLoop.instForIn] = ∅

#guard_axioms advance, caller, nested, repeatUntil, pureProgram, tick,
  advance.parametric, caller.parametric, nested.parametric, repeatUntil.parametric,
  pureProgram.parametric, tick.parametric, advance_related, caller_related ⊆
  [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.PartialEffectInference
