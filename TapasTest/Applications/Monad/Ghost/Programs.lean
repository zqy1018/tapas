module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Ghost.Basic
meta import TapasTest.Applications.Monad.Ghost.Basic -- shake: keep (required by #guard/#eval)

open Tapas.Parametricity Tapas.LogicalRelation TapasTest.Applications.Monad.Ghost.Basic

namespace TapasTest.Applications.Monad.Ghost.Programs

section

/-! ## One program, several counters

The program is written once against `MonadGhostOf`; nothing below re-elaborates it. -/

-- Keep ghost updates abstract instead of selecting the default erased interpretation.
attribute [-instance] erasedGhost in
def countVals (l : List Nat) (target : Nat) := infer_effects% do
  let mut c := 0
  for x in l do
    MonadGhostOf.ghost (I := Nat) 2
    if x == target then
      c := c + 1
  MonadGhostOf.ghost (I := Nat) 1
  pure c

derive_parametric countVals

-- Check the full generated interface: no interpretation-specific hypothesis is added.
example (l : List Nat) (t : Nat) {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] [MonadGhostOf Nat m] [MonadGhostOf Nat n]
    (relation : ComputationRelation m n) (hm : Monad.Rel relation)
    (hg : MonadGhostOf.Rel (I := Nat) relation) :
    relation (countVals (m := m) l t) (countVals (m := n) l t) :=
  countVals.parametric l t relation hm hg

abbrev Counted : Type → Type := StateT Nat Id
abbrev Unary : Type → Type := StateT (List PUnit) Id
abbrev Plain : Type → Type := Id

local instance countedStep : GhostUpdateStep Nat Nat where
  step n s := s + n

local instance unaryStep : GhostUpdateStep Nat (List PUnit) where
  step n s := List.replicate n ⟨⟩ ++ s

/-! ## The instrumented program is still the program -/

theorem countVals_certificate (l : List Nat) (t : Nat) :
    Erase Nat Id (countVals (m := Counted) l t) (countVals (m := Plain) l t) :=
  countVals.parametric l t _ Erase.monadRel Erase.ghostRel

/-- Instrumentation does not change the result, from any initial credit. -/
theorem countVals_erase (l : List Nat) (t : Nat) (s : Nat) :
    Prod.fst <$> countVals (m := Counted) l t s = countVals (m := Plain) l t :=
  Erase.run_eq (countVals_certificate l t) s

/- The ghost updates leave no trace in the generated code, as long as the compiler can
*specialize* `countVals`: at a call site that fixes both `m` and the `MonadGhostOf`
instance, the compiler emits a copy of `countVals` with that instance inlined, and under
`erasedGhost` each `MonadGhostOf.ghost` call becomes `pure ⟨⟩` and is folded away together
with the bind that consumed it. `countVals` itself is compiled once for an unknown `m`, so
its own IR still calls the instance field; it is the specialized copy that is ghost-free.
Fixing `m` is all it takes: elaborating `def run := countVals (m := Plain)` under
`set_option trace.compiler.ir.result true` prints that copy, and its loop body is a
`Nat.decEq` and a `Nat.add` with nothing else in it. The same holds for `PlainOpt`, so this
is not an artifact of `Id`. Specializing at `Counted` instead selects `stateGhost`, and the
copy then carries each update as an ordinary `Nat.add` on the threaded state. -/

-- The runtime interpretation runs, with no counter present at all.
#guard Id.run (countVals (m := Plain) [1, 2, 2, 3, 2] 2) == 3
-- The same program, instrumented, exposes the cost as an ordinary value.
#guard Id.run (countVals (m := Counted) [1, 2, 2, 3, 2] 2 0) == (3, 11)

/-! ## The counter may be represented differently -/

theorem countVals_unary_certificate (l : List Nat) (t : Nat) :
    Reindex List.length Id (countVals (m := Unary) l t) (countVals (m := Counted) l t) :=
  countVals.parametric l t _ (Reindex.monadRel _)
    (Reindex.ghostRel _ (by
      intro n s
      change (List.replicate n PUnit.unit ++ s).length = s.length + n
      simp [Nat.add_comm]))

/-- The unary run computes the same number the numeric run does. -/
theorem countVals_unary (l : List Nat) (t : Nat) (s : List PUnit) :
    (fun p => (p.1, p.2.length)) <$> countVals (m := Unary) l t s
      = countVals (m := Counted) l t s.length :=
  Reindex.run_eq _ (countVals_unary_certificate l t) s

#guard Id.run ((countVals (m := Unary) [1, 2, 2, 3, 2] 2 []).2.length) == 11

/-! ## Simple Run irrelevance -/

theorem countVals_shift_certificate (l : List Nat) (t : Nat) (d : Nat) :
    Reindex (· + d) Id (countVals (m := Counted) l t) (countVals (m := Counted) l t) :=
  countVals.parametric l t (Reindex (· + d) Id) (Reindex.monadRel _)
    (Reindex.ghostRel _ (fun n s => Nat.add_right_comm s n d))

theorem countVals_shift (l : List Nat) (t : Nat) (s d : Nat) :
    (fun p => (p.1, p.2 + d)) <$> countVals (m := Counted) l t s
      = countVals (m := Counted) l t (s + d) :=
  Reindex.run_eq _ (countVals_shift_certificate l t d) s

/-! ## Range loops need no rewriting

`for i in [0:n]` recurses through a private helper, so `derive_parametric` cannot reach it;
`Tapas.Parametricity.StdLoops` registers the translation instead. The program below is
written exactly as it would be without any of this. -/

attribute [-instance] erasedGhost in
def bumpN (n : Nat) := infer_effects% do
  let mut acc := 0
  for _ in [0:n] do
    MonadGhostOf.ghost (I := Nat) 2
    acc := acc + 1
  pure acc

derive_parametric bumpN

theorem bumpN_erase (n s : Nat) :
    Prod.fst <$> bumpN (m := Counted) n s = bumpN (m := Plain) n :=
  Erase.run_eq (bumpN.parametric n _ Erase.monadRel Erase.ghostRel) s

#guard Id.run (bumpN (m := Plain) 5) == 5
#guard Id.run (bumpN (m := Counted) 5 0) == (5, 10)

/-! ## Loops defined by a least fixpoint

`Id` has no uniform `CCPO`, so a `while` program is erased into `Option` instead. The
admissibility premise is discharged once by `Erase.admissible`. -/

attribute [-instance] erasedGhost in
def drain (l : List Nat) := infer_effects_partial% do
  let mut tmp := l
  while tmp.length > 0 do
    MonadGhostOf.ghost (I := Nat) 1
    tmp := tmp.tail
  pure tmp.length

derive_parametric drain

abbrev CountedOpt : Type → Type := StateT Nat Option
abbrev PlainOpt : Type → Type := Option

theorem drain_certificate (l : List Nat) :
    Erase Nat Option (drain (m := CountedOpt) l) (drain (m := PlainOpt) l) :=
  drain.parametric l _ Erase.monadRel Erase.ghostRel (fun {_} => Erase.admissible)

theorem drain_erase (l : List Nat) (s : Nat) :
    Prod.fst <$> drain (m := CountedOpt) l s = drain (m := PlainOpt) l :=
  Erase.run_eq (drain_certificate l) s

#guard (drain (m := PlainOpt) [1, 2, 3]) == some 0
#guard (drain (m := CountedOpt) [1, 2, 3] 0) == some (0, 3)

end

/-! ## Unrestricted ghost state

Setting the alphabet to `σ → σ` gives ghost state with no restriction on the updates: the
program may store anything, computed from any real data it holds. Erasure still holds —
it never depended on what the updates do. -/

abbrev Arbitrary : Type → Type := StateT Nat Id

local instance arbitraryStep : GhostUpdateStep (Nat → Nat) Nat where
  step f s := f s

attribute [-instance] erasedGhost in
/-- The ghost update is an arbitrary function, and it depends on the program's real data. -/
def mixed (xs : List Nat) := infer_effects% do
  let mut total := 0
  for x in xs do
    total := total + x
    MonadGhostOf.ghost (I := Nat → Nat) (fun g => g * 2 + x)
  pure total

derive_parametric mixed

theorem mixed_erase (xs : List Nat) (s : Nat) :
    Prod.fst <$> mixed (m := Arbitrary) xs s = mixed (m := Plain) xs :=
  Erase.run_eq (mixed.parametric xs _ Erase.monadRel Erase.ghostRel) s

#guard Id.run (mixed (m := Plain) [1, 2, 3]) == 6
#guard Id.run (mixed (m := Arbitrary) [1, 2, 3] 0) == (6, 11)

-- Think this as a counterexample for `Reindex.ghostRel` when `hstep` does not hold
example : ¬ MonadGhostOf.Rel (I := (Nat → Nat)) (Reindex (· + 1) Id) := by
  intro h
  have := congrArg Prod.snd (h.ghost (fun g => g * 2) 0)
  exact absurd this (by decide)

/-! ## More complicated ghost state -/

section

abbrev Logged : Type → Type := StateT (List Nat) Id

local instance historyStep : GhostUpdateStep Nat (List Nat) where
  step x h := x :: h

local instance updateCountStep : GhostUpdateStep Nat Nat where
  step _ s := s + 1

theorem history_certificate (l : List Nat) (t : Nat) :
    Reindex List.length Id (countVals (m := Logged) l t)
      (countVals (m := Counted) l t) :=
  countVals.parametric l t (Reindex List.length Id) (Reindex.monadRel _)
    (Reindex.ghostRel _ (fun _ _ => List.length_cons ..))

/-- The counting run computes the length of the history the logging run records. -/
theorem history_length (l : List Nat) (t : Nat) (h : List Nat) :
    (fun p => (p.1, p.2.length)) <$> countVals (m := Logged) l t h
      = countVals (m := Counted) l t h.length :=
  Reindex.run_eq _ (history_certificate l t) h

#guard Id.run ((countVals (m := Logged) [1, 2, 2] 2 []).2) == [1, 2, 2, 2]

end

/-! ## Boundaries -/

-- A tick interpretation that also reports the counter would not fit the capability: the
-- class has no way to read it, which is exactly what makes `erasedGhost` available.
example : (MonadGhostOf.ghost 7 : Plain PUnit) = pure ⟨⟩ := rfl

-- An interpretation may spend credit however it likes and still erase.
theorem odd_step_erases :
    MonadGhostOf.Rel (left := stateGhost (inst := ⟨fun n s => s * 2 + n⟩)) (right := erasedGhost)
      (Erase Nat Id) := by
  letI : GhostUpdateStep Nat Nat := ⟨fun n s => s * 2 + n⟩
  exact Erase.ghostRel

#guard_axioms MonadGhostOf.Rel.ghost, Erase.monadRel, Erase.ghostRel, Erase.run_eq,
  Erase.admissible, Reindex.monadRel, Reindex.ghostRel, Reindex.run_eq, countVals.parametric,
  countVals_certificate, countVals_erase, countVals_unary_certificate, countVals_unary,
  countVals_shift_certificate, countVals_shift, bumpN.parametric, bumpN_erase,
  mixed.parametric, mixed_erase, history_certificate, history_length, drain.parametric,
  drain_certificate, drain_erase, odd_step_erases ⊆ [propext, Classical.choice, Quot.sound]

-- Erasure and reindexing of a terminating program need no choice.
#guard_axioms countVals_erase, countVals_shift ⊆ [propext, Quot.sound]

-- The `partial_fixpoint` program does need it, through the order structure its least fixpoint
-- is taken in. A `⊆` bound cannot state that an axiom is present, so this one stays a print.
/-- info: '_private.TapasTest.Applications.Monad.Ghost.Programs.0.TapasTest.Applications.Monad.Ghost.Programs.drain_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms drain_erase

end TapasTest.Applications.Monad.Ghost.Programs
