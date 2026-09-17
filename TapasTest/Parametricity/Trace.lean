import Tapas

namespace TapasTest.Parametricity.Trace

def direct {α : Type} (x : α) : α := x

-- Tracing is silent by default.
#guard_msgs in
derive_parametric direct (repr := α)

-- The goal is captured before its metavariable is assigned.
/--
trace: [Tapas.Parametricity] ✅️ goal:
    α α' : Type
    R : α → α' → Prop
    x : α
    x' : α'
    x_rel : R x x'
    ⊢ R x x'
-/
#guard_msgs in
set_option trace.Tapas.Parametricity true in
derive_parametric direct as directTraced (repr := α)

def source {α : Type} (_n : Nat) (x : α) : α := x
def caller {α : Type} (x : α) : α := source 1 x

@[parametric] theorem mismatch {α β : Type} (R : α → β → Prop)
    (x : α) (y : β) (h : R x y) : R (source 0 x) (source 0 y) := h

@[parametric] theorem unusable {α β : Type} (R : α → β → Prop)
    (x : α) (y : β) (h : False) : R (source 1 x) (source 1 y) := h.elim

-- Enabling trace preserves the ordinary error when all rules fail.
/--
error: parametricity: missing relational premise:
False
-/
#guard_msgs (error, drop trace) in
set_option trace.Tapas.Parametricity true in
derive_parametric caller (repr := α)

-- An application mismatch is visible even though `observing?` swallows it.
/--
[Tapas.Parametricity] ❌️ rule @mismatch: not applicable
    [Tapas.Parametricity] 💥️ application failed: Tactic `apply` failed:
-/
#guard_msgs (trace, drop error, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric caller (repr := α)

@[parametric] theorem usable {α β : Type} (R : α → β → Prop)
    (x : α) (y : β) (h : R x y) : R (source 1 x) (source 1 y) := h

-- A failed premise and its context survive rollback, followed by the successful
-- alternative. Check this part of the tree without pinning `apply`'s full diagnostic.
/--
[Tapas.Parametricity] 💥️ rule @unusable: premise failed
      parametricity: missing relational premise:
      False
    [Tapas.Parametricity] ✅️ application: 1 subgoals
    [Tapas.Parametricity] 💥️ goal:
        α α' : Type
        R : α → α' → Prop
        x : α
        x' : α'
        x_rel : R x x'
        ⊢ False
  [Tapas.Parametricity] ✅️ rule @usable
    [Tapas.Parametricity] ✅️ application: 1 subgoals
    [Tapas.Parametricity] ✅️ goal:
        α α' : Type
        R : α → α' → Prop
        x : α
        x' : α'
        x_rel : R x x'
        ⊢ R x x'
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric caller (repr := α)

/-- info: 'TapasTest.Parametricity.Trace.caller.parametric' does not depend on any axioms -/
#guard_msgs in
#print axioms caller.parametric

abbrev boxedAlias {α : Type} (x : α) : Option α := some x
def boxed {α : Type} (x : α) : Option α := boxedAlias x

-- Normalization records the two endpoints only when they change.
/--
[Tapas.Parametricity] normalize left:
      boxedAlias x
      ↦ some x
  [Tapas.Parametricity] normalize right:
      boxedAlias x'
      ↦ some x'
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric boxed (repr := α)

/-- [Tapas.Parametricity] ✅️ relation constructor Option.Rel.some -/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric boxed as boxedConstructors (repr := α)

def empty {α : Type} : Option α := none

-- The `some` constructor fails before the `none` constructor succeeds.
/--
[Tapas.Parametricity] 💥️ relation constructor Option.Rel.some failed
      Tactic `apply` failed:
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric empty (repr := α)

def conditional {α : Type} (b : Bool) (x y : α) : α := if b then x else y

/--
[Tapas.Parametricity] conditional discriminants:
      left: b = true
      right: b = true
  [Tapas.Parametricity] split: 2 branches
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric conditional (repr := α)

def byCases {α : Type} (b : Bool) (x y : α) : α := Bool.casesOn b x y

/--
[Tapas.Parametricity] match discriminants:
      left: [b]
      right: [b]
  [Tapas.Parametricity] split declined; trying cases on a shared discriminant
  [Tapas.Parametricity] ✅️ cases b: 2 branches
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric byCases (repr := α)

def branchWithProof {α : Type} (b : Bool) (_h : b = true) (x y : α) : α :=
  if b then x else y

-- This branch closes without calling `proveGoal` again, but still appears in the trace.
/-- [Tapas.Parametricity] closed by contradiction -/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric branchWithProof (repr := α)

open Lean.Order in
def indexedSpin {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (k : Nat) : m Nat := indexedSpin (k + 1)
partial_fixpoint

-- Base admissibility cannot apply directly to a relation on functions.
/--
[Tapas.Parametricity] 💥️ admissibility rule R_admissible failed
      Tactic `apply` failed:
-/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric indexedSpin

-- The pointwise rule then lifts it over the shared argument.
/-- [Tapas.Parametricity] ✅️ admissibility rule Tapas.Parametricity.AdmissibleRel.pointwise -/
#guard_msgs (trace, substring := true) in
set_option trace.Tapas.Parametricity true in
derive_parametric indexedSpin as indexedSpinPointwise

end TapasTest.Parametricity.Trace
