import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Freer.Basic

/-!
Lower a request for a pair into two individual reads. The output is another Freer
program, whose interpretation agrees with the original whenever the handlers agree
on the lowering of each request. Parametricity connects this syntax transformation
back to the original Final program.
-/

namespace TapasTest.Applications.Monad.Freer.Lowering

open Tapas.Parametricity TapasTest.Applications.Monad.Freer.Basic

universe u v v' w

/-- Correct translations of individual requests compose into a correct translation of any tree. -/
theorem fold_lower {E : Type u → Type v} {F : Type u → Type v'}
    (translate : (α : Type u) → E α → Freer F α)
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    (source : (α : Type u) → E α → m α) (target : (α : Type u) → F α → m α)
    (hop : ∀ α (op : E α), Freer.fold target (translate α op) = source α op)
    {α : Type u} (tree : Freer E α) :
    Freer.fold target (Freer.fold translate tree) = Freer.fold source tree := by
  induction tree with
  | pure a => rfl
  | impure op k ih =>
    change Freer.fold target (Freer.bind (translate _ op) (fun x => Freer.fold translate (k x))) =
      source _ op >>= fun x => Freer.fold source (k x)
    rw [Freer.fold_bind, hop]
    exact congrArg (fun f => source _ op >>= f) (funext ih)

inductive HighOp : Type → Type where
  | readPair : HighOp (Nat × Nat)

inductive LowOp : Type → Type where
  | read : LowOp Nat

def lowerOp : (α : Type) → HighOp α → Freer LowOp α
  | _, .readPair => do
    let first ← LowOp.read
    let second ← LowOp.read
    pure (first, second)

/-- Replace every pair request by two reads, retaining the program's continuations. -/
def lower {α : Type} (tree : Freer HighOp α) : Freer LowOp α :=
  Freer.fold lowerOp tree

-- LawfulMonad does not assign meaning to readPair. The equality below is the
-- operation-specific obligation needed to justify this lowering.
theorem lower_correct {m : Type → Type w} [Monad m] [LawfulMonad m]
    (source : (α : Type) → HighOp α → m α) (target : (α : Type) → LowOp α → m α)
    (hpair : source _ .readPair = do
      let first ← target _ .read
      let second ← target _ .read
      pure (first, second))
    {α : Type} (tree : Freer HighOp α) :
    Freer.fold target (lower tree) = Freer.fold source tree := by
  apply fold_lower lowerOp source target ?_ tree
  intro α op
  cases op
  exact hpair.symm

-- Subtraction makes the order of the two returned values observable.
def difference : Final.{0, 0, w} HighOp Nat := fun {_} _ h => do
  let pair ← h _ .readPair
  pure (pair.1 - pair.2)

derive_parametric difference (repr := m)

def compiledDifference : Freer LowOp Nat := lower (toFreer difference)

-- The compiled artifact contains only low-level reads, in their original order.
example : compiledDifference =
    .impure .read (fun first => .impure .read (fun second => .pure (first - second))) := rfl

/-- Executing the lowered tree agrees with executing the original final program. -/
theorem difference_correct {m : Type → Type w} [Monad m] [LawfulMonad m]
    (source : (α : Type) → HighOp α → m α) (target : (α : Type) → LowOp α → m α)
    (hpair : source _ .readPair = do
      let first ← target _ .read
      let second ← target _ .read
      pure (first, second)) :
    Freer.fold target compiledDifference = difference source :=
  (lower_correct source target hpair (toFreer difference)).trans
    (toFinal_toFreer_rel difference difference difference.parametric source)

-- Each read consumes one input; exhausted input yields zero without consuming anything.
def readHandler : (α : Type) → LowOp α → StateM (List Nat) α
  | _, .read => fun input => match input with
    | [] => (0, [])
    | first :: rest => (first, rest)

-- The high-level interpreter obtains the pair directly from the input list.
def pairHandler : (α : Type) → HighOp α → StateM (List Nat) α
  | _, .readPair => fun input => match input with
    | [] => ((0, 0), [])
    | [first] => ((first, 0), [])
    | first :: second :: rest => ((first, second), rest)

theorem handlers_compatible : pairHandler _ .readPair = (do
    let first ← readHandler _ .read
    let second ← readHandler _ .read
    pure (first, second)) := by
  funext input
  cases input with
  | nil => rfl
  | cons first rest => cases rest <;> rfl

-- Return values and remaining input agree for every input list. The proof uses
-- the generic compiler theorem, rather than unfolding this particular program.
theorem difference_run_eq (input : List Nat) :
    (Freer.fold readHandler compiledDifference).run input = (difference pairHandler).run input :=
  congrArg (fun program => program.run input)
    (difference_correct pairHandler readHandler handlers_compatible)

#guard ((difference pairHandler).run [7, 3, 99]).run == (4, [99])
#guard ((Freer.fold readHandler compiledDifference).run [7, 3, 99]).run == (4, [99])
#guard ((Freer.fold readHandler compiledDifference).run [3, 7, 99]).run == (0, [99])
#guard ((Freer.fold readHandler compiledDifference).run [7]).run == (7, [])
#guard ((Freer.fold readHandler compiledDifference).run []).run == (0, [])

#guard_uses difference_correct ⊇ [lower_correct, toFinal_toFreer_rel, difference.parametric]
#guard_uses difference_run_eq ⊇ [difference_correct, handlers_compatible]
#guard_axioms difference.parametric ⊆ []
#guard_axioms fold_lower, lower_correct, difference_correct, handlers_compatible,
  difference_run_eq ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.Lowering
