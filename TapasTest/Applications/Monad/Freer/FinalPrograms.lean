import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Freer.Basic

/-!
State programs written directly as `Final` values. Ordinary `get` and `set` calls
become requests to the supplied handler; sequencing, branching, and recursion stay
ordinary Lean code. Each generated parametricity theorem supplies the premise of
`toFinal_toFreer`, so reification needs no separate correctness proof for the program.
-/

namespace TapasTest.Applications.Monad.Freer.FinalPrograms

open Tapas.Parametricity TapasTest.Applications.Monad.Freer.Basic

universe w w'

inductive StateOp : Type → Type where
  | get : StateOp Nat
  | set : Nat → StateOp Unit

-- Translation of `do let old ← get; set (old + amount); pure old`.
def add (amount : Nat) : Final.{0, 0, w} StateOp Nat := fun {_} _ h => do
  let old ← h _ .get
  h _ (.set (old + amount))
  pure old

derive_parametric add (repr := m)

example (amount : Nat) : Final.Rel (add.{w} amount) (add.{w'} amount) :=
  add.parametric amount

-- Freer StateOp returns values in Type 1. The same-universe roundtrip theorem
-- therefore compares handler functions into an arbitrary lawful m : Type → Type 1.
theorem add_roundtrip (amount : Nat) {m : Type → Type 1} [Monad m] [LawfulMonad m] :
    toFinal (toFreer (add amount)) (m := m) = add amount (m := m) :=
  toFinal_toFreer (add amount) (add.parametric amount)

-- Translation of a state program whose next operation depends on the value read.
def withdraw (amount : Nat) : Final.{0, 0, w} StateOp Bool := fun {_} _ h => do
  let balance ← h _ .get
  if amount ≤ balance then
    h _ (.set (balance - amount))
    pure true
  else
    pure false

derive_parametric withdraw (repr := m)

example (amount : Nat) : Final.Rel (withdraw.{w} amount) (withdraw.{w'} amount) :=
  withdraw.parametric amount

theorem withdraw_roundtrip (amount : Nat) {m : Type → Type 1} [Monad m] [LawfulMonad m] :
    toFinal (toFreer (withdraw amount)) (m := m) = withdraw amount (m := m) :=
  toFinal_toFreer (withdraw amount) (withdraw.parametric amount)

-- Reuse withdraw for each request and count the successful withdrawals.
-- The roundtrip proof below stays the same despite this program's recursion.
def withdrawMany (amounts : List Nat) : Final.{0, 0, w} StateOp Nat := fun {_} _ h =>
  match amounts with
  | [] => pure 0
  | amount :: rest => do
    let accepted ← withdraw amount h
    let count ← withdrawMany rest h
    pure (if accepted then count + 1 else count)

derive_parametric withdrawMany (repr := m)

example (amounts : List Nat) : Final.Rel (withdrawMany.{w} amounts) (withdrawMany.{w'} amounts) :=
  withdrawMany.parametric amounts

theorem withdrawMany_roundtrip (amounts : List Nat)
    {m : Type → Type 1} [Monad m] [LawfulMonad m] :
    toFinal (toFreer (withdrawMany amounts)) (m := m) = withdrawMany amounts (m := m) :=
  toFinal_toFreer (withdrawMany amounts) (withdrawMany.parametric amounts)

-- The handler recovers the usual state operations.
def stateHandler : (α : Type) → StateOp α → StateM Nat α
  | _, .get => get
  | _, .set value => set value

example (amount : Nat) : add amount stateHandler =
    (do let old ← get; set (old + amount); pure old : StateM Nat Nat) := rfl

example (amount : Nat) : withdraw amount stateHandler =
    (do
      let balance ← get
      if amount ≤ balance then
        set (balance - amount)
        pure true
      else
        pure false : StateM Nat Bool) := rfl

-- Reification produces the expected requests, including the read-dependent write.
example (amount : Nat) : toFreer (add amount) =
    .impure .get (fun old => .impure (.set (old + amount)) (fun _ => .pure old)) := rfl

-- StateM Nat returns values in Type, so this execution uses the cross-universe
-- theorem with two universe instances of the same Final program.
theorem withdrawMany_state_roundtrip (amounts : List Nat) :
    toFinal (toFreer (withdrawMany amounts)) stateHandler = withdrawMany amounts stateHandler :=
  toFinal_toFreer_rel (withdrawMany amounts) (withdrawMany amounts)
    (withdrawMany.parametric amounts) stateHandler

#guard ((add 3 stateHandler).run 5).run == (5, 8)
#guard ((withdraw 3 stateHandler).run 5).run == (true, 2)
#guard ((withdraw 8 stateHandler).run 5).run == (false, 5)
#guard ((withdrawMany [3, 8, 2] stateHandler).run 10).run == (2, 5)
#guard ((toFinal (toFreer (withdrawMany [3, 8, 2])) stateHandler).run 10).run == (2, 5)

#guard_axioms add.parametric, withdraw.parametric, withdrawMany.parametric ⊆ []
#guard_axioms add_roundtrip, withdraw_roundtrip, withdrawMany_roundtrip,
  withdrawMany_state_roundtrip ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.FinalPrograms
