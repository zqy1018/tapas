import TapasTest.Applications.Monad.StackSuggestion.Basic

/-!
`#suggest_stack` on programs whose capabilities were inferred: which transformers supply
them, which orderings discharge them, and which of those orderings return the same thing.
-/

namespace TapasTest.Applications.Monad.StackSuggestion.Programs

/- One capability leaves one stack, and no choice to make. -/
def counter :=
  infer_effects% do
    let n ← get
    set (n + 1)
    pure n

/--
info: counter requires 1 capability of `m`:
  MonadStateOf Nat m  ←  StateT Nat

1 stack discharges all of them:
  StateT Nat Id
    unfolds to (α : Type) → Nat → α × Nat
-/
#guard_msgs in
#suggest_stack counter

/- A reader can sit anywhere: both orderings take the same two arguments and return the
same result, so the choice between them is free. -/
def greet :=
  infer_effects% do
    let name ← readThe String
    let n ← getThe Nat
    pure (name, n)

/--
info: greet requires 2 capabilities of `m`:
  MonadReaderOf String m  ←  ReaderT String
  MonadStateOf Nat m  ←  StateT Nat

2 stacks discharge all of them, and all return the same result
(up to the order of a run's arguments and the nesting of its products):
  ReaderT String (StateT Nat Id)
    unfolds to (α : Type) → String → Nat → α × Nat
  StateT Nat (ReaderT String Id)
    unfolds to (α : Type) → Nat → String → α × Nat
-/
#guard_msgs in
#suggest_stack greet

/- State and exceptions do not commute, and the two results say how. With `ExceptT`
outermost the state comes back beside the error; with `StateT` outermost it is inside the
`Except`, so a failing run returns no state at all. -/
def withdraw (amount : Nat) :=
  infer_effects% do
    let balance ← get
    if amount ≤ balance then set (balance - amount) else throw "insufficient"
    pure balance

/--
info: withdraw requires 2 capabilities of `m`:
  MonadStateOf Nat m  ←  StateT Nat
  MonadExceptOf String m  ←  ExceptT String

2 stacks discharge all of them, returning 2 different results
(up to the order of a run's arguments and the nesting of its products):
  result 1:
    StateT Nat (ExceptT String Id)
      unfolds to (α : Type) → Nat → Except String (α × Nat)
  result 2:
    ExceptT String (StateT Nat Id)
      unfolds to (α : Type) → Nat → Except String α × Nat
-/
#guard_msgs in
#suggest_stack withdraw

example : ((withdraw 10 (m := StateT Nat (ExceptT String Id))).run 3).run =
    Except.error "insufficient" := rfl

example : (withdraw 10 (m := ExceptT String (StateT Nat Id))).run.run 3 =
    (Except.error "insufficient", 3) := rfl

/- Two states commute: only the order of the arguments and the nesting of the returned
products differ, which a caller can undo. -/
def twoStates :=
  infer_effects% do
    let n ← get
    let b ← get
    set (n + 1)
    set (!b)
    pure (n, b)

/--
info: twoStates requires 2 capabilities of `m`:
  MonadStateOf Nat m  ←  StateT Nat
  MonadStateOf Bool m  ←  StateT Bool

2 stacks discharge all of them, and all return the same result
(up to the order of a run's arguments and the nesting of its products):
  StateT Nat (StateT Bool Id)
    unfolds to (α : Type) → Nat → Bool → (α × Nat) × Bool
  StateT Bool (StateT Nat Id)
    unfolds to (α : Type) → Bool → Nat → (α × Bool) × Nat
-/
#guard_msgs in
#suggest_stack twoStates

/- A class the user wrote needs no registration: its own instance names the transformer
that supplies it. Here the capability is not a positional copy -- `MonadEmit String` is
supplied by `StateT (List String)` -- and the transformer is still found. -/
class MonadEmit (ω : Type) (m : Type → Type) where
  emit : ω → m PUnit

def emit [MonadEmit ω m] (message : ω) : m PUnit :=
  MonadEmit.emit message

instance [Monad m] : MonadEmit String (StateT (List String) m) where
  emit message messages := pure (PUnit.unit, messages ++ [message])

def audited :=
  infer_effects% do
    let n ← get
    emit "read"
    if n = 0 then throw "empty" else pure n

/- `MonadEmit` has no lifting instance, so `StateT (List String)` has to be outermost:
anything above it, a state as much as an exception, leaves `MonadEmit String` unsynthesized.
That pins one of the three layers and rules out four of the six orderings. The two that
survive still disagree on whether a failing run returns the log. -/
/--
info: audited requires 3 capabilities of `m`:
  MonadStateOf Nat m  ←  StateT Nat
  MonadEmit String m  ←  StateT (List String)
  MonadExceptOf String m  ←  ExceptT String

2 stacks discharge all of them, returning 2 different results
(up to the order of a run's arguments and the nesting of its products):
  result 1:
    StateT (List String) (StateT Nat (ExceptT String Id))
      unfolds to (α : Type) → List String → Nat → Except String ((α × List String) × Nat)
  result 2:
    StateT (List String) (ExceptT String (StateT Nat Id))
      unfolds to (α : Type) → List String → Nat → Except String (α × List String) × Nat
-/
#guard_msgs in
#suggest_stack audited

/- A program needing nothing but `Monad` constrains no stack. -/
def pureProgram :=
  infer_effects% do
    pure 42

/-- info: pureProgram needs no capability beyond `Monad`; any monad runs it. -/
#guard_msgs in
#suggest_stack pureProgram

/- A capability no transformer in scope supplies is reported rather than guessed at.
`MonadLiftT` names two monads, so which of them a stack would be is not determined. -/
def liftFromExcept :=
  infer_effects% do
    let n ← liftM (m := Except String) (Except.ok 41)
    pure (n + 1)

/--
error: suggest_stack: no transformer in scope supplies
  MonadLiftT (Except String) m
-/
#guard_msgs in
#suggest_stack liftFromExcept

/- Enough distinct capabilities and the orderings stop being a list worth reading. -/
def sevenStates :=
  infer_effects% do
    let a ← getThe Nat
    let b ← getThe Bool
    let c ← getThe String
    let d ← getThe (List Nat)
    let e ← getThe (Option Nat)
    let f ← getThe Char
    let g ← getThe (Array Nat)
    pure (a, b, c, d, e, f, g)

/-- error: suggest_stack: 5040 candidate stacks is too many to list -/
#guard_msgs in
#suggest_stack sevenStates

end TapasTest.Applications.Monad.StackSuggestion.Programs
