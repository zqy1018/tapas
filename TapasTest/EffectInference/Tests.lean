import Tapas

namespace TestMonad.EffectInference.Tests

open TestMonad.EffectInference

/- Repeated state operations produce one capability binder. The state type of the
plain `get` is only fixed by the later `set`, and the `MonadState` goal it produces
is normalized to the same `MonadStateOf` that `set` requires. -/
def stateOnly :=
  inferEffects% do
    let n ← get
    set (n + 1)
    pure n

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m Nat) :=
  @stateOnly

example : Id.run (StateT.run (stateOnly (m := StateT Nat Id)) 10) =
    (10, 11) := rfl

/- Annotating the binder fixes the state type before `get` is elaborated instead. -/
def stateOnlyWithAnnotatedGet :=
  inferEffects% do
    let n : Nat ← get
    set (n + 1)
    pure n

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m Nat) :=
  @stateOnlyWithAnnotatedGet

/- Reader and exception capabilities are inferred independently. -/
def readLabel :=
  inferEffects% do
    readThe String

example :
    ({m : Type → Type} → [Monad m] → [MonadReaderOf String m] → m String) :=
  @readLabel

example : Id.run (ReaderT.run (readLabel (m := ReaderT String Id)) "abc") =
    "abc" := rfl

def requireNonempty (label : String) :=
  inferEffects% do
    if label.isEmpty then
      throw "empty"
    else
      pure label

example :
    ((label : String) → {m : Type → Type} → [Monad m] →
      [MonadExceptOf String m] → m String) :=
  @requireNonempty

example : requireNonempty "" (m := Except String) =
    Except.error "empty" := rfl

example : requireNonempty "ok" (m := Except String) =
    Except.ok "ok" := rfl

/- Distinct state types remain distinct effects, while each is deduplicated. Two
plain `get`s are enough: each one is normalized to the `MonadStateOf` it is derived
from, which is a capability a two-state stack can still discharge. -/
def twoStates :=
  inferEffects% do
    let n ← get
    let b ← get
    set (n + 1)
    set (!b)
    pure (n, b)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadStateOf Bool m] → m (Nat × Bool)) :=
  @twoStates

abbrev TwoStateStack := StateT Nat (StateT Bool Id)

example :
    Id.run (StateT.run (StateT.run (twoStates (m := TwoStateStack)) 3) false) =
      (((3, false), 4), true) := rfl

/- Calls propagate the inferred requirements of opaque leaf definitions. -/
def workflow :=
  inferEffects% do
    let n ← stateOnly
    let label ← readLabel
    let label ← requireNonempty label
    pure (n, label)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadReaderOf String m] →
      [MonadExceptOf String m] → m (Nat × String)) :=
  @workflow

abbrev WorkflowStack := ReaderT String (ExceptT String (StateT Nat Id))

example :
    Id.run (StateT.run
      (ExceptT.run (ReaderT.run (workflow (m := WorkflowStack)) "abc")) 10) =
      (Except.ok (10, "abc"), 11) := rfl

example :
    Id.run (StateT.run
      (ExceptT.run (ReaderT.run (workflow (m := WorkflowStack)) "")) 10) =
      (Except.error "empty", 11) := rfl

/- Repeated calls to a program still require only one state capability. -/
def stateTwice :=
  inferEffects% do
    let a ← stateOnly
    let b ← stateOnly
    pure (a, b)

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m (Nat × Nat)) :=
  @stateTwice

example : Id.run (StateT.run (stateTwice (m := StateT Nat Id)) 4) =
    ((4, 5), 6) := rfl

/- Both branches contribute to the static may-effect set. -/
def branchEffects (useState : Bool) :=
  inferEffects% do
    if useState then
      get
    else
      let label ← readThe String
      pure label.length

example :
    ((useState : Bool) → {m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadReaderOf String m] → m Nat) :=
  @branchEffects

/- Local reader adaptation and reading are two separate capabilities. -/
def locallyRead :=
  inferEffects%
    withTheReader String (fun s => s ++ "!") do
      readThe String

example :
    ({m : Type → Type} → [Monad m] →
      [MonadWithReaderOf String m] → [MonadReaderOf String m] → m String) :=
  @locallyRead

example : Id.run (ReaderT.run (locallyRead (m := ReaderT String Id)) "abc") =
    "abc!" := rfl

/- `MonadLiftT` can be treated as another inferred capability. -/
def liftFromExcept :=
  inferEffects% do
    let n ← liftM (m := Except String) (Except.ok 41)
    pure (n + 1)

example :
    ({m : Type → Type} → [Monad m] → [MonadLiftT (Except String) m] → m Nat) :=
  @liftFromExcept

example : Id.run (ExceptT.run
    (liftFromExcept (m := ExceptT String Id))) = Except.ok 42 := rfl

/- A custom monad-indexed class is discovered without being registered. -/
class MonadEmit (ω : Type) (m : Type → Type) where
  emit : ω → m PUnit

def emit [MonadEmit ω m] (message : ω) : m PUnit :=
  MonadEmit.emit message

instance [Monad m] : MonadEmit String (StateT (List String) m) where
  emit message messages := pure (PUnit.unit, messages ++ [message])

def emitLength (message : String) :=
  inferEffects% do
    emit message
    pure message.length

example :
    ((message : String) → {m : Type → Type} → [Monad m] →
      [MonadEmit String m] → m Nat) :=
  @emitLength

example : Id.run (StateT.run
    (emitLength "hello" (m := StateT (List String) Id)) []) =
    (5, ["hello"]) := rfl

/- Requirements propagate transitively through an already-composed program. -/
def auditedWorkflow :=
  inferEffects% do
    let (n, label) ← workflow
    emit label
    pure n

example :
    ({m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadReaderOf String m] →
      [MonadExceptOf String m] → [MonadEmit String m] → m Nat) :=
  @auditedWorkflow

abbrev AuditedStack := StateT (List String) WorkflowStack

example :
    Id.run (StateT.run
      (ExceptT.run
        (ReaderT.run
          (StateT.run (auditedWorkflow (m := AuditedStack)) []) "abc")) 10) =
      (Except.ok (10, ["abc"]), 11) := rfl

/- Requirements already derivable from `Monad m` do not enter the set. -/
def liftFromIdNeedsNoExtraCapability :=
  inferEffects% do
    let n ← liftM (m := Id) (41 : Id Nat)
    pure (n + 1)

example :
    ({m : Type → Type} → [Monad m] → m Nat) :=
  @liftFromIdNeedsNoExtraCapability

end TestMonad.EffectInference.Tests
