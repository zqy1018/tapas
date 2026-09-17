import Tapas

namespace TapasTest.Applications.Monad.EffectInference

/- Repeated state operations produce one capability binder. The state type of the
plain `get` is only fixed by the later `set`, and the `MonadState` goal it produces
is normalized to the same `MonadStateOf` that `set` requires. -/
def stateOnly :=
  infer_effects% do
    let n ← get
    set (n + 1)
    pure n

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m Nat) :=
  @stateOnly

example : Id.run (StateT.run (stateOnly (m := StateT Nat Id)) 10) =
    (10, 11) := rfl

/- Reader and exception capabilities are inferred independently. -/
def readLabel :=
  infer_effects% do
    readThe String

example :
    ({m : Type → Type} → [Monad m] → [MonadReaderOf String m] → m String) :=
  @readLabel

example : Id.run (ReaderT.run (readLabel (m := ReaderT String Id)) "abc") =
    "abc" := rfl

def requireNonempty (label : String) :=
  infer_effects% do
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
  infer_effects% do
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
  infer_effects% do
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
  infer_effects% do
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
  infer_effects% do
    if useState then
      get
    else
      let label ← read
      pure <| String.length label

example :
    ((useState : Bool) → {m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadReaderOf String m] → m Nat) :=
  @branchEffects

/- Local reader adaptation and reading are two separate capabilities. -/
def locallyRead :=
  infer_effects%
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
  infer_effects% do
    let n ← liftM (m := Except String) (Except.ok 41)
    pure (n + 1)

example :
    ({m : Type → Type} → [Monad m] → [MonadLiftT (Except String) m] → m Nat) :=
  @liftFromExcept

example : Id.run (ExceptT.run
    (liftFromExcept (m := ExceptT String Id))) = Except.ok 42 := rfl

/- Dropping that annotation leaves the lifted monad undetermined, so the
capability it produces cannot be abstracted. -/
/--
error: don't know how to synthesize implicit argument `m`
  @liftM (Except ?m.8) m ?effect0 Nat (Except.ok 41)
context:
m : Type → Type ?u.3
instMonad : Monad m
⊢ Type → Type ?u.9

Note: the inferred requirement
  MonadLiftT (Except ?m.8) m
still has an undetermined argument, so it cannot become an instance parameter: no caller could supply one.
---
error: don't know how to synthesize implicit argument `ε`
  @Except.ok ?m.8 Nat 41
context:
m : Type → Type ?u.3
instMonad : Monad m
⊢ Type ?u.9

Note: the inferred requirement
  MonadLiftT (Except ?m.8) m
still has an undetermined argument, so it cannot become an instance parameter: no caller could supply one.
-/
#guard_msgs in
def liftFromUnknownMonad :=
  infer_effects% do
    let n ← liftM (Except.ok 41)
    pure (n + 1)

/- A custom monad-indexed class is discovered without being registered. -/
class MonadEmit (ω : Type) (m : Type → Type) where
  emit : ω → m PUnit

def emit [MonadEmit ω m] (message : ω) : m PUnit :=
  MonadEmit.emit message

instance [Monad m] : MonadEmit String (StateT (List String) m) where
  emit message messages := pure (PUnit.unit, messages ++ [message])

def emitLength (message : String) :=
  infer_effects% do
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
  infer_effects% do
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
  infer_effects% do
    let n ← liftM (m := Id) (41 : Id Nat)
    pure (n + 1)

example :
    ({m : Type → Type} → [Monad m] → m Nat) :=
  @liftFromIdNeedsNoExtraCapability

/-! ## Group 1: a Reader/Except/State/Emit audit pipeline -/

structure AuditResult where
  before : Nat
  label : String
  adapted : String
deriving Repr, DecidableEq

/- Eight monadic binds/statements, including four inferred callees. -/
def validatedAudit :=
  infer_effects% do
    let rawLabel ← readLabel
    let label ← requireNonempty rawLabel
    let before ← stateOnly
    let current ← getThe Nat
    let emittedLength ← emitLength label
    let adapted ← locallyRead
    set (current + emittedLength)
    emit adapted
    pure ({ before := before, label := label, adapted := adapted } : AuditResult)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadReaderOf String m] → [MonadExceptOf String m] →
      [MonadStateOf Nat m] → [MonadEmit String m] →
      [MonadWithReaderOf String m] → m AuditResult) :=
  @validatedAudit

structure PipelineResult where
  firstBefore : Nat
  twice : Nat × Nat
  branchValue : Nat
  secondBefore : Nat
  checked : String
deriving Repr, DecidableEq

/- Eight more binds; the first layer's five capabilities must propagate. -/
def auditPipeline :=
  infer_effects% do
    let first ← validatedAudit
    let twice ← stateTwice
    let branchValue ← branchEffects true
    let second ← validatedAudit
    let current ← getThe Nat
    set (current + branchValue)
    emit first.label
    let checked ← requireNonempty second.label
    pure ({
      firstBefore := first.before
      twice
      branchValue
      secondBefore := second.before
      checked
    } : PipelineResult)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadReaderOf String m] → [MonadExceptOf String m] →
      [MonadStateOf Nat m] → [MonadEmit String m] →
      [MonadWithReaderOf String m] → m PipelineResult) :=
  @auditPipeline

abbrev AuditStack :=
  StateT (List String) (ReaderT String (ExceptT String (StateT Nat Id)))

example :
    Id.run (StateT.run
      (ExceptT.run
        (ReaderT.run
          (StateT.run (auditPipeline (m := AuditStack)) []) "abc")) 10) =
      (Except.ok ({
        firstBefore := 10
        twice := (14, 15)
        branchValue := 16
        secondBefore := 16
        checked := "abc"
      }, ["abc", "abc!", "abc", "abc!", "abc"]), 36) := rfl

/-! ## Group 2: two state capabilities across repeated transactions -/

structure DualRoundResult where
  initialNat : Nat
  initialFlag : Bool
  observedNat : Nat
  observedFlag : Bool
  label : String
deriving Repr, DecidableEq

/- Eight binds/statements and two distinct `MonadStateOf` requirements. -/
def dualStateRound :=
  infer_effects% do
    let (initialNat, initialFlag) ← twoStates
    let observedNat ← getThe Nat
    let observedFlag ← getThe Bool
    set (observedNat + 10)
    set (!observedFlag)
    let label ← readLabel
    let label ← requireNonempty label
    emit label
    pure ({
      initialNat := initialNat
      initialFlag := initialFlag
      observedNat := observedNat
      observedFlag := observedFlag
      label := label
    } : DualRoundResult)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadStateOf Bool m] →
      [MonadReaderOf String m] → [MonadExceptOf String m] →
      [MonadEmit String m] → m DualRoundResult) :=
  @dualStateRound

structure DualScenarioResult where
  firstInitial : Nat
  secondInitial : Nat
  adapted : String
  finalFlag : Bool
deriving Repr, DecidableEq

/- Eight more binds; both rounds' requirements are deduplicated transitively. -/
def dualStateScenario :=
  infer_effects% do
    let first ← dualStateRound
    let second ← dualStateRound
    let adapted ← locallyRead
    let checked ← requireNonempty adapted
    emit checked
    let currentNat ← getThe Nat
    let finalFlag ← getThe Bool
    set (currentNat + checked.length)
    pure ({
      firstInitial := first.initialNat
      secondInitial := second.initialNat
      adapted
      finalFlag
    } : DualScenarioResult)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadStateOf Nat m] → [MonadStateOf Bool m] →
      [MonadReaderOf String m] → [MonadExceptOf String m] →
      [MonadEmit String m] → [MonadWithReaderOf String m] →
      m DualScenarioResult) :=
  @dualStateScenario

abbrev DualStateStack :=
  StateT (List String)
    (ReaderT String (ExceptT String (StateT Nat (StateT Bool Id))))

example :
    Id.run (StateT.run
      (StateT.run
        (ExceptT.run
          (ReaderT.run
            (StateT.run (dualStateScenario (m := DualStateStack)) []) "xy")) 2)
      false) =
      ((Except.ok ({
        firstInitial := 2
        secondInitial := 13
        adapted := "xy!"
        finalFlag := false
      }, ["xy", "xy", "xy!"]), 27), false) := rfl

/-! ## Group 3: explicit base lifting combined with inferred effects -/

structure LiftedResult where
  before : Nat
  payload : Nat
  adapted : String
deriving Repr, DecidableEq

/- Eight binds/statements; failure in the first lift short-circuits the rest. -/
def liftedScenario (source : Except String Nat) :=
  infer_effects% do
    let payload ← liftM (m := Except String) source
    let rawLabel ← readLabel
    let _label ← requireNonempty rawLabel
    let before ← stateOnly
    let current ← getThe Nat
    let adapted ← locallyRead
    emit adapted
    set (current + payload + adapted.length)
    pure ({ before := before, payload := payload, adapted := adapted } : LiftedResult)

example :
    ((source : Except String Nat) → {m : Type → Type} → [Monad m] →
      [MonadLiftT (Except String) m] → [MonadReaderOf String m] →
      [MonadExceptOf String m] → [MonadStateOf Nat m] →
      [MonadWithReaderOf String m] → [MonadEmit String m] →
      m LiftedResult) :=
  @liftedScenario

example :
    Id.run (StateT.run
      (ExceptT.run
        (ReaderT.run
          (StateT.run
            (liftedScenario (.ok 5) (m := AuditStack)) []) "a")) 3) =
      (Except.ok ({ before := 3, payload := 5, adapted := "a!" }, ["a!"]), 11) := rfl

example :
    Id.run (StateT.run
      (ExceptT.run
        (ReaderT.run
          (StateT.run
            (liftedScenario (.error "upstream") (m := AuditStack)) []) "a")) 3) =
      (Except.error "upstream", 3) := rfl

/- Eight binds, including two calls to the six-capability lifted program. -/
def liftedBatch :=
  infer_effects% do
    let first ← liftedScenario (.ok 2)
    let second ← liftedScenario (.ok 3)
    let rawLabel ← readLabel
    let label ← requireNonempty rawLabel
    let emittedLength ← emitLength label
    let current ← getThe Nat
    set (current + emittedLength)
    emit first.adapted
    pure (first.before + second.before + current + emittedLength)

example :
    ({m : Type → Type} → [Monad m] →
      [MonadLiftT (Except String) m] → [MonadReaderOf String m] →
      [MonadExceptOf String m] → [MonadStateOf Nat m] →
      [MonadWithReaderOf String m] → [MonadEmit String m] → m Nat) :=
  @liftedBatch

example :
    Id.run (StateT.run
      (ExceptT.run
        (ReaderT.run
          (StateT.run (liftedBatch (m := AuditStack)) []) "z")) 1) =
      (Except.ok (20, ["z!", "z!", "z", "z!"]), 13) := rfl

end TapasTest.Applications.Monad.EffectInference
