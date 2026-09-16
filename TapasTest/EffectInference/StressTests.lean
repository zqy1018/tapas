import TapasTest.EffectInference.Tests

namespace TestMonad.EffectInference.StressTests

open TestMonad.EffectInference
open TestMonad.EffectInference.Tests

/-! ## Group 1: a Reader/Except/State/Emit audit pipeline -/

structure AuditResult where
  before : Nat
  label : String
  adapted : String
deriving Repr, DecidableEq

/- Eight monadic binds/statements, including four inferred callees. -/
def validatedAudit :=
  inferEffects% do
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
  inferEffects% do
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
  inferEffects% do
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
  inferEffects% do
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
  inferEffects% do
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
  inferEffects% do
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

end TestMonad.EffectInference.StressTests
