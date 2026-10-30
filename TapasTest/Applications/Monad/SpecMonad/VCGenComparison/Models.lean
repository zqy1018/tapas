module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Specification
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.AddSubCancelDeep
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.PurePrecond
import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.TimeSetup

-- `#time_setup` must observe each proof's checking.
set_option Elab.async false

public section

/-!
The operations of the eight cases, interpreted in three tiers. `CustomMonad` uses our own
specification monad with hand-written specs, `HandWrittenSpecs` uses Lean's `PredTrans` with
hand-written specs, and `Library` uses `PredTrans` with Lean's own instances. The specs of
the two `PredTrans` tiers are scoped to their namespaces.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order Std.WP

abbrev NatPred := Nat → Prop
abbrev BoolPred := Bool → Prop
abbrev ReaderPred := Nat → Nat → Prop
abbrev ExceptState := ExceptT String (StateM Nat)
-- `ExceptState` has one exception postcondition, for its `String` errors.
abbrev ExceptEPred := EStack⟨String → NatPred⟩
-- Keep every assertion argument of the deep add/sub stack, including its reader and outer state,
-- and, in `PredTrans`, the exception postconditions of its three `ExceptT` layers.
abbrev DeepPred := String → Nat → Unit → Prop
abbrev DeepEPred :=
  EStack⟨String → DeepPred, Nat → Nat → Unit → Prop, Unit → Unit → Prop⟩

-- Only uncaught throw is used by these cases.
class Throw (m : Type → Type) where
  raise : {α : Type} → String → m α

#time_setup "throw.all.derive_effect_rel" derive_effect_rel Throw

instance executionThrow : Throw ExceptState := ⟨fun message => throw message⟩

-- A call boundary preserves PurePrecond's original partial contracts.
class Flip (m : Type → Type) where
  flipp : Bool → m Unit

#time_setup "flip.all.derive_effect_rel" derive_effect_rel Flip

instance executionFlip : Flip (StateM Bool) := ⟨_root_.PurePrecond.flipp⟩

-- The two upstream contracts of `flipp`, which every tier's soundness proof uses.
#time_setup "flip.all.contract"
theorem flipp_negates (flag b : Bool) (h : b = flag) : (!b) = (!flag) := by
  cases flag with
  | false => exact _root_.PurePrecond.Spec.flipp_false.le_wp b h
  | true => exact _root_.PurePrecond.Spec.flipp_true.le_wp b h

-- The contract is not a library operation, so both `PredTrans` tiers state it the same way.
@[expose] def flipSpec (flag : Bool) : PredTrans BoolPred EStack⟨⟩ Unit :=
  ⟨fun post _ b => b = flag ∧ post () (!flag)⟩

instance specificationFlip : Flip (PredTrans BoolPred EStack⟨⟩) := ⟨flipSpec⟩

#time_setup "flip.predtrans.sound"
theorem flip_sound : Flip.Rel (Sound (m := StateM Bool) (Pred := BoolPred)) where
  flipp flag post epost b h := by
    obtain ⟨hflag, hpost⟩ := h
    change post () (!b)
    rw [flipp_negates flag b hflag]
    exact hpost

namespace CustomMonad

instance natState : MonadStateOf Nat (Spec NatPred) where
  get := fun post s => post s s
  set n := fun post _ => post () n
  modifyGet f := fun post s => post (f s).1 (f s).2

instance deepState : MonadStateOf Nat (Spec DeepPred) where
  get := fun post r s u => post s r s u
  set n := fun post r _ u => post () r n u
  modifyGet f := fun post r s u => post (f s).1 r (f s).2 u

instance readerState : MonadStateOf Nat (Spec ReaderPred) where
  get := fun post r s => post s r s
  set n := fun post r _ => post () r n
  modifyGet f := fun post r s => post (f s).1 r (f s).2

instance readerRead : MonadReaderOf Nat (Spec ReaderPred) where
  read := fun post r s => post r r s

-- Without an exception postcondition, an uncaught throw requires `False`.
instance specificationThrow : Throw (Spec NatPred) := ⟨fun _ _ _ => False⟩

@[expose] def flipSpec (flag : Bool) : Spec BoolPred Unit := fun post b =>
  b = flag ∧ post () (!flag)

instance specificationFlip : Flip (Spec BoolPred) := ⟨flipSpec⟩

#time_setup "state.custom-monad.sound"
theorem nat_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := StateM Nat) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

#time_setup "deep_state.custom-monad.sound"
theorem deep_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := _root_.AddSubCancelDeep.M) (Pred := DeepPred)) where
  get := fun _ _ _ _ _ h => h
  set := fun _ _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ _ h => h

#time_setup "except_state.custom-monad.sound"
theorem except_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

#time_setup "reader_state.custom-monad.sound"
theorem reader_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  get := fun _ _ _ _ h => h
  set := fun _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ h => h

#time_setup "reader_read.custom-monad.sound"
theorem reader_read_sound :
    MonadReaderOf.Rel (ρ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  read := fun _ _ _ _ h => h

#time_setup "throw.custom-monad.sound"
theorem throw_sound : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)) where
  raise := fun _ _ _ _ h => False.elim h

#time_setup "flip.custom-monad.sound"
theorem flip_sound : Flip.Rel (Sound (m := StateM Bool) (Pred := BoolPred)) where
  flipp flag post epost b h := by
    obtain ⟨hflag, hpost⟩ := h
    change post () (!b)
    rw [flipp_negates flag b hflag]
    exact hpost

end CustomMonad

namespace HandWrittenSpecs

-- Hand-written specs, preferred over Lean's `PredTrans` instances in this tier.
scoped instance (priority := high) natState {EPred : Type} :
    MonadStateOf Nat (PredTrans NatPred EPred) where
  get := ⟨fun post _ s => post s s⟩
  set n := ⟨fun post _ _ => post () n⟩
  modifyGet f := ⟨fun post _ s => post (f s).1 (f s).2⟩

-- Read the deep state in one step, like upstream's `Spec.M_getThe_Nat`.
scoped instance (priority := high) deepState :
    MonadStateOf Nat (PredTrans DeepPred DeepEPred) where
  get := ⟨fun post _ r s u => post s r s u⟩
  set n := ⟨fun post _ r _ u => post () r n u⟩
  modifyGet f := ⟨fun post _ r s u => post (f s).1 r (f s).2 u⟩

scoped instance (priority := high) readerState :
    MonadStateOf Nat (PredTrans ReaderPred EStack⟨⟩) where
  get := ⟨fun post _ r s => post s r s⟩
  set n := ⟨fun post _ r _ => post () r n⟩
  modifyGet f := ⟨fun post _ r s => post (f s).1 r (f s).2⟩

scoped instance (priority := high) readerRead :
    MonadReaderOf Nat (PredTrans ReaderPred EStack⟨⟩) where
  read := ⟨fun post _ r s => post r r s⟩

scoped instance specificationThrow : Throw (PredTrans NatPred ExceptEPred) :=
  ⟨fun message => ⟨fun _ epost => epost.1 message⟩⟩

#time_setup "state.hand-written-specs.sound"
theorem nat_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := StateM Nat) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

#time_setup "deep_state.hand-written-specs.sound"
theorem deep_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := _root_.AddSubCancelDeep.M) (Pred := DeepPred)) where
  get := fun _ _ _ _ _ h => h
  set := fun _ _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ _ h => h

#time_setup "except_state.hand-written-specs.sound"
theorem except_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

#time_setup "reader_state.hand-written-specs.sound"
theorem reader_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  get := fun _ _ _ _ h => h
  set := fun _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ h => h

#time_setup "reader_read.hand-written-specs.sound"
theorem reader_read_sound :
    MonadReaderOf.Rel (ρ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  read := fun _ _ _ _ h => h

#time_setup "throw.hand-written-specs.sound"
theorem throw_sound : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)) where
  raise := fun _ _ _ _ h => h

end HandWrittenSpecs

namespace Library

-- Lean's direct state instance would read the reader argument of `ReaderPred`; its lifting
-- instance reaches the state under it.
scoped instance (priority := high) readerState :
    MonadStateOf Nat (PredTrans ReaderPred EStack⟨⟩) :=
  -- can also be defined by `inferInstance`
  instMonadStateOfOfMonadLift (m := PredTrans NatPred EStack⟨⟩)

-- The throwing interface is ours; its interpretation is Lean's `throw`.
scoped instance specificationThrow : Throw (PredTrans NatPred ExceptEPred) :=
  ⟨fun message => throw message⟩

-- The same proofs as in `HandWrittenSpecs`: Lean's specs are also the weakest preconditions.
#time_setup "state.library.sound"
theorem nat_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := StateM Nat) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

-- Lean's lifting instances reach the deep state.
#time_setup "deep_state.library.sound"
theorem deep_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := _root_.AddSubCancelDeep.M) (Pred := DeepPred)) where
  get := fun _ _ _ _ _ h => h
  set := fun _ _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ _ h => h

#time_setup "except_state.library.sound"
theorem except_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)) where
  get := fun _ _ _ h => h
  set := fun _ _ _ _ h => h
  modifyGet := fun _ _ _ _ h => h

#time_setup "reader_state.library.sound"
theorem reader_state_sound :
    MonadStateOf.Rel (σ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  get := fun _ _ _ _ h => h
  set := fun _ _ _ _ _ h => h
  modifyGet := fun _ _ _ _ _ h => h

#time_setup "reader_read.library.sound"
theorem reader_read_sound :
    MonadReaderOf.Rel (ρ := Nat) (Sound (m := ReaderT Nat (StateM Nat)) (Pred := ReaderPred)) where
  read := fun _ _ _ _ h => h

#time_setup "throw.library.sound"
theorem throw_sound : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)) where
  raise := fun _ _ _ _ h => h

end Library

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
