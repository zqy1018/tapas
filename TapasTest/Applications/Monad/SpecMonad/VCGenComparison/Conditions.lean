module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Programs
import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.TimeSetup
import TapasTest.TestingUtils

-- `#time_setup` must observe each proof's checking.
set_option Elab.async false

public section

/-!
Each case's calculated VC and its soundness bridge to the original goal, in the three tiers of
[Models.lean](Models.lean). A VC passes the goal's postcondition and, in `PredTrans`, the goal's
default exception postcondition `⊥`. The two `PredTrans` tiers share each case's VC and bridge,
which take the operation specs as instance arguments; each tier supplies its own.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order Std.WP

-- One program for both add/sub cases, so one VC and bridge for each.
namespace AddSub

@[expose] def plainVC [MonadStateOf Nat (PredTrans NatPred EStack⟨⟩)] (n : Nat) : Prop :=
  ∀ (post : NatPred) s, post s →
    (loop n : PredTrans NatPred EStack⟨⟩ Unit).apply (fun _ => post) ⊥ s

#time_setup "AddSubCancel.predtrans.bridge"
theorem plain_sound [MonadStateOf Nat (PredTrans NatPred EStack⟨⟩)]
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := StateM Nat) (Pred := NatPred)))
    (n : Nat) : plainVC n → _root_.AddSubCancel.Goal n := by
  intro h post
  rw [← plain_loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := StateM Nat)) Sound.monad hstate n
    (fun _ => post) ⊥ s (h post s hs)⟩

@[expose] def deepVC [MonadStateOf Nat (PredTrans DeepPred DeepEPred)] (n : Nat) : Prop :=
  ∀ (post : DeepPred) r s u, post r s u →
    (loop n : PredTrans DeepPred DeepEPred Unit).apply (fun _ => post) ⊥ r s u

#time_setup "AddSubCancelDeep.predtrans.bridge"
theorem deep_sound [MonadStateOf Nat (PredTrans DeepPred DeepEPred)]
    (hstate :
      MonadStateOf.Rel (σ := Nat) (Sound (m := _root_.AddSubCancelDeep.M) (Pred := DeepPred)))
    (n : Nat) : deepVC n → _root_.AddSubCancelDeep.Goal n := by
  intro h post
  rw [← deep_loop_eq n]
  exact ⟨fun r s u hs => loop.parametric (Sound (m := _root_.AddSubCancelDeep.M)) Sound.monad
    hstate n (fun _ => post) ⊥ r s u (h post r s u hs)⟩

end AddSub

namespace Let

@[expose] def VC [MonadStateOf Nat (PredTrans NatPred EStack⟨⟩)] (n : Nat) : Prop :=
  ∀ (post : NatPred) s, post s →
    (loop n : PredTrans NatPred EStack⟨⟩ Unit).apply (fun _ => post) ⊥ s

-- Attach soundness only after proving the calculated VC; the result is the original goal.
#time_setup "LetBinding.predtrans.bridge"
theorem sound [MonadStateOf Nat (PredTrans NatPred EStack⟨⟩)]
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := StateM Nat) (Pred := NatPred)))
    (n : Nat) : VC n → _root_.LetBinding.Goal n := by
  intro h post
  rw [← loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := StateM Nat)) Sound.monad hstate n
    (fun _ => post) ⊥ s (h post s hs)⟩

end Let

namespace Reader

@[expose] def VC [MonadReaderOf Nat (PredTrans ReaderPred EStack⟨⟩)]
    [MonadStateOf Nat (PredTrans ReaderPred EStack⟨⟩)] (n : Nat) : Prop :=
  ∀ (post : ReaderPred) r s, post r s →
    (loop n : PredTrans ReaderPred EStack⟨⟩ Unit).apply (fun _ => post) ⊥ r s

#time_setup "ReaderState.predtrans.bridge"
theorem sound [MonadReaderOf Nat (PredTrans ReaderPred EStack⟨⟩)]
    [MonadStateOf Nat (PredTrans ReaderPred EStack⟨⟩)]
    (hread : MonadReaderOf.Rel (ρ := Nat) (Sound (m := _root_.ReaderState.M) (Pred := ReaderPred)))
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := _root_.ReaderState.M) (Pred := ReaderPred)))
    (n : Nat) : VC n → _root_.ReaderState.Goal n := by
  intro h post
  rw [← loop_eq n]
  exact ⟨fun r s hs => loop.parametric (Sound (m := _root_.ReaderState.M)) Sound.monad
    hread hstate n (fun _ => post) ⊥ r s (h post r s hs)⟩

end Reader

-- `flipp`'s contract is the only operation, so both `PredTrans` tiers use this VC.
namespace Pure

@[expose] def VC (n : Nat) : Prop :=
  ∀ s, s = true →
    (loop n : PredTrans BoolPred EStack⟨⟩ Unit).apply (fun _ s => s = true) ⊥ s

#time_setup "PurePrecond.predtrans.bridge"
theorem sound (n : Nat) : VC n → _root_.PurePrecond.Goal n := by
  intro h
  unfold _root_.PurePrecond.Goal
  rw [← loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := StateM Bool)) Sound.monad flip_sound n
    (fun _ s => s = true) ⊥ s (h s hs)⟩

end Pure

namespace ThrowSet

@[expose] def VC [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)] (n : Nat) : Prop :=
  ∀ s, s ≤ 0 → (loop n : PredTrans NatPred ExceptEPred Unit).apply (fun _ s => s = n) ⊥ s

#time_setup "GetThrowSet.predtrans.bridge"
theorem sound [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)]
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)))
    (hthrow : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)))
    (n : Nat) : VC n → _root_.GetThrowSet.Goal n := by
  intro h
  unfold _root_.GetThrowSet.Goal
  rw [← loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := ExceptState)) Sound.monad hstate hthrow n
    (fun _ s => s = n) ⊥ s (h s hs)⟩

end ThrowSet

namespace Dite

@[expose] def VC [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)] (n : Nat) : Prop :=
  ∀ s, s = 0 → (loop n : PredTrans NatPred ExceptEPred Unit).apply (fun _ s => s = 0) ⊥ s

#time_setup "DiteSplit.predtrans.bridge"
theorem sound [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)]
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)))
    (hthrow : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)))
    (n : Nat) : VC n → _root_.DiteSplit.Goal n := by
  intro h
  unfold _root_.DiteSplit.Goal
  rw [← loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := ExceptState)) Sound.monad hstate hthrow n
    (fun _ s => s = 0) ⊥ s (h s hs)⟩

end Dite

namespace Match

@[expose] def VC [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)] (n : Nat) : Prop :=
  ∀ s, s = n → (loop n : PredTrans NatPred ExceptEPred Unit).apply (fun _ s => s = 0) ⊥ s

#time_setup "MatchSplit.predtrans.bridge"
theorem sound [MonadStateOf Nat (PredTrans NatPred ExceptEPred)]
    [Throw (PredTrans NatPred ExceptEPred)]
    (hstate : MonadStateOf.Rel (σ := Nat) (Sound (m := ExceptState) (Pred := NatPred)))
    (hthrow : Throw.Rel (Sound (m := ExceptState) (Pred := NatPred)))
    (n : Nat) : VC n → _root_.MatchSplit.Goal n := by
  intro h
  unfold _root_.MatchSplit.Goal
  rw [← loop_eq n]
  exact ⟨fun s hs => loop.parametric (Sound (m := ExceptState)) Sound.monad hstate hthrow n
    (fun _ s => s = 0) ⊥ s (h s hs)⟩

end Match

-- Our own monad has no exception postcondition, so its VCs pass none.
namespace CustomMonad

@[expose] def plainVC (n : Nat) : Prop :=
  ∀ (post : NatPred) s, post s → (AddSub.loop n : Spec NatPred Unit) (fun _ => post) s

#time_setup "AddSubCancel.custom-monad.bridge"
theorem plain_sound (n : Nat) : plainVC n → _root_.AddSubCancel.Goal n := by
  intro h post
  rw [← AddSub.plain_loop_eq n]
  exact ⟨fun s hs => AddSub.loop.parametric (Sound (m := StateM Nat)) Sound.monad nat_state_sound
    n (fun _ => post) ⊥ s (h post s hs)⟩

@[expose] def deepVC (n : Nat) : Prop :=
  ∀ (post : DeepPred) r s u, post r s u →
    (AddSub.loop n : Spec DeepPred Unit) (fun _ => post) r s u

#time_setup "AddSubCancelDeep.custom-monad.bridge"
theorem deep_sound (n : Nat) : deepVC n → _root_.AddSubCancelDeep.Goal n := by
  intro h post
  rw [← AddSub.deep_loop_eq n]
  exact ⟨fun r s u hs => AddSub.loop.parametric (Sound (m := _root_.AddSubCancelDeep.M))
    Sound.monad deep_state_sound n (fun _ => post) ⊥ r s u (h post r s u hs)⟩

@[expose] def letVC (n : Nat) : Prop :=
  ∀ (post : NatPred) s, post s → (Let.loop n : Spec NatPred Unit) (fun _ => post) s

#time_setup "LetBinding.custom-monad.bridge"
theorem let_sound (n : Nat) : letVC n → _root_.LetBinding.Goal n := by
  intro h post
  rw [← Let.loop_eq n]
  exact ⟨fun s hs => Let.loop.parametric (Sound (m := StateM Nat)) Sound.monad nat_state_sound n
    (fun _ => post) ⊥ s (h post s hs)⟩

@[expose] def readerVC (n : Nat) : Prop :=
  ∀ (post : ReaderPred) r s, post r s →
    (Reader.loop n : Spec ReaderPred Unit) (fun _ => post) r s

#time_setup "ReaderState.custom-monad.bridge"
theorem reader_sound (n : Nat) : readerVC n → _root_.ReaderState.Goal n := by
  intro h post
  rw [← Reader.loop_eq n]
  exact ⟨fun r s hs => Reader.loop.parametric (Sound (m := _root_.ReaderState.M)) Sound.monad
    reader_read_sound reader_state_sound n (fun _ => post) ⊥ r s (h post r s hs)⟩

@[expose] def pureVC (n : Nat) : Prop :=
  ∀ s, s = true → (Pure.loop n : Spec BoolPred Unit) (fun _ s => s = true) s

#time_setup "PurePrecond.custom-monad.bridge"
theorem pure_sound (n : Nat) : pureVC n → _root_.PurePrecond.Goal n := by
  intro h
  unfold _root_.PurePrecond.Goal
  rw [← Pure.loop_eq n]
  exact ⟨fun s hs => Pure.loop.parametric (Sound (m := StateM Bool)) Sound.monad flip_sound n
    (fun _ s => s = true) ⊥ s (h s hs)⟩

@[expose] def throwSetVC (n : Nat) : Prop :=
  ∀ s, s ≤ 0 → (ThrowSet.loop n : Spec NatPred Unit) (fun _ s => s = n) s

#time_setup "GetThrowSet.custom-monad.bridge"
theorem throw_set_sound (n : Nat) : throwSetVC n → _root_.GetThrowSet.Goal n := by
  intro h
  unfold _root_.GetThrowSet.Goal
  rw [← ThrowSet.loop_eq n]
  exact ⟨fun s hs => ThrowSet.loop.parametric (Sound (m := ExceptState)) Sound.monad
    except_state_sound throw_sound n (fun _ s => s = n) ⊥ s (h s hs)⟩

@[expose] def diteVC (n : Nat) : Prop :=
  ∀ s, s = 0 → (Dite.loop n : Spec NatPred Unit) (fun _ s => s = 0) s

#time_setup "DiteSplit.custom-monad.bridge"
theorem dite_sound (n : Nat) : diteVC n → _root_.DiteSplit.Goal n := by
  intro h
  unfold _root_.DiteSplit.Goal
  rw [← Dite.loop_eq n]
  exact ⟨fun s hs => Dite.loop.parametric (Sound (m := ExceptState)) Sound.monad
    except_state_sound throw_sound n (fun _ s => s = 0) ⊥ s (h s hs)⟩

@[expose] def matchVC (n : Nat) : Prop :=
  ∀ s, s = n → (Match.loop n : Spec NatPred Unit) (fun _ s => s = 0) s

#time_setup "MatchSplit.custom-monad.bridge"
theorem match_sound (n : Nat) : matchVC n → _root_.MatchSplit.Goal n := by
  intro h
  unfold _root_.MatchSplit.Goal
  rw [← Match.loop_eq n]
  exact ⟨fun s hs => Match.loop.parametric (Sound (m := ExceptState)) Sound.monad
    except_state_sound throw_sound n (fun _ s => s = 0) ⊥ s (h s hs)⟩

end CustomMonad

namespace HandWrittenSpecs

@[expose] def plainVC (n : Nat) : Prop := AddSub.plainVC n
#time_setup "AddSubCancel.hand-written-specs.bridge"
theorem plain_sound (n : Nat) : plainVC n → _root_.AddSubCancel.Goal n :=
  AddSub.plain_sound nat_state_sound n

@[expose] def deepVC (n : Nat) : Prop := AddSub.deepVC n
#time_setup "AddSubCancelDeep.hand-written-specs.bridge"
theorem deep_sound (n : Nat) : deepVC n → _root_.AddSubCancelDeep.Goal n :=
  AddSub.deep_sound deep_state_sound n

@[expose] def letVC (n : Nat) : Prop := Let.VC n
#time_setup "LetBinding.hand-written-specs.bridge"
theorem let_sound (n : Nat) : letVC n → _root_.LetBinding.Goal n := Let.sound nat_state_sound n

@[expose] def readerVC (n : Nat) : Prop := Reader.VC n
#time_setup "ReaderState.hand-written-specs.bridge"
theorem reader_sound (n : Nat) : readerVC n → _root_.ReaderState.Goal n :=
  Reader.sound reader_read_sound reader_state_sound n

@[expose] def throwSetVC (n : Nat) : Prop := ThrowSet.VC n
#time_setup "GetThrowSet.hand-written-specs.bridge"
theorem throw_set_sound (n : Nat) : throwSetVC n → _root_.GetThrowSet.Goal n :=
  ThrowSet.sound except_state_sound throw_sound n

@[expose] def diteVC (n : Nat) : Prop := Dite.VC n
#time_setup "DiteSplit.hand-written-specs.bridge"
theorem dite_sound (n : Nat) : diteVC n → _root_.DiteSplit.Goal n :=
  Dite.sound except_state_sound throw_sound n

@[expose] def matchVC (n : Nat) : Prop := Match.VC n
#time_setup "MatchSplit.hand-written-specs.bridge"
theorem match_sound (n : Nat) : matchVC n → _root_.MatchSplit.Goal n :=
  Match.sound except_state_sound throw_sound n

end HandWrittenSpecs

namespace Library

@[expose] def plainVC (n : Nat) : Prop := AddSub.plainVC n
#time_setup "AddSubCancel.library.bridge"
theorem plain_sound (n : Nat) : plainVC n → _root_.AddSubCancel.Goal n :=
  AddSub.plain_sound nat_state_sound n

@[expose] def deepVC (n : Nat) : Prop := AddSub.deepVC n
#time_setup "AddSubCancelDeep.library.bridge"
theorem deep_sound (n : Nat) : deepVC n → _root_.AddSubCancelDeep.Goal n :=
  AddSub.deep_sound deep_state_sound n

@[expose] def letVC (n : Nat) : Prop := Let.VC n
#time_setup "LetBinding.library.bridge"
theorem let_sound (n : Nat) : letVC n → _root_.LetBinding.Goal n := Let.sound nat_state_sound n

@[expose] def readerVC (n : Nat) : Prop := Reader.VC n
#time_setup "ReaderState.library.bridge"
theorem reader_sound (n : Nat) : readerVC n → _root_.ReaderState.Goal n :=
  Reader.sound reader_read_sound reader_state_sound n

@[expose] def throwSetVC (n : Nat) : Prop := ThrowSet.VC n
#time_setup "GetThrowSet.library.bridge"
theorem throw_set_sound (n : Nat) : throwSetVC n → _root_.GetThrowSet.Goal n :=
  ThrowSet.sound except_state_sound throw_sound n

@[expose] def diteVC (n : Nat) : Prop := Dite.VC n
#time_setup "DiteSplit.library.bridge"
theorem dite_sound (n : Nat) : diteVC n → _root_.DiteSplit.Goal n :=
  Dite.sound except_state_sound throw_sound n

@[expose] def matchVC (n : Nat) : Prop := Match.VC n
#time_setup "MatchSplit.library.bridge"
theorem match_sound (n : Nat) : matchVC n → _root_.MatchSplit.Goal n :=
  Match.sound except_state_sound throw_sound n

end Library

#guard_axioms Pure.sound, CustomMonad.plain_sound, CustomMonad.deep_sound, CustomMonad.let_sound,
  CustomMonad.reader_sound, CustomMonad.pure_sound, CustomMonad.throw_set_sound,
  CustomMonad.dite_sound, CustomMonad.match_sound,
  HandWrittenSpecs.plain_sound, HandWrittenSpecs.deep_sound, HandWrittenSpecs.let_sound,
  HandWrittenSpecs.reader_sound, HandWrittenSpecs.throw_set_sound,
  HandWrittenSpecs.dite_sound, HandWrittenSpecs.match_sound,
  Library.plain_sound, Library.deep_sound, Library.let_sound, Library.reader_sound,
  Library.throw_set_sound, Library.dite_sound, Library.match_sound ⊆
  [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
