module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Conditions
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Harness
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.SymBaseline
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.WPEquations

public meta section

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

-- A tier's VC and bridge, calculated in our own monad or in Lean's `PredTrans`.
private def inSpec (vc sound : Lean.Name) : Harness.Normalization :=
  ⟨``CustomMonad.Spec, vc, sound⟩
private def inPredTrans (vc sound : Lean.Name) : Harness.Normalization :=
  ⟨``Lean.Order.PredTrans, vc, sound⟩

-- The `wp` routes' equations for each monad, after the rules turning a triple into implications.
-- The deep stack has none written, and MatchSplit's `match` on the state has no equation.
private def wpOrder : List Lean.Name :=
  [``Std.WP.Triple.iff, ``WPEquations.pi_rel_eq, ``WPEquations.prop_rel_eq]
private def wpState : List Lean.Name := wpOrder ++
  [``WPEquations.StateM.wp_bind, ``WPEquations.StateM.wp_get, ``WPEquations.StateM.wp_set,
   ``WPEquations.StateM.wp_StateT_set, ``WPEquations.StateM.wp_pure, ``WPEquations.StateM.wp_modify]
private def wpReaderState : List Lean.Name := wpOrder ++
  [``WPEquations.ReaderState.wp_bind, ``WPEquations.ReaderState.wp_read,
   ``WPEquations.ReaderState.wp_get, ``WPEquations.ReaderState.wp_set,
   ``WPEquations.ReaderState.wp_pure]
private def wpExceptState : List Lean.Name := wpOrder ++
  [``WPEquations.ExceptState.wp_bind, ``WPEquations.ExceptState.wp_get,
   ``WPEquations.ExceptState.wp_set, ``WPEquations.ExceptState.wp_throw,
   ``WPEquations.ExceptState.wp_pure, ``WPEquations.ExceptState.wp_ite,
   ``WPEquations.ExceptState.wp_dite]

-- Only the add/sub cases have upstream's Sym baseline.
def cases : List Harness.Case := [
  { label := "AddSubCancel", goal := ``_root_.AddSubCancel.Goal,
    specs := [``_root_.AddSubCancel.spec_get_StateT, ``_root_.AddSubCancel.spec_set_StateT'],
    programs := [``_root_.AddSubCancel.loop, ``_root_.AddSubCancel.step],
    customMonad := inSpec ``CustomMonad.plainVC ``CustomMonad.plain_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.plainVC ``HandWrittenSpecs.plain_sound,
    library := inPredTrans ``Library.plainVC ``Library.plain_sound,
    symGoal := ``PlainSymGoal, symSound := ``plain_sym_sound, symSolve := solvePlain,
    wpEquations := wpState },
  { label := "AddSubCancelDeep", goal := ``_root_.AddSubCancelDeep.Goal,
    specs := [``_root_.AddSubCancelDeep.Spec.M_getThe_Nat, ``_root_.AddSubCancelDeep.Spec.M_set_Nat],
    programs := [``_root_.AddSubCancelDeep.loop, ``_root_.AddSubCancelDeep.step],
    customMonad := inSpec ``CustomMonad.deepVC ``CustomMonad.deep_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.deepVC ``HandWrittenSpecs.deep_sound,
    library := inPredTrans ``Library.deepVC ``Library.deep_sound,
    symGoal := ``DeepSymGoal, symSound := ``deep_sym_sound, symSolve := solveDeep },
  { label := "LetBinding", goal := ``_root_.LetBinding.Goal,
    specs := [``_root_.LetBinding.spec_get_StateT, ``_root_.LetBinding.spec_set_StateT'],
    programs := [``_root_.LetBinding.loop, ``_root_.LetBinding.step],
    customMonad := inSpec ``CustomMonad.letVC ``CustomMonad.let_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.letVC ``HandWrittenSpecs.let_sound,
    library := inPredTrans ``Library.letVC ``Library.let_sound,
    wpEquations := wpState },
  { label := "ReaderState", goal := ``_root_.ReaderState.Goal,
    specs := [``_root_.ReaderState.spec_read, ``_root_.ReaderState.spec_get, ``_root_.ReaderState.spec_set],
    -- `finish` cannot show `post r s → post r (r + s - r)`, which `grind` alone proves.
    failing := [(.vcgenFinish, .handWrittenSpecs), (.vcgenFinish, .library)],
    programs := [``_root_.ReaderState.loop, ``_root_.ReaderState.step],
    customMonad := inSpec ``CustomMonad.readerVC ``CustomMonad.reader_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.readerVC ``HandWrittenSpecs.reader_sound,
    library := inPredTrans ``Library.readerVC ``Library.reader_sound,
    wpEquations := wpReaderState },
  -- `flipp`'s contract is its only operation, so both `PredTrans` tiers state the same VC.
  { label := "PurePrecond", goal := ``_root_.PurePrecond.Goal,
    contracts := [``_root_.PurePrecond.Spec.flipp_true, ``_root_.PurePrecond.Spec.flipp_false],
    programs := [``_root_.PurePrecond.loop, ``_root_.PurePrecond.step],
    customMonad := inSpec ``CustomMonad.pureVC ``CustomMonad.pure_sound,
    handWrittenSpecs := inPredTrans ``Pure.VC ``Pure.sound,
    library := inPredTrans ``Pure.VC ``Pure.sound,
    wpEquations := wpState, wpUnfold := [``_root_.PurePrecond.flipp] },
  { label := "GetThrowSet", goal := ``_root_.GetThrowSet.Goal,
    specs := [``_root_.GetThrowSet.spec_get, ``_root_.GetThrowSet.spec_set, ``_root_.GetThrowSet.spec_throw],
    -- Upstream's vcgen_get_throw_set_grind, spelled `simp [Nat.add_assoc]` in later Lean.
    finishSimp := [``Nat.add_assoc],
    programs := [``_root_.GetThrowSet.loop, ``_root_.GetThrowSet.step],
    customMonad := inSpec ``CustomMonad.throwSetVC ``CustomMonad.throw_set_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.throwSetVC ``HandWrittenSpecs.throw_set_sound,
    library := inPredTrans ``Library.throwSetVC ``Library.throw_set_sound,
    wpEquations := wpExceptState },
  { label := "DiteSplit", goal := ``_root_.DiteSplit.Goal,
    specs := [``_root_.DiteSplit.spec_get, ``_root_.DiteSplit.spec_set, ``_root_.DiteSplit.spec_throw],
    programs := [``_root_.DiteSplit.loop, ``_root_.DiteSplit.step],
    customMonad := inSpec ``CustomMonad.diteVC ``CustomMonad.dite_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.diteVC ``HandWrittenSpecs.dite_sound,
    library := inPredTrans ``Library.diteVC ``Library.dite_sound,
    wpEquations := wpExceptState },
  { label := "MatchSplit", goal := ``_root_.MatchSplit.Goal,
    specs := [``_root_.MatchSplit.spec_get, ``_root_.MatchSplit.spec_set, ``_root_.MatchSplit.spec_throw],
    programs := [``_root_.MatchSplit.loop, ``_root_.MatchSplit.step],
    customMonad := inSpec ``CustomMonad.matchVC ``CustomMonad.match_sound,
    handWrittenSpecs := inPredTrans ``HandWrittenSpecs.matchVC ``HandWrittenSpecs.match_sound,
    library := inPredTrans ``Library.matchVC ``Library.match_sound }]

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
