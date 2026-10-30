module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Models
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.AddSubCancel
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.Baseline
import TapasTest.TestingUtils

public section

/-!
Upstream's hand-written Sym baseline, which only the add/sub cases have. Its solver is extracted
once and parameterized by its rules: the plain rules are upstream's `Exec` rules; the deep rules
are ours, taking the deep model's WP as successful execution.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Lean.Order Std.WP

-- The shallow goal and rules are exactly the upstream Exec formulation.
@[expose] def PlainSymGoal (n : Nat) : Prop :=
  ∀ s post, post () s → _root_.Exec s (_root_.AddSubCancel.loop n) post

theorem plain_sym_sound (n : Nat) : PlainSymGoal n → _root_.AddSubCancel.Goal n := by
  intro h post
  exact ⟨fun s hs => h s (fun _ => post) hs⟩

/-- Successful execution with all assertions of the deep stack retained. -/
@[expose] def DeepExec (r : String) (s : Nat) (u : Unit)
    (x : _root_.AddSubCancelDeep.M α) (post : α → DeepPred) : Prop :=
  wp x post ⊥ r s u

-- Adapt the three Exec rules to the deep model. No cancellation fact is used here.
theorem DeepExec.bind (x : _root_.AddSubCancelDeep.M α)
    (f : α → _root_.AddSubCancelDeep.M β) (post : β → DeepPred) :
    DeepExec r s u x (fun a r' s' u' => DeepExec r' s' u' (f a) post) →
      DeepExec r s u (x >>= f) post :=
  WPMonad.bind_le_wp_bind x f post ⊥ r s u

theorem DeepExec.get :
    post s r s u → DeepExec r s u (getThe (m := _root_.AddSubCancelDeep.M) Nat) post :=
  fun h => h

theorem DeepExec.set (s' : Nat) :
    post () r s' u → DeepExec r s u (set (m := _root_.AddSubCancelDeep.M) s') post :=
  fun h => h

theorem deep_unit_map (x : _root_.AddSubCancelDeep.M Unit) :
    (fun _ : Unit => PUnit.unit) <$> x = x := by simp

@[expose] def DeepSymGoal (n : Nat) : Prop :=
  ∀ r s u post, post () r s u → DeepExec r s u (_root_.AddSubCancelDeep.loop n) post

theorem deep_sym_sound (n : Nat) : DeepSymGoal n → _root_.AddSubCancelDeep.Goal n := by
  intro h post
  exact ⟨fun r s u hs => h r s u (fun _ => post) hs⟩

meta section

open Lean Meta Elab Sym

/- Extract the upstream hard-coded solver once, parameterizing only its rules and binder count.
The original, complete implementation remains in Upstream/Baseline.lean for comparison. -/
private partial def solveWith (bindName getName setName unitMapName : Name) (introCount : Nat)
    (goal : MVarId) : SymM Unit := do
  let bindRule ← mkBackwardRuleFromDecl bindName
  let getRule ← mkBackwardRuleFromDecl getName
  let setRule ← mkBackwardRuleFromDecl setName
  let preMethods ← _root_.mkSimpMethods #[
    ``Nat.add_zero, ``Nat.sub_zero, ``bind_pure_comp, ``map_bind, ``id_map', unitMapName, ``bind_assoc]
  let postMethods ← mkMethods #[``Nat.add_sub_cancel]
  let goal ← preprocessMVar goal
  let .goal _ goal ← Sym.introN goal introCount | failure
  let .goal goal ← Sym.simpGoal goal preMethods | failure
  let rec advance (original : MVarId) : SymM MVarId := do
    let .goals [goal] ← bindRule.apply original | return original
    let .goals [goal] ← getRule.apply goal | return original
    let .goals [goal] ← bindRule.apply goal | return original
    let .goals [goal] ← setRule.apply goal | return original
    advance goal
  let goal ← advance goal
  let .goals [goal] ← bindRule.apply goal | failure
  let .goals [goal] ← getRule.apply goal | failure
  let .goals [goal] ← setRule.apply goal | failure
  let .goal goal ← Sym.simpGoal goal postMethods | failure
  goal.assumption

/-- Run the upstream solver algorithm with the shallow Exec rules. -/
def solvePlain (goal : MVarId) : MetaM (List MVarId) := SymM.run do
  solveWith ``_root_.Exec.bind ``_root_.Exec.get ``_root_.Exec.set ``_root_.unit_map 3 goal
  return []

/-- Run the same solver algorithm with the deep Exec rules. -/
def solveDeep (goal : MVarId) : MetaM (List MVarId) := SymM.run do
  solveWith ``DeepExec.bind ``DeepExec.get ``DeepExec.set ``deep_unit_map 5 goal
  return []

end

-- Upstream's original, unchanged solver proves the goal that Verify.lean proves by the extraction.
set_option maxRecDepth 10000 in
theorem original_sym_three : _root_.AddSubCancel.Goal 3 := by
  apply plain_sym_sound
  simp only [PlainSymGoal, _root_.AddSubCancel.loop, _root_.AddSubCancel.step]
  run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => Lean.Meta.Sym.SymM.run do
    _root_.solve goal
    return []

#guard_axioms original_sym_three ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
