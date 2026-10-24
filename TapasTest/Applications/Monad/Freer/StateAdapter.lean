module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Freer.Basic
meta import TapasTest.Applications.Monad.Freer.Basic -- shake: keep (required by #guard/#eval)

/-!
`MonadStateOf σ` and `MonadLiftT (StateOp σ)` present the same state operations.
Their dictionaries convert in both directions, with no monad laws, and the conversions
preserve and reflect their logical relations. A state program then reuses the freer /
tagless-final conversion through these adapters.
-/

namespace TapasTest.Applications.Monad.Freer.StateAdapter

open Tapas.Parametricity Tapas.LogicalRelation TapasTest.Applications.Monad.Freer.Basic

universe u w w'

-- One capability adapter. Keep modifyGet as an independent operation, since
-- MonadStateOf does not require its implementation to be derived from get/set.
inductive StateOp (σ : Type u) : Type u → Type (u + 1) where
  | get : StateOp σ σ
  | set : σ → StateOp σ PUnit
  | modifyGet {α : Type u} : (σ → α × σ) → StateOp σ α

section Adapters

variable {σ : Type u} {m : Type u → Type w}

-- Keep the adapters as definitions: registering both directions as global instances
-- would make instance search follow a cycle between the two capabilities.
/-- Use a request interpreter as a state capability. -/
@[instance_reducible] def stateOfLift (lift : MonadLiftT (StateOp σ) m) : MonadStateOf σ m where
  get := lift.monadLift .get
  set s := lift.monadLift (.set s)
  modifyGet f := lift.monadLift (.modifyGet f)

/-- Interpret state requests using a state capability. -/
@[instance_reducible] def liftOfState (state : MonadStateOf σ m) : MonadLiftT (StateOp σ) m where
  monadLift op := match op with
    | .get => state.get
    | .set s => state.set s
    | .modifyGet f => state.modifyGet f

/-- Converting a state capability to requests and back preserves it. -/
theorem stateOfLift_liftOfState (state : MonadStateOf σ m) :
    stateOfLift (liftOfState state) = state := rfl

/-- Converting a request interpreter to a state capability and back preserves it. -/
theorem liftOfState_stateOfLift (lift : MonadLiftT (StateOp σ) m) :
    liftOfState (stateOfLift lift) = lift := by
  cases lift with
  | mk h =>
    dsimp [liftOfState, stateOfLift]
    congr 1
    funext α op
    cases op <;> rfl

/-- Request interpreters are related exactly when their state capabilities are related. -/
theorem lift_rel_iff_state_rel {n : Type u → Type w'} (R : ComputationRelation m n)
    (left : MonadLiftT (StateOp σ) m) (right : MonadLiftT (StateOp σ) n) :
    MonadLiftT.Rel (left := left) (right := right) R ↔
      MonadStateOf.Rel (left := stateOfLift left) (right := stateOfLift right) R := by
  constructor
  · intro h
    exact MonadStateOf.Rel.mk (left := (_)) (right := (_)) R
      (h.monadLift .get) (fun s => h.monadLift (.set s))
      (fun f => h.monadLift (.modifyGet f))
  · intro h
    exact MonadLiftT.Rel.mk (left := left) (right := right) R fun op => match op with
      | .get => h.get
      | .set s => h.set s
      | .modifyGet f => h.modifyGet f

end Adapters

instance {σ : Type u} : MonadStateOf σ (Freer (StateOp σ)) := stateOfLift inferInstance

-- The original program uses ordinary do notation and inferred capabilities.
def tick := infer_effects% do
  let old ← get
  set (old + 1)
  pure old

def tickFinal : Final.{0, 1, w} (StateOp Nat) Nat := fun {m} _ _ =>
  letI : MonadStateOf Nat m := stateOfLift inferInstance
  tick

def tickFreer : Freer (StateOp Nat) Nat := toFreer @tickFinal

-- The conversion really produces requests, including the data-dependent set.
example : tickFreer = .impure .get (fun old =>
    .impure (.set (old + 1)) (fun _ => .pure old)) := rfl

derive_parametric tick

-- The generated theorem supplies a certificate for arbitrary related handlers,
-- independently of Freer or any particular concrete interpretation.
theorem tickFinal_rel : Final.Rel @tickFinal.{w} @tickFinal.{w'} := by
  intro m n R lm rn hm h k hop
  dsimp only [tickFinal]
  refine tick.parametric (m := m) (m' := n) (effect0 := (_)) (effect0' := (_)) R hm ?_
  exact (lift_rel_iff_state_rel R h k).mp hop

theorem tick_roundtrip {m : Type → Type w} [Monad m] [LawfulMonad m] [MonadStateOf Nat m] :
    @toFinal _ _ tickFreer m _ (liftOfState inferInstance) = tick (m := m) := by
  letI : MonadLiftT (StateOp Nat) m := liftOfState inferInstance
  exact toFinal_toFreer_rel @tickFinal @tickFinal tickFinal_rel

-- The freer computation lives in Type 1; these interpreters return values in Type.
/-- info: (5, 6) -/
#guard_msgs in
#eval tick (m := StateM Nat) 5

/-- info: (5, 6) -/
#guard_msgs in
#eval @toFinal _ _ tickFreer (StateM Nat) _ (liftOfState inferInstance) 5

/-- info: some (5, 6) -/
#guard_msgs in
#eval @toFinal _ _ tickFreer (StateT Nat Option) _ (liftOfState inferInstance) 5

#guard_uses tickFinal_rel ⊇ [tick.parametric, lift_rel_iff_state_rel]
#guard_axioms stateOfLift_liftOfState, lift_rel_iff_state_rel ⊆ []
#guard_axioms liftOfState_stateOfLift ⊆ [Quot.sound]
#guard_axioms toFinal_rel ⊆ []
#guard_axioms toFreer_toFinal ⊆ [Quot.sound]
#guard_axioms toFinal_toFreer_rel, toFinal_toFreer, tick_roundtrip ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.StateAdapter
