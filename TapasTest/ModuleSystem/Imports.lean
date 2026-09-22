module

import TapasTest.ModuleSystem.Definitions
meta import TapasTest.ModuleSystem.Definitions -- shake: keep (required by #guard/#eval)

open TapasTest.ModuleSystem.Definitions

#guard_msgs (drop info) in
#check_failure hidden
#guard_msgs (drop info) in
#check_failure hiddenProgram
#guard_msgs (drop info) in
#check_failure hiddenProof

-- Public names and certificates survive import, but unexposed bodies do not unfold.
example : sealed (m := Id) = 4 := sealed_eq
#guard_msgs (drop info) in
#check_failure (rfl : sealed (m := Id) = 4)
#guard_msgs (drop info) in
#check_failure (rfl : sectionSealed (m := Id) = 11)

example : unfolded (m := Id) = 9 := rfl
example : sectionIdentity (A := Nat) 7 = 7 := rfl

def caller := infer_effects% sealed
derive_parametric caller

example {m n : Type → Type} [Monad m] [Monad n]
    (R : Tapas.LogicalRelation.ComputationRelation m n) (h : Monad.Rel R) :
    R (caller (m := m)) (caller (m := n)) := caller.parametric R h

#guard (caller (m := Id)).run == 4
