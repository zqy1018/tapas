module

import TapasTest.TestingUtils

open Tapas.LogicalRelation Tapas.Parametricity Lean.Order

namespace TapasTest.Applications.Monad.Parameters

/-!
Where a generated theorem puts its parameters, and which ones the induction principle keeps.

Every definition below writes its signature out instead of inferring it with `infer_effects`,
because the position and order of the binders is the subject: a monad parameter that follows an
index the recursion varies, a fixed parameter the induction principle must drop next to one it
must keep, and `mutual` functions that disagree about the order.
-/

-- A varying computation argument is related to its copy inside the motive.
def rep {m : Type → Type u} [Monad m] (x : m Nat) : Nat → m Nat
  | 0 => x
  | k + 1 => rep (x >>= fun a => pure (a + 1)) k

derive_parametric rep

example {m : Type → Type u} {n : Type → Type v} [Monad m] [Monad n]
    (R : ComputationRelation m n) (h : Monad.Rel R)
    (x : m Nat) (y : n Nat) (hxy : R x y) (k : Nat) :
    R (rep x k) (rep y k) := rep.parametric R h x y hxy k

-- The fixed monad parameters follow a varying index. The computation argument's
-- type depends on that shared index, and both vary during well-founded recursion.
def repWF (k : Nat) {m : Type → Type u} [Monad m] (x : m (Fin (k + 1))) : m Nat :=
  if k = 0 then x >>= fun a => pure a.val
  else repWF (k - 1) (x >>= fun _ => pure ⟨0, Nat.zero_lt_succ _⟩)
termination_by k

derive_parametric repWF

example {m : Type → Type u} {n : Type → Type v} [Monad m] [Monad n]
    (R : ComputationRelation m n) (h : Monad.Rel R) (k : Nat)
    (x : m (Fin (k + 1))) (y : n (Fin (k + 1))) (hxy : R x y) :
    R (repWF k x) (repWF k y) := repWF.parametric k R h x y hxy

-- The induction principle drops `unused` but keeps `bound`, although both have type `Nat`.
def repUntil (unused bound : Nat) {m : Type → Type u} [Monad m] (x : m Nat) : Nat → m Nat
  | 0 => x
  | k + 1 =>
    if k < bound then repUntil unused bound (x >>= fun a => pure (a + 1)) k else x

derive_parametric repUntil

example {m : Type → Type u} {n : Type → Type v} [Monad m] [Monad n]
    (R : ComputationRelation m n) (h : Monad.Rel R)
    (unused bound k : Nat) (x : m Nat) (y : n Nat) (hxy : R x y) :
    R (repUntil unused bound x k) (repUntil unused bound y k) :=
  repUntil.parametric unused bound R h x y hxy k

-- Mutual functions can put their fixed and varying parameters in different orders.
mutual
def repLeft (unused bound : Nat) {m : Type → Type u} [Monad m] (x : m Nat) : Nat → m Nat
  | 0 => x
  | k + 1 =>
    if k < bound then repRight bound unused k (x >>= fun a => pure (a + 1)) else x
def repRight (bound unused : Nat) {m : Type → Type u} [Monad m] (k : Nat) (x : m Nat) : m Nat :=
  match k with
  | 0 => x
  | k + 1 => repLeft unused bound (x >>= fun a => pure (a + 1)) k
end

derive_parametric repRight

example {m : Type → Type u} {n : Type → Type v} [Monad m] [Monad n]
    (R : ComputationRelation m n) (h : Monad.Rel R)
    (unused bound k : Nat) (x : m Nat) (y : n Nat) (hxy : R x y) :
    R (repRight bound unused k x) (repRight bound unused k y) :=
  repRight.parametric bound unused R h k x y hxy

#guard rep (m := Option) (some 2) 3 == some 5
#guard repWF 3 (some ⟨1, by decide⟩) == some 0
#guard repUntil 99 4 (some 2) 3 == some 5
#guard repLeft 99 4 (some 2) 3 == some 5
#guard repRight 4 99 3 (some 2) == some 5

-- One invocation derives every function of a mutual block, whatever order its parameters are in.
#guard_parametric rep, repWF, repUntil, repLeft, repRight

#guard_axioms rep.parametric ⊆ []

-- Well-founded recursion and functional induction add no axiom beyond the ones Lean's own
-- constructions use.
#guard_axioms repWF.parametric, repUntil.parametric, repLeft.parametric,
  repRight.parametric ⊆ [propext, Quot.sound, Classical.choice]

end TapasTest.Applications.Monad.Parameters
