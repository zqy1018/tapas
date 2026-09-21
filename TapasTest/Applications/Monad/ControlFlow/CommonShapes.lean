import TapasTest.TestingUtils

/-!
Common do-notation shapes: consecutive `if`s without `else`, `unless`, a `match` arm that
produces no result, and a long run of `if`/`else`. Each one is derived, and the check at
the end also bounds the size of the generated proof, so a blow-up in the proof term shows
up as a failure rather than as a slow build.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.CommonShapes

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

-- C1: two consecutive `if`s without `else`.
def c1 (b1 b2 : Bool) := infer_effects% do
  if b1 then set 1
  if b2 then set 2
  let n ← get
  pure n
derive_parametric c1

-- C2: `unless`.
def c2 (b : Bool) := infer_effects% do
  unless b do set 1
  let n ← get
  pure n
derive_parametric c2

-- C3: `match` with a `pure ()` arm, then more statements.
def c3 (o : Option Nat) := infer_effects% do
  match o with
  | some k => set k
  | none => pure ()
  let n ← get
  pure n
derive_parametric c3

-- C4: six `if`/`else` statements in sequence.
def c4 (b1 b2 b3 b4 b5 b6 : Bool) := infer_effects% do
  if b1 then set 1 else set 0
  if b2 then set 2 else set 0
  if b3 then set 3 else set 0
  if b4 then set 4 else set 0
  if b5 then set 5 else set 0
  if b6 then set 6 else set 0
  let n ← get
  pure n
derive_parametric c4

#guard_parametric c1, c2, c3, c4

-- The bound is loose on purpose: it catches a proof term that stops sharing, not ordinary drift.
#guard_num_objs c1.parametric, c2.parametric, c3.parametric, c4.parametric < 8000

end TapasTest.Applications.Monad.ControlFlow.CommonShapes
