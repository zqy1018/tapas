import TapasTest.TestingUtils

/-!
`if`/`dite` programs for `derive_parametric`.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.If

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

-- I1: condition on a value obtained from a bind.
def i1 := infer_effects% do
  let n ← get
  if n > 0 then set (n - 1) else set 10
  pure n
derive_parametric i1

-- I2: `if` without `else` followed by more statements (join point).
def i2 (b : Bool) := infer_effects% do
  if b then set 1
  let n ← get
  pure (n + 1)
derive_parametric i2

-- I3: nested `if`.
def i3 (b c : Bool) := infer_effects% do
  if b then
    if c then tick else pure 1
  else
    pure 2
derive_parametric i3

-- I4: condition on a let-bound value, followed by `tick`.
def i4 := infer_effects% do
  let n ← get
  let k := n + 1
  if k > 3 then set k else pure ()
  tick
derive_parametric i4

-- I5: early return.
def i5 := infer_effects% do
  let n ← get
  if n == 0 then return 0
  set (n * 2)
  tick
derive_parametric i5

-- I6: `if` selecting a monadic function, then applied (over-applied `ite`).
def i6 (b : Bool) := infer_effects% do
  (if b then (fun k => set k *> tick) else (fun _ => tick)) 3
derive_parametric i6

-- I7: `if` selecting a monadic function through a local `let`.
def i7 (b : Bool) := infer_effects% do
  let f := if b then (fun k => set k *> tick) else (fun _ => tick)
  f 3
derive_parametric i7

-- I8: `if` inside a higher-order operation (a `tryCatch` body).
def i8 (b : Bool) := infer_effects% do
  try
    if b then throw "e" else pure 1
  catch e : String =>
    pure e.length
derive_parametric i8

-- I9: `if` whose condition itself contains an `if`.
def i9 (b c : Bool) := infer_effects% do
  if (if b then c else !c) then tick else pure 0
derive_parametric i9

-- I10: `if` over a `let mut` variable.
def i10 := infer_effects% do
  let mut x ← get
  if x > 5 then x := x - 5
  set x
  pure x
derive_parametric i10

-- I11: conditions on monadic results; branch results are bound and used later.
def i11 := infer_effects% do
  let a ← tick
  let b ← if a % 2 == 0 then tick else pure a
  let c ← if b > a then pure (b - a) else tick
  pure (a + b + c)
derive_parametric i11

-- I12: `let` inside a branch.
def i12 (b : Bool) := infer_effects% do
  if b then
    let k := 3
    set k
    tick
  else
    tick
derive_parametric i12

#guard_parametric i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12

end TapasTest.Applications.Monad.ControlFlow.If
