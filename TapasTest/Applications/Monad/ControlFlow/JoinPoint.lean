import TapasTest.TestingUtils

/-!
Do-notation join points. An `if` or `match` followed by more statements elaborates to
`have __do_jp := fun __r => rest`; a branch without a result calls `__do_jp ()`.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Parametricity.ControlFlow.JoinPoint

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

def tickBy (k : Nat) := infer_effects% do
  let n ← get
  set (n + k)
  pure n
derive_parametric tickBy

/-! ## Minimal reproductions -/

-- A1: `if` without `else`; the continuation is `tick`.
def a1 (b : Bool) := infer_effects% do
  if b then set 1
  tick
derive_parametric a1

-- A2: the continuation is a bind.
def a2 (b : Bool) := infer_effects% do
  if b then set 1
  let n ← get
  pure n
derive_parametric a2

-- A3: the continuation is a capability operation.
def a3 (b : Bool) := infer_effects% do
  if b then set 1
  get
derive_parametric a3

-- A4: the continuation is `pure`.
def a4 (b : Bool) := infer_effects% do
  if b then set 1
  pure 5
derive_parametric a4

-- A5: `match` arms without results; the continuation is `tick`.
def a5 (x : Option Nat) := infer_effects% do
  match x with
  | some k => set k
  | none => pure ()
  tick
derive_parametric a5

-- A6: the continuation is a helper applied to an argument.
def a6 (b : Bool) := infer_effects% do
  if b then set 1
  tickBy 2
derive_parametric a6

/-! ## Variants of `IfTests.i4` -/

-- I4: let-bound condition; the continuation is `tick`.
def i4 := infer_effects% do
  let n ← get
  let k := n + 1
  if k > 3 then set k else pure ()
  tick
derive_parametric i4

-- The elaborated body, showing the join point `__do_jp : PUnit → m Nat` that both
-- branches jump to. This is the shape every case in this file is about.
/--
info: def TapasTest.Parametricity.ControlFlow.JoinPoint.i4.{u_1} : {m : Type → Type u_1} →
  [instMonad : Monad m] → [effect0 : MonadStateOf Nat m] → m Nat :=
fun {m} [Monad m] [MonadStateOf Nat m] => do
  let n ← get
  let k : Nat := n + 1
  have __do_jp : PUnit → m Nat := fun __r => tick
  if k > 3 then do
      let __r ← set k
      __do_jp __r
    else __do_jp ()
-/
#guard_msgs in
set_option pp.letVarTypes true in
#print i4

-- I4a: let-bound condition, no continuation.
def i4a := infer_effects% do
  let n ← get
  let k := n + 1
  if k > 3 then set k else pure ()
derive_parametric i4a

-- I4b: no `let`; the continuation is `tick`.
def i4b := infer_effects% do
  let n ← get
  if n + 1 > 3 then set (n + 1) else pure ()
  tick
derive_parametric i4b

-- I4c: let-bound value and continuation `tick`, but no `if`.
def i4c := infer_effects% do
  let n ← get
  let k := n + 1
  set k
  tick
derive_parametric i4c

-- I4d: condition on a parameter; the continuation is `tick`.
def i4d (b : Bool) := infer_effects% do
  let k := 3
  if b then set k else pure ()
  tick
derive_parametric i4d

-- I4e: the `if` is a bound computation rather than a statement.
def i4e := infer_effects% do
  let n ← get
  let k := n + 1
  let r ← if k > 3 then pure k else tick
  pure r
derive_parametric i4e

/-! ## Composed join points -/

-- Each statement shares the remaining branches and the final helper call.
def sequentialJoins (b1 b2 b3 : Bool) (x y : Option Nat) := infer_effects% do
  let start ← tick
  if b1 then set (start + 1)
  match x with
  | some k => set (start + k)
  | none => pure ()
  if b2 then set (start + 2)
  match y with
  | some k => set (start + k + 1)
  | none => pure ()
  unless b3 do set (start + 3)
  if start > 4 then set (start + 4)
  tickBy (start + 1)
derive_parametric sequentialJoins

-- Inner continuations use branch-local values before reaching the outer continuation.
def nestedJoins (outer left right : Bool) (x : Option Nat) := infer_effects% do
  let base ← tick
  if outer then
    if left then set (base + 1)
    match x with
    | some k =>
      if right then set (base + k)
      let n ← tick
      set (n + k)
    | none =>
      if right then set base
      set (base + 2)
    let n ← tick
    if n > base then set (n + 1)
    set (n + base)
  else
    if right then set (base + 3)
    unless left do set (base + 4)
    set (base + 5)
  if left then set (base + 6)
  tickBy base
derive_parametric nestedJoins

-- Reassigned locals become additional arguments of the shared continuations.
def mutableJoins (b c : Bool) (x : Option Nat) := infer_effects% do
  let mut total ← tick
  let mut steps := 0
  if b then
    if c then
      total := total + 1
      steps := steps + 1
    total := total + steps
  else
    total := total + 2
    steps := steps + 2
  match x with
  | some k =>
    if k > total then
      total := k
      steps := steps + 1
    total := total + steps
  | none =>
    if c then steps := steps + 1
    total := total + steps
  if c then
    total := total + steps
    steps := steps + 1
  set total
  let observed ← tickBy steps
  pure (observed, total, steps)
derive_parametric mutableJoins

-- Early returns skip different amounts of work; other branches resume shared continuations.
def earlyReturnJoins (stop fallback : Bool) (x : Option Nat) := infer_effects% do
  let start ← tick
  if stop then return start
  match x with
  | none =>
    if fallback then return start + 1
    set (start + 2)
  | some k =>
    if k = 0 then return start
    if fallback then set k
    set (start + k)
  let middle ← tick
  if fallback then set (middle + start)
  match x with
  | some k => set (middle + k)
  | none => pure ()
  if middle > start + 3 then
    if fallback then return middle
    set (middle + 1)
  if middle == 0 then return 0
  tickBy (start + middle)
derive_parametric earlyReturnJoins

#guard_parametric a1, a2, a3, a4, a5, a6, i4, i4a, i4b, i4c, i4d, i4e
#guard_parametric sequentialJoins, nestedJoins, mutableJoins, earlyReturnJoins

-- The current proofs use about 3,000–5,100 objects; leave room for ordinary changes.
#guard_num_objs sequentialJoins.parametric, nestedJoins.parametric,
  mutableJoins.parametric, earlyReturnJoins.parametric < 8000

end TapasTest.Parametricity.ControlFlow.JoinPoint
