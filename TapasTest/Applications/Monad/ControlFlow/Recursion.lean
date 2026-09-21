import TapasTest.TestingUtils

/-!
Recursive monadic programs: the signature `infer_effects` gives each recursion shape, and what
`derive_parametric` can then translate.

Structural, well-founded, `mutual` and `partial_fixpoint` recursion are handled directly.
Everything else recurses through *some other* declaration, and then the question is only whether
that declaration has a translation: a `where` or `let rec` helper is derived along with the
definition it was split out of, a library loop ships one, and a user's own helper is derived by
naming it. The cases that cannot be repaired that way are the ones where no translation exists to
derive -- an opaque `partial def`, a recursor, and `Lean.Loop.forIn`.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.Recursion

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

/-! ## Recursion the generator handles by itself -/

-- Structural recursion. The capability is used only under the recursive branch.
infer_effects
def countDown : Nat → m Nat
  | 0 => get
  | k + 1 => do set k; countDown k

example : ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat) := @countDown

example : Id.run (StateT.run (countDown (m := StateT Nat Id) 3) 7) = (0, 0) := rfl

derive_parametric countDown

-- Join points in a recursive body.
infer_effects
def evenSet : Nat → m Nat
  | 0 => tick
  | k + 1 => do
    if k % 2 == 0 then set k
    let r ← evenSet k
    pure (r + 1)

derive_parametric evenSet

-- Well-founded recursion with an explicit measure and a discharging tactic.
infer_effects
def halve (n : Nat) : m Nat := do
  if n ≤ 1 then
    pure n
  else
    set n
    halve (n / 2)
termination_by n
decreasing_by omega

example : ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat) := @halve

#guard Id.run (StateT.run (halve (m := StateT Nat Id) 8) 0) == (1, 2)

derive_parametric halve

-- The recursive argument is a monadic result, so its induction hypothesis carries a premise.
infer_effects
def chase (n : Nat) : m Nat := do
  let x ← get
  if _h : x < n then chase x else pure n
termination_by n

derive_parametric chase

/- Two capabilities, contributed by different functions of the block, become one shared set of
parameters. A recursive occurrence can then always supply what the function it calls needs.
One invocation derives both functions. -/
infer_effects
mutual
def evenSteps : Nat → m Nat
  | 0 => get
  | k + 1 => do set k; oddSteps k
def oddSteps : Nat → m Nat
  | 0 => do let label ← readThe String; pure label.length
  | k + 1 => evenSteps k
end

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → [MonadReaderOf String m] →
      Nat → m Nat) := @evenSteps

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → [MonadReaderOf String m] →
      Nat → m Nat) := @oddSteps

#guard Id.run (StateT.run (ReaderT.run
  (evenSteps (m := ReaderT String (StateT Nat Id)) 4) "abc") 9) == (1, 1)

derive_parametric evenSteps

-- The first invocation already added the other member's theorem.
/-- error: parametricity: declaration already exists: TapasTest.Applications.Monad.ControlFlow.Recursion.oddSteps.parametric -/
#guard_msgs in
derive_parametric oddSteps

/- A `where` helper is lifted with the capabilities it uses in its own signature, and is derived
along with the definition it was split out of. -/
infer_effects
def total (xs : List Nat) : m Nat := go xs 0
where
  go : List Nat → Nat → m Nat
    | [], acc => pure acc
    | x :: rest, acc => do set x; go rest (acc + x)

example :
    ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → List Nat → Nat → m Nat) := @total.go

example : Id.run (StateT.run (total (m := StateT Nat Id) [2, 3, 5]) 0) = (10, 5) := rfl

derive_parametric total

-- A `let rec` inside the body is lifted the same way.
infer_effects
def countUp (n : Nat) : m Nat := do
  let rec go : Nat → m Nat
    | 0 => pure 0
    | k + 1 => do set k; let rest ← go k; pure (rest + 1)
  go n

example : ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat) := @countUp.go

example : Id.run (StateT.run (countUp (m := StateT Nat Id) 3) 9) = (3, 0) := rfl

/- A `partial_fixpoint` is built from the order parameters after the bodies are elaborated, so
`infer_effects_partial` keeps them even though no body mentions them. Its translation carries an
`AdmissibleRel` premise, which the check at the end of this file records. -/
infer_effects_partial
def pfix (n : Nat) : m Nat := do
  set n
  if n == 0 then pure 0 else pfix (n - 1)
partial_fixpoint

example :
    ({m : Type → Type} → [Monad m] → [∀ α, Lean.Order.CCPO (m α)] → [Lean.Order.MonoBind m] →
      [MonadStateOf Nat m] → Nat → m Nat) := @pfix

derive_parametric pfix

/- A block that does not loop gets the signature `infer_effects` would have given it. -/
infer_effects_partial
def noLoop : Nat → m Nat
  | 0 => get
  | k + 1 => do set k; noLoop k

example : ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat) := @noLoop

/-! ## Loops whose translation the library ships

`Tapas.Applications.Monad.StdLoops` ships the translations used below. It derives list and array
loops as ordinary recursive definitions. The legacy range rule is written by hand because
`Std.Legacy.Range.forIn'` recurses through a private helper that no `derive_parametric` invocation
can name. The rules are registered under that module's own names, so `List.forIn'.parametric`
stays free -- `TapasTest/Applications/Monad/Program.lean` claims it, to show that `as` left it available.
-/

-- `for` over a list, which goes through `List.forIn'`.
def forList (xs : List Nat) := infer_effects% do
  for x in xs do
    set x
  get
derive_parametric forList

-- Early return from a list loop.
def loopReturn (xs : List Nat) := infer_effects% do
  for x in xs do
    let n ← get
    if n > x then return n
    set (n + x)
  pure 0
derive_parametric loopReturn

-- `break` leaves the loop with the accumulator the body last assigned.
def loopBreak (xs : List Nat) := infer_effects% do
  let mut acc := 0
  for x in xs do
    if x == 0 then break
    acc := acc + x
    let _ ← tick
  pure acc
derive_parametric loopBreak

-- `for` over an array.
def arrayLoop (xs : Array Nat) := infer_effects% do
  for x in xs do
    set x
  get
derive_parametric arrayLoop

-- `for` over a range. The legacy spelling needs the hand-written rule; the current one iterates
-- through a list and is carried by the list rule, as the check below records.
def forRange (k : Nat) := infer_effects% do
  for i in [0:k] do
    set i
  get
derive_parametric forRange

def forPRange (k : Nat) := infer_effects% do
  for i in [0...k] do
    set i
  getThe Nat
derive_parametric forPRange

def forPRangeIncl (k : Nat) := infer_effects% do
  for i in [0...=k] do
    set i
  getThe Nat
derive_parametric forPRangeIncl

open Tapas.Parametricity.StdLoops in
#guard_uses forRange.parametric ⊇ [rangeForIn'Rel]

open Tapas.Parametricity.StdLoops in
#guard_uses forPRange.parametric, forPRangeIncl.parametric ⊇ [listForIn'Rel]

-- A monadic traversal is shipped on the same terms as a loop.
def mapMProg (xs : List Nat) := infer_effects% do
  xs.mapM fun x => do set x; tick
derive_parametric mapMProg

def folded (xs : List Nat) := infer_effects% do
  xs.foldlM (fun acc x => do set x; pure (acc + x)) 0
derive_parametric folded

/-! ## What inference decides about a signature -/

/- A section variable the block uses is kept, and one it does not is dropped. Here the capability
itself is what mentions the variable. -/
section
variable (σ : Type) (unused : Bool)

infer_effects
def cycle (init : σ) : Nat → m σ
  | 0 => get
  | k + 1 => do set init; cycle init k

example :
    ((σ : Type) → {m : Type → Type} → [Monad m] → [MonadStateOf σ m] → σ → Nat → m σ) := @cycle

end

class Indexed (n : Nat) (m : Type → Type) where
  peek : m Nat

-- A capability depending on a definition's own parameter is generalized over it.
infer_effects
def scanIndex : Nat → m Nat
  | 0 => pure 0
  | k + 1 => do
      let here ← Indexed.peek (n := k)
      let rest ← scanIndex k
      pure (here + rest)

example :
    ({m : Type → Type} → [Monad m] → [(n : Nat) → Indexed n m] → Nat → m Nat) := @scanIndex

/- A `where` helper sees its parent's parameters, but the parent's signature is built outside
them, so the same capability cannot be generalized there. -/
/--
error: interface inference: the inferred requirement
  Indexed k m
mentions `k`, which is local to a body of this block and so cannot appear in a signature. Write the requirement out as a binder instead.
-/
#guard_msgs in
infer_effects
def atIndex (k : Nat) : Nat → m Nat
  | 0 => go 3
  | j + 1 => atIndex k j
where
  go : Nat → m Nat
    | 0 => Indexed.peek (n := k)
    | i + 1 => go i

/-- error: interface inference applies to a definition or a `mutual` block of definitions -/
#guard_msgs in
infer_effects
#check 1

/-! ## Recursion with no translation to derive -/

/- A `partial def` is an opaque constant, so there is no body to walk. Use `partial_fixpoint`
when the program is to be derived. -/
infer_effects
partial def spin (n : Nat) : m Nat := do
  set n
  if n == 0 then pure 0 else spin (n - 1)

example : ({m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat) := @spin

/--
error: parametricity: expected a definition with a body: TapasTest.Applications.Monad.ControlFlow.Recursion.spin
-/
#guard_msgs in
derive_parametric spin

/- `Array.mapM` recurses through a private helper, like the range loop, but unlike it has no
unconditional way around: it rewrites to `List.mapM` or to `Array.foldlM`, and both rewrites
assume `LawfulMonad` of *both* interpretations, which a translation applied to an arbitrary pair
of related monads cannot supply. A program that needs it relates it under its own lawfulness
premises. -/
def arrayMapMProg (xs : Array Nat) := infer_effects% do
  xs.mapM fun x => do set x; tick

/--
error: parametricity: no applicable translation for Array.mapM; use `derive_parametric Array.mapM` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric arrayMapMProg

-- And following that instruction runs into the private helper, which is where it stops.
/--
error: parametricity: no applicable translation for _private.Init.Data.Array.Basic.0.Array.mapM.map; use `derive_parametric _private.Init.Data.Array.Basic.0.Array.mapM.map` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric Array.mapM (repr := m)

/- A `while` loop expands to `ForIn` over `Lean.Loop`, and `Lean.Loop.forIn` is `whileM`, whose
value is a classically chosen fixed point rather than a recursion the walk can follow, so no
translation is provable for an arbitrary relation. `infer_effects_partial%` selects a
least-fixpoint loop instead; see `TapasTest.Applications.Monad.Loop`. -/
def whileLoop := infer_effects% do
  while (← get) > 0 do
    modify (· - 1)
  get

/--
error: parametricity: no applicable translation for Lean.Loop.forIn; use `derive_parametric Lean.Loop.forIn` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric whileLoop

-- An explicit recursor in a term. `Nat.rec` is not a definition either.
infer_effects
def viaRec (k : Nat) : m Nat :=
  Nat.rec get (fun j ih => set j *> ih) k

/--
error: parametricity: no applicable translation for Nat.rec; use `derive_parametric Nat.rec` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric viaRec

/- A failure in one function of a `mutual` block rolls back the theorems of the whole block. -/
def unregistered := infer_effects% pure (1 : Nat)

infer_effects
mutual
def good : Nat → m Nat
  | 0 => pure 0
  | k + 1 => bad k
def bad : Nat → m Nat
  | 0 => unregistered
  | k + 1 => good k
end

/--
error: parametricity: no applicable translation for TapasTest.Applications.Monad.ControlFlow.Recursion.unregistered; use `derive_parametric TapasTest.Applications.Monad.ControlFlow.Recursion.unregistered` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric good

/-! ## What the derivations left behind -/

#guard_parametric tick, countDown, evenSet, halve, chase, evenSteps, oddSteps, total,
  total.go, pfix, forList, loopReturn, loopBreak, arrayLoop, forRange, forPRange,
  forPRangeIncl, mapMProg, folded

#guard_no_parametric spin, whileLoop, viaRec, arrayMapMProg, good, bad

-- A recursive theorem uses functional induction rather than recursion on itself.
#guard_uses countDown.parametric ⊇ [countDown.induct]
#guard_uses halve.parametric ⊇ [halve.induct]
#guard_uses evenSteps.parametric ⊇ [evenSteps.induct]
#guard_uses oddSteps.parametric ⊇ [oddSteps.induct]

-- The admissibility premise is what distinguishes a `partial_fixpoint` translation.
#guard_uses type pfix.parametric ⊇ [AdmissibleRel]

#guard_axioms countDown.parametric, halve.parametric, chase.parametric, total.parametric,
  total.go.parametric, loopBreak.parametric ⊆ [propext, Quot.sound]

/- The mutual block and the fixpoint need the same axioms as the hand-written definitions they
replace. -/
#guard_axioms evenSteps.parametric, oddSteps.parametric, pfix.parametric ⊆
  [propext, Quot.sound, Classical.choice]

end TapasTest.Applications.Monad.ControlFlow.Recursion
