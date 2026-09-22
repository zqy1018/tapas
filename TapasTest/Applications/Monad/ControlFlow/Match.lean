module

import TapasTest.TestingUtils

/-!
`match` programs for `derive_parametric`.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.Match

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

-- M1: match on a value obtained from a bind.
def m1 := infer_effects% do
  let o : Option Nat ← get
  match o with
  | none => pure 0
  | some k => do set k; pure k
derive_parametric m1

-- M2: Nat literal patterns with an overlapping wildcard.
def m2 (n : Nat) := infer_effects% do
  match n with
  | 0 => pure 0
  | 1 => set 1; pure 1
  | _ => get
derive_parametric m2

-- M3: `if let`.
def m3 (o : Option Nat) := infer_effects% do
  if let some k := o then set k; get else get
derive_parametric m3

-- M4: `match h : ...` (equation hypothesis).
def m4 (o : Option Nat) := infer_effects% do
  match h : o with
  | some k => set k; pure (Option.get o (by simp [h]))
  | none => get
derive_parametric m4

-- M5: discriminant is a let-bound variable.
def m5 := infer_effects% do
  let n ← get
  let k := n % 3
  match k with
  | 0 => pure 0
  | _ => pure 1
derive_parametric m5

-- M6: discriminant is a compound expression.
def m6 (n : Nat) := infer_effects% do
  match n + 1 with
  | 0 => pure 0
  | k + 1 => set k; get
derive_parametric m6

-- M7: pattern-matching bind on a pair.
def pairProg := infer_effects% do
  let a ← get
  pure (a, a + 1)
derive_parametric pairProg

def m7 := infer_effects% do
  let (a, b) ← pairProg
  set (a + b)
  pure b
derive_parametric m7

-- M8: match selecting a monadic function, then applied (over-applied matcher).
def m8 (b : Bool) := infer_effects% do
  (match b with
   | true => fun k => set k *> get
   | false => fun _ => get) 3
derive_parametric m8

-- M9: nested matches on bound values.
def m9 (x : Option (Option Nat)) := infer_effects% do
  match x with
  | none => pure 0
  | some y =>
    let z : Nat ← get
    match y, z with
    | none, _ => pure z
    | some k, 0 => set k; pure k
    | some _, _ + 1 => get
derive_parametric m9

-- M10: match followed by a continuation that is a bind.
def m10 (x : Option Nat) := infer_effects% do
  match x with
  | some k => set k
  | none => pure ()
  let n ← get
  pure (n + 1)
derive_parametric m10

-- M11: String literal patterns.
def m11 (s : String) := infer_effects% do
  match s with
  | "inc" => set 1; get
  | "get" => get
  | _ => pure 0
derive_parametric m11

-- M12: `casesOn` produced by a tactic block. The signature is written out rather than
-- inferred, because an operation inside a tactic block cannot contribute an effect: the
-- tactic block reports an unresolved `MonadStateOf Nat m` before `infer_effects%` sees it.
def m12 {m : Type → Type v} [Monad m] [MonadStateOf Nat m] (o : Option Nat) : m Nat := by
  cases o with
  | none => exact pure 0
  | some k => exact (set k *> get)
derive_parametric m12

-- M13: a dependent match is rejected, because the computation-valued parameter `xs` is
-- itself a discriminant, so the two interpretations do not match on the same value.
def m13 {m : Type → Type v} [Monad m] (n : Nat) (xs : Fin n → m Nat) : m Nat :=
  match n, xs with
  | 0, _ => pure 0
  | _ + 1, xs => xs 0

/--
error: parametricity: match discriminant depends on the representation or differs between interpretations
-/
#guard_msgs in
derive_parametric m13

-- M14: match on a structure value obtained from a reader.
structure Cfg where
  flag : Bool
  size : Nat

def m14 := infer_effects% do
  -- `read` currently leaves an untranslated `readThe` wrapper during derivation.
  let c ← readThe Cfg
  match c with
  | ⟨true, s⟩ => set s; pure s
  | ⟨false, _⟩ => get
derive_parametric m14

-- M15: List patterns.
def m15 (xs : List Nat) := infer_effects% do
  match xs with
  | [] => pure 0
  | [a] => set a; pure a
  | a :: b :: _ => set (a + b); get
derive_parametric m15

/-! ## Composed matches -/

-- Three discriminants with overlapping list, option, and literal patterns.
def overlappingMatches (xs : List Nat) (choice : Option Nat) (tag : Nat) := infer_effects% do
  let base ← tick
  match xs, choice, tag with
  | [], none, _ => pure base
  | [], some k, 0 => set (base + k); tick
  | [], some k, _ + 1 => pure (base + k)
  | [a], _, 0 => set (base + a); tick
  | [a], some k, _ => set (a + k); tick
  | a :: b :: _, some k, 0 => set (a + b + k); tick
  | a :: _, none, _ => set (base + a); tick
  | _, some k, _ => set (base + k); tick
derive_parametric overlappingMatches

-- The inner branch uses both equation hypotheses to recover a value from the original input.
def nestedEquations (x : Option (Option Nat)) (fallback : Nat) := infer_effects% do
  let base ← tick
  match hx : x with
  | none => pure (base + fallback)
  | some y =>
    let outer := x.get (by simp [hx])
    match hy : y with
    | none => set (base + fallback); tick
    | some k =>
      let actual := outer.get (by simp [outer, hx, hy])
      let total := base + k + actual
      match actual % 3 with
      | 0 => set total; pure actual
      | 1 => set (total + 1); tick
      | _ => set (total + 2); tick
derive_parametric nestedEquations

-- Each selected function takes two arguments and captures values from before the match.
def appliedMatcher (x : Option Nat) (xs : List Nat) (offset : Nat) := infer_effects% do
  let base ← tick
  let result ←
    (match x, xs with
     | none, [] => fun a b => pure (base + a + b)
     | none, k :: _ => fun a b => do
       set (base + k + a)
       pure (b + k)
     | some k, [] => fun a b => do
       set (k + a)
       let n ← tick
       pure (n + b)
     | some k, j :: _ => fun a b => do
       let n ← tick
       set (n + k + j + a)
       pure (b + base)) offset (base + 1)
  pure (result + base)
derive_parametric appliedMatcher

-- Unlike `m13`, the dependent function is shared: its result does not mention the monad.
def sharedDependentMatch (n : Nat) (xs : Fin n → Nat) := infer_effects% do
  match n, xs with
  | 0, _ => pure 0
  | k + 1, xs =>
    set (xs 0 + k)
    tick
derive_parametric sharedDependentMatch

#guard_parametric m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m14, m15
#guard_parametric overlappingMatches, nestedEquations, appliedMatcher, sharedDependentMatch

-- The current proofs use about 800–5,700 objects; leave room for ordinary changes.
#guard_num_objs overlappingMatches.parametric, nestedEquations.parametric,
  appliedMatcher.parametric, sharedDependentMatch.parametric < 8000

-- The rejected dependent match left nothing behind.
#guard_no_parametric m13

end TapasTest.Applications.Monad.ControlFlow.Match
