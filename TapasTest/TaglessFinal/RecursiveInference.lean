import TapasTest.TestingUtils

/-!
`infer_final` on declarations: the interface parameters are inferred from the bodies instead of
being written out, for the recursion shapes a term elaborator cannot reach.

The programs here are ordinary tagless-final ones, with no monad involved; the selected parameter
is a carrier, an indexed family, or one of a pair.
-/

open Tapas.LogicalRelation

namespace TapasTest.TaglessFinal.RecursiveInference

universe u

class Arithmetic (A : Type u) where
  literal : Nat → A
  add : A → A → A

derive_interface_rel Arithmetic (repr := A)

inductive Formula where
  | literal : Nat → Formula
  | variable : Nat → Formula
  | add : Formula → Formula → Formula

-- Tree recursion: two recursive calls, and a parameter valued in the representation.
infer_final (A : Type u)
def evaluate (env : Nat → A) : Formula → A
  | .literal n => Arithmetic.literal n
  | .variable i => env i
  | .add lhs rhs => Arithmetic.add (evaluate env lhs) (evaluate env rhs)

example : ({A : Type u} → [Arithmetic A] → (Nat → A) → Formula → A) := @evaluate

derive_parametric evaluate

-- A `where` helper with a representation-valued accumulator gets the interface in its own right.
infer_final (A : Type u)
def sumList (xs : List Nat) : A := loop xs (Arithmetic.literal 0)
where
  loop (rest : List Nat) (acc : A) : A :=
    match rest with
    | [] => acc
    | x :: rest => loop rest (Arithmetic.add acc (Arithmetic.literal x))

example : ({A : Type u} → [Arithmetic A] → List Nat → A → A) := @sumList.loop

-- Deriving the helper first is allowed too: it is registered, so the definition does not derive
-- it again.
derive_parametric sumList.loop
derive_parametric sumList

-- Well-founded recursion: finishing a row decreases `rows` but resets `cols`.
infer_final (A : Type u)
def countCells (width rows cols : Nat) : A :=
  match rows, cols with
  | 0, _ => Arithmetic.literal 0
  | row + 1, 0 => countCells width row width
  | row + 1, col + 1 => Arithmetic.add (Arithmetic.literal 1) (countCells width (row + 1) col)
termination_by (rows, cols)

derive_parametric countCells (repr := A)

/- A body that uses no interface gets no interface parameter, `mutual` included: the shared set
is the one the bodies need, not one per selected parameter. -/
infer_final (A : Type u)
mutual
def visitLeft (f g : A → A) (n : Nat) (x : A) : A :=
  match n with
  | 0 => x
  | n + 1 => visitRight g f (f x) n
def visitRight (g f : A → A) (x : A) (n : Nat) : A :=
  match n with
  | 0 => x
  | n + 1 => visitLeft f g n (g x)
end

example : ({A : Type u} → (A → A) → (A → A) → Nat → A → A) := @visitLeft

derive_parametric visitLeft (repr := A)

class Scale (A : Type u) where
  double : A → A

derive_interface_rel Scale (repr := A)

/- Two functions of a block contribute different interfaces, and the block settles one shared
set. `alternate` never mentions `Scale`, but binds it all the same, which is what lets its call
to `emphasize` supply it. -/
infer_final (A : Type u)
mutual
def alternate : Nat → A
  | 0 => Arithmetic.literal 0
  | n + 1 => emphasize n
def emphasize : Nat → A
  | 0 => Arithmetic.literal 1
  | n + 1 => Scale.double (alternate n)
end

example : ({A : Type u} → [Arithmetic A] → [Scale A] → Nat → A) := @alternate

example : ({A : Type u} → [Arithmetic A] → [Scale A] → Nat → A) := @emphasize

derive_parametric alternate (repr := A)

-- Two interpretations of one program, related by the theorem the inferred signature carries.
instance : Arithmetic (List Nat) where
  literal n := [n]
  add := List.append

instance : Arithmetic Nat where
  literal n := n
  add := Nat.add

instance : Scale (List Nat) := ⟨fun xs => xs ++ xs⟩

instance : Scale Nat := ⟨fun n => n + n⟩

abbrev sumCompatible : Arithmetic.Rel (fun xs n => xs.sum = n)
    (inferInstance : Arithmetic (List Nat)) (inferInstance : Arithmetic Nat) where
  literal _ := rfl
  add xs x hx ys y hy := by
    change (xs ++ ys).sum = x + y
    simp only [List.sum_append, hx, hy]

example (env : Nat → List Nat) (expr : Formula) :
    (evaluate (A := List Nat) env expr).sum =
      evaluate (A := Nat) (fun i => (env i).sum) expr :=
  evaluate.parametric (fun xs n => xs.sum = n) sumCompatible env (fun i => (env i).sum)
    (fun _ => rfl) expr

example (xs : List Nat) : (sumList (A := List Nat) xs).sum = sumList (A := Nat) xs :=
  sumList.parametric (fun xs n => List.sum xs = n) sumCompatible xs

#guard evaluate (A := Nat) (fun i => i + 10)
  (.add (.variable 0) (.add (.literal 2) (.variable 1))) == 23
#guard sumList (A := List Nat) [2, 3, 5] == [0, 2, 3, 5]
#guard countCells (A := Nat) 3 2 3 == 6
#guard visitLeft (· + 1) (· * 2) 3 3 == 9
#guard alternate (A := Nat) 5 == 4
#guard alternate (A := List Nat) 5 == [1, 1, 1, 1]

/-! ## An indexed representation -/

class Sequence (repr : Nat → Type u) where
  empty : repr 0
  prepend {n : Nat} : Nat → repr n → repr (n + 1)

derive_interface_rel Sequence (repr := repr)

-- Each recursive call returns a value at a smaller index.
infer_final (repr : Nat → Type u)
def tabulate (f : Nat → Nat) : (n : Nat) → repr n
  | 0 => Sequence.empty
  | n + 1 => Sequence.prepend (f n) (tabulate f n)

example : ({repr : Nat → Type u} → [Sequence repr] → (Nat → Nat) → (n : Nat) → repr n) :=
  @tabulate

derive_parametric tabulate (repr := repr)

instance : Sequence (fun _ => List Nat) where
  empty := []
  prepend := List.cons

#guard tabulate (repr := fun _ => List Nat) (· + 10) 3 == [12, 11, 10]

/-! ## Several selected parameters -/

class Convert (A : Type) (B : Type) where
  conv : A → B

-- One constraint mentioning both selected parameters is abstracted once.
infer_final (A : Type) (B : Type)
def convAll : List A → List B
  | [] => []
  | x :: rest => Convert.conv x :: convAll rest

example : ({A B : Type} → [Convert A B] → List A → List B) := @convAll

instance : Convert Nat String := ⟨toString⟩

#guard convAll (A := Nat) (B := String) [1, 2] == ["1", "2"]

/-! ## Boundaries -/

class Config where
  number : Nat

/- A missing instance that mentions no selected parameter is an ordinary error, in a recursive
body as much as in a term. -/
/--
error: don't know how to synthesize implicit argument `self`
  @Config.number ?m.6
context:
A : Type u
⊢ Config

Note: `Config` does not mention `A`, so it is not abstracted and must be synthesized from the environment.
-/
#guard_msgs in
infer_final (A : Type u)
def repeatLiteral : Nat → A
  | 0 => Arithmetic.literal Config.number
  | count + 1 => repeatLiteral count

#guard_parametric evaluate, sumList, sumList.loop, countCells, visitLeft, visitRight,
  alternate, emphasize, tabulate

#guard_axioms evaluate.parametric, sumList.parametric, sumList.loop.parametric,
  countCells.parametric, visitLeft.parametric, visitRight.parametric,
  alternate.parametric, emphasize.parametric,
  tabulate.parametric ⊆ [propext, Quot.sound]

end TapasTest.TaglessFinal.RecursiveInference
