import TapasTest.TestingUtils

/-!
Recursive programs over ordinary and indexed representations. Their signatures state
the representation and interface parameters before the recursive bodies are elaborated.
-/

open Tapas.LogicalRelation

namespace TapasTest.Parametricity.ControlFlow.Recursion

class Arithmetic (A : Type u) where
  literal : Nat → A
  add : A → A → A

derive_interface_rel Arithmetic (repr := A)

inductive Formula where
  | literal : Nat → Formula
  | variable : Nat → Formula
  | add : Formula → Formula → Formula

-- Tree recursion makes two recursive calls and reads a related environment.
def evaluate {A : Type u} [Arithmetic A] (env : Nat → A) : Formula → A
  | .literal n => Arithmetic.literal n
  | .variable i => env i
  | .add lhs rhs => Arithmetic.add (evaluate env lhs) (evaluate env rhs)
derive_parametric evaluate (repr := A)

-- The recursive helper changes its representation-valued accumulator.
def sumList {A : Type u} [Arithmetic A] (xs : List Nat) : A :=
  loop xs (Arithmetic.literal 0)
where
  loop (rest : List Nat) (acc : A) : A :=
    match rest with
    | [] => acc
    | x :: rest => loop rest (Arithmetic.add acc (Arithmetic.literal x))

/--
error: parametricity: no applicable translation for TapasTest.Parametricity.ControlFlow.Recursion.sumList.loop; use `derive_parametric TapasTest.Parametricity.ControlFlow.Recursion.sumList.loop` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric sumList (repr := A)

derive_parametric sumList.loop (repr := A)
derive_parametric sumList (repr := A)

-- Finishing a row decreases `rows` but resets `cols`, requiring a lexicographic measure.
def countCells {A : Type u} [Arithmetic A] (width rows cols : Nat) : A :=
  match rows, cols with
  | 0, _ => Arithmetic.literal 0
  | row + 1, 0 => countCells width row width
  | row + 1, col + 1 => Arithmetic.add (Arithmetic.literal 1) (countCells width (row + 1) col)
termination_by (rows, cols)
derive_parametric countCells (repr := A)

-- Mutual calls reorder both fixed functions and the varying value and counter.
mutual
def visitLeft {A : Type u} (f g : A → A) (n : Nat) (x : A) : A :=
  match n with
  | 0 => x
  | n + 1 => visitRight g f (f x) n
def visitRight {A : Type u} (g f : A → A) (x : A) (n : Nat) : A :=
  match n with
  | 0 => x
  | n + 1 => visitLeft f g n (g x)
end
derive_parametric visitLeft (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    (f g : A → A) (f' g' : B → B)
    (hf : ∀ x y, R x y → R (f x) (f' y)) (hg : ∀ x y, R x y → R (g x) (g' y))
    (n : Nat) (x : A) (y : B) (hxy : R x y) :
    R (visitLeft f g n x) (visitLeft f' g' n y) :=
  visitLeft.parametric f g n x R f' hf g' hg y hxy

-- The same arithmetic program may build a list of contributions or add them directly.
instance : Arithmetic (List Nat) where
  literal n := [n]
  add := List.append

instance : Arithmetic Nat where
  literal n := n
  add := Nat.add

abbrev sumCompatible : Arithmetic.Rel (fun xs n => xs.sum = n)
    (inferInstance : Arithmetic (List Nat)) (inferInstance : Arithmetic Nat) where
  literal _ := rfl
  add xs x hx ys y hy := by
    change (xs ++ ys).sum = x + y
    simp only [List.sum_append, hx, hy]

-- Use the generated tree-recursion theorem with different representations and environments.
example (env : Nat → List Nat) (expr : Formula) :
    (evaluate (A := List Nat) env expr).sum =
      evaluate (A := Nat) (fun i => (env i).sum) expr :=
  evaluate.parametric env expr (fun xs n => xs.sum = n) sumCompatible
    (fun i => (env i).sum) (fun _ => rfl)

example (xs : List Nat) : (sumList (A := List Nat) xs).sum = sumList (A := Nat) xs :=
  sumList.parametric xs (fun xs n => List.sum xs = n) sumCompatible

#guard evaluate (A := Nat) (fun i => i + 10)
  (.add (.variable 0) (.add (.literal 2) (.variable 1))) == 23
#guard sumList (A := List Nat) [2, 3, 5] == [0, 2, 3, 5]
#guard sumList (A := Nat) [2, 3, 5] == 10
#guard countCells (A := Nat) 3 2 3 == 6
#guard visitLeft (· + 1) (· * 2) 3 3 == 9
#guard visitRight (· * 2) (· + 1) 3 3 == 14

namespace Indexed

class Sequence (repr : Nat → Type u) where
  empty : repr 0
  prepend {n : Nat} : Nat → repr n → repr (n + 1)

derive_interface_rel Sequence (repr := repr)

-- Each recursive call returns a value at a smaller index.
def tabulate {repr : Nat → Type u} [Sequence repr] (f : Nat → Nat) : (n : Nat) → repr n
  | 0 => Sequence.empty
  | n + 1 => Sequence.prepend (f n) (tabulate f n)
derive_parametric tabulate (repr := repr)

-- A shared inductive input determines the result index.
def fromList {repr : Nat → Type u} [Sequence repr] (xs : List Nat) : repr xs.length :=
  match xs with
  | [] => Sequence.empty
  | x :: rest => Sequence.prepend x (fromList rest)
derive_parametric fromList (repr := repr)

example {repr : Nat → Type u} {repr' : Nat → Type v} (R : IndexedRelation repr repr')
    [left : Sequence repr] [right : Sequence repr'] (h : Sequence.Rel R left right)
    (xs : List Nat) : R (fromList (repr := repr) xs) (fromList (repr := repr') xs) :=
  fromList.parametric xs R h

instance : Sequence (fun _ => List Nat) where
  empty := []
  prepend := List.cons

#guard tabulate (repr := fun _ => List Nat) (· + 10) 3 == [12, 11, 10]
#guard fromList (repr := fun _ => List Nat) [2, 4, 6] == [2, 4, 6]

end Indexed

#guard_parametric evaluate, sumList.loop, sumList, countCells, visitLeft, visitRight,
  Indexed.tabulate, Indexed.fromList

#guard_axioms evaluate.parametric, sumList.loop.parametric, sumList.parametric,
  countCells.parametric, visitLeft.parametric, visitRight.parametric,
  Indexed.tabulate.parametric, Indexed.fromList.parametric ⊆ [propext, Quot.sound]

end TapasTest.Parametricity.ControlFlow.Recursion
