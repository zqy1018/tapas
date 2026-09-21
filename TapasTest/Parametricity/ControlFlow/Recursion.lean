import TapasTest.TestingUtils

/-!
Recursive programs over ordinary and indexed representations, and the parametricity theorems
derived from them. The representation and interface parameters are inferred from the bodies by
`infer_final`, so each definition states only what it is about.
-/

open Tapas.LogicalRelation

namespace TapasTest.Parametricity.ControlFlow.Recursion

universe u

class Arithmetic (A : Type u) where
  literal : Nat → A
  add : A → A → A

derive_interface_rel Arithmetic (repr := A)

inductive Formula where
  | literal : Nat → Formula
  | variable : Nat → Formula
  | add : Formula → Formula → Formula

-- Tree recursion makes two recursive calls and reads a related environment.
infer_final (A : Type u)
def evaluate (env : Nat → A) : Formula → A
  | .literal n => Arithmetic.literal n
  | .variable i => env i
  | .add lhs rhs => Arithmetic.add (evaluate env lhs) (evaluate env rhs)
derive_parametric evaluate (repr := A)

-- The recursive helper changes its representation-valued accumulator.
infer_final (A : Type u)
def sumList (xs : List Nat) : A :=
  loop xs (Arithmetic.literal 0)
where
  loop (rest : List Nat) (acc : A) : A :=
    match rest with
    | [] => acc
    | x :: rest => loop rest (Arithmetic.add acc (Arithmetic.literal x))

-- The `where` helper is a declaration of its own, and is derived along with the definition it
-- was split out of.
derive_parametric sumList (repr := A)

-- Finishing a row decreases `rows` but resets `cols`, requiring a lexicographic measure.
infer_final (A : Type u)
def countCells (width rows cols : Nat) : A :=
  match rows, cols with
  | 0, _ => Arithmetic.literal 0
  | row + 1, 0 => countCells width row width
  | row + 1, col + 1 => Arithmetic.add (Arithmetic.literal 1) (countCells width (row + 1) col)
termination_by (rows, cols)
derive_parametric countCells (repr := A)

/- Mutual calls reorder both fixed functions and the varying value and counter. Neither body uses
an interface, so neither signature gains one. -/
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
derive_parametric visitLeft (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    (f g : A → A) (f' g' : B → B)
    (hf : ∀ x y, R x y → R (f x) (f' y)) (hg : ∀ x y, R x y → R (g x) (g' y))
    (n : Nat) (x : A) (y : B) (hxy : R x y) :
    R (visitLeft f g n x) (visitLeft f' g' n y) :=
  visitLeft.parametric R f f' hf g g' hg n x y hxy

-- The same arithmetic program may build a list of contributions or add them directly.
instance : Arithmetic (List Nat) where
  literal n := [n]
  add := List.append

instance : Arithmetic Nat where
  literal n := n
  add := Nat.add

abbrev sumCompatible : Arithmetic.Rel (fun (xs : List Nat) (n : Nat) => xs.sum = n) where
  literal _ := rfl
  add xs x hx ys y hy := by
    change (xs ++ ys).sum = x + y
    simp only [List.sum_append, hx, hy]

-- Use the generated tree-recursion theorem with different representations and environments.
example (env : Nat → List Nat) (expr : Formula) :
    (evaluate (A := List Nat) env expr).sum =
      evaluate (A := Nat) (fun i => (env i).sum) expr :=
  evaluate.parametric (fun xs n => xs.sum = n) sumCompatible env
    (fun i => (env i).sum) (fun _ => rfl) expr

example (xs : List Nat) : (sumList (A := List Nat) xs).sum = sumList (A := Nat) xs :=
  sumList.parametric (fun xs n => List.sum xs = n) sumCompatible xs

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
infer_final (repr : Nat → Type u)
def tabulate (f : Nat → Nat) : (n : Nat) → repr n
  | 0 => Sequence.empty
  | n + 1 => Sequence.prepend (f n) (tabulate f n)
derive_parametric tabulate (repr := repr)

-- A shared inductive input determines the result index.
infer_final (repr : Nat → Type u)
def fromList (xs : List Nat) : repr xs.length :=
  match xs with
  | [] => Sequence.empty
  | x :: rest => Sequence.prepend x (fromList rest)
derive_parametric fromList (repr := repr)

example {repr : Nat → Type u} {repr' : Nat → Type v} (R : IndexedRelation repr repr')
    [Sequence repr] [Sequence repr'] (h : Sequence.Rel R)
    (xs : List Nat) : R (fromList (repr := repr) xs) (fromList (repr := repr') xs) :=
  fromList.parametric R h xs

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
