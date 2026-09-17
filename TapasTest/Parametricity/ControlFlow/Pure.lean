import TapasTest.TestingUtils

/-!
Control flow in ordinary polymorphic functions. Branches inspect shared inputs;
values of the selected type and functions over them are related between interpretations.
-/

namespace TapasTest.Parametricity.ControlFlow.Pure

-- The branches consume the proof supplied by a dependent `if`.
def withProof {A : Type u} (n : Nat) (yes : n = 0 → A) (no : n ≠ 0 → A) : A :=
  if h : n = 0 then yes h else no h
derive_parametric withProof (repr := A)

-- An `if` returns a function, which is then applied.
def chooseFunction {A : Type u} (b : Bool) (f g : A → A) (x : A) : A :=
  (if b then f else g) x
derive_parametric chooseFunction (repr := A)

-- A shared local function is called from both branches.
def localFunction {A : Type u} (b : Bool) (f : A → A) (x y : A) : A :=
  let twice := fun z => f (f z)
  if b then twice x else twice y
derive_parametric localFunction (repr := A)

-- The discriminant is a local `let`, not a parameter.
def letDiscriminant {A : Type u} (n : Nat) (x y : A) : A :=
  let k := n % 3
  match k with
  | 0 => x
  | _ => y
derive_parametric letDiscriminant (repr := A)

-- An equation from pattern matching justifies reading the shared value.
def matchWithProof {A : Type u} (o : Option Nat) (f : Nat → A) (fallback : A) : A :=
  match h : o with
  | none => fallback
  | some _ => f (o.get (by simp [h]))
derive_parametric matchWithProof (repr := A)

-- Structural recursion repeatedly applies related functions.
def iterate {A : Type u} (step : A → A) (seed : A) : Nat → A
  | 0 => seed
  | n + 1 => step (iterate step seed n)
derive_parametric iterate (repr := A)

-- Well-founded recursion changes the related value passed to the next call.
def halve {A : Type u} (step : A → A) (seed : A) (n : Nat) : A :=
  if h : n ≤ 1 then seed else halve step (step seed) (n / 2)
termination_by n
decreasing_by omega
derive_parametric halve (repr := A)

-- One derivation handles both functions of a mutual block.
mutual
def alternateLeft {A : Type u} (f g : A → A) (x : A) : Nat → A
  | 0 => x
  | n + 1 => f (alternateRight f g x n)
def alternateRight {A : Type u} (f g : A → A) (x : A) : Nat → A
  | 0 => x
  | n + 1 => g (alternateLeft f g x n)
end
derive_parametric alternateLeft (repr := A)

-- The generated theorem relates different types and different functions.
example {A : Type u} {B : Type v} (R : A → B → Prop)
    (f : A → A) (g : B → B) (hfg : ∀ x y, R x y → R (f x) (g y))
    (x : A) (y : B) (hxy : R x y) (n : Nat) :
    R (iterate f x n) (iterate g y n) :=
  iterate.parametric f x n R g hfg y hxy

#guard chooseFunction false (· + 1) (· * 2) 3 == 6
#guard localFunction true (· + 1) 2 9 == 4
#guard matchWithProof (some 3) (· + 1) 0 == 4
#guard iterate (· + 3) 2 4 == 14
#guard halve (· + 1) 0 8 == 3
#guard alternateLeft (· + 1) (· * 2) 3 2 == 7

#guard_parametric withProof, chooseFunction, localFunction, letDiscriminant,
  matchWithProof, iterate, halve, alternateLeft, alternateRight

end TapasTest.Parametricity.ControlFlow.Pure
