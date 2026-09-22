module

import Tapas
import all Init.Data.Repr -- check the String interpreter by kernel reduction

universe u

namespace TapasTest.TaglessFinal.Inference

class Literal (A : Type) where
  lit : Nat → A

class Arithmetic (A : Type) extends Literal A where
  add : A → A → A

/- A constraint mentioning the selected parameter becomes a parameter of the
result. The stronger interface supplies its parent, so the two `Literal A`
requirements merge into the single `Arithmetic A`. -/
def combined := infer_final% (A : Type) =>
  Arithmetic.add (A := A) (Literal.lit 1) (Literal.lit 2)

example : {A : Type} → [Arithmetic A] → A := @combined

instance : Arithmetic Nat where
  lit n := n
  add := Nat.add

instance : Arithmetic String where
  lit n := toString n
  add x y := x ++ " + " ++ y

/- The selected parameter is what two interpretations of one program differ in:
`Nat` evaluates it and `String` prints it. -/
example : combined (A := Nat) = 3 := rfl

example : combined (A := String) = "1 + 2" := rfl

class Wrap (A : Type) where
  wrap : A → A

instance : Wrap A := ⟨id⟩

/- An instance available in the environment is used as usual rather than
abstracted, so only `Literal A` remains. -/
def usingAvailable := infer_final% (A : Type) => Wrap.wrap (Literal.lit (A := A) 1)

example : {A : Type} → [Literal A] → A := @usingAvailable

class Config where
  number : Nat

/- A missing instance that mentions no selected parameter is an ordinary error
instead: it is neither abstracted nor silently dropped. -/
/--
error: don't know how to synthesize implicit argument `self`
  @Config.number ?m.3
context:
A : Type
⊢ Config

Note: `Config` does not mention `A`, so it is not abstracted and must be synthesized from the environment.
-/
#guard_msgs in
def missingUnrelated := infer_final% (A : Type) => Literal.lit (A := A) Config.number

/- An ordinary unsolved hole stays an error too. -/
/--
error: don't know how to synthesize placeholder
context:
A : Type
⊢ Nat
-/
#guard_msgs in
def hole := infer_final% (A : Type) => Literal.lit (A := A) (_ : Nat)

class Choose (σ : Type) (A : Type) where
  choose : A

/- An argument the body would otherwise leave open is fixed by writing it. -/
def chosen := infer_final% (A : Type) => Choose.choose (A := A) (σ := Nat)

example : {A : Type} → [Choose Nat A] → A := @chosen

/- Leaving it open blocks the requirement it belongs to: a parameter carrying a
metavariable is one no caller could supply. -/
/--
error: don't know how to synthesize placeholder for argument `σ`
context:
A : Type
⊢ Type

Note: the inferred requirement
  Choose ?m.2 A
still has an undetermined argument, so it cannot become an instance parameter: no caller could supply one.
-/
#guard_msgs in
def hiddenTypeHole := infer_final% (A : Type) => Choose.choose (A := A) (σ := _)

class At (repr : Bool → Type) where
  value {i} : repr i

/- An index the body never fixes fails for a different reason: the requirement
`At repr` is complete, and it is the result type `repr ?i` that is not. -/
/--
error: don't know how to synthesize implicit argument `i`
  @At.value repr ?interface0 ?m.3
context:
repr : Bool → Type
⊢ Bool
-/
#guard_msgs in
def unknownIndex := infer_final% (repr : Bool → Type) => At.value (repr := repr)

/- Writing the index makes the result type concrete. -/
def indexed := infer_final% (repr : Bool → Type) => At.value (repr := repr) (i := true)

example : {repr : Bool → Type} → [At repr] → repr true := @indexed

instance : Choose Nat Nat where
  choose := 7

/- Requirements inferred for an opaque leaf definition propagate through a call
and merge with the ones the caller raises itself: `Arithmetic A` is required by
both `combined` and the `add` here, and appears once. -/
def callsLeaves := infer_final% (A : Type) =>
  Arithmetic.add (A := A) (combined (A := A)) (chosen (A := A))

example : {A : Type} → [Arithmetic A] → [Choose Nat A] → A := @callsLeaves

example : callsLeaves (A := Nat) = 10 := rfl

/- Selecting a parameter prescribes neither the result type nor that the body use
the parameter at all. -/
def concrete := infer_final% (A : Type) => (1 : Nat)

example : {_ : Type} → Nat := @concrete

/- Multiple indices are ordinary Lean parameters, not a separate inference case. -/
def twoIndices := infer_final% (repr : Nat → Nat → Type) => 0

example : {_ : Nat → Nat → Type} → Nat := @twoIndices

class Convert (A B : Type) where
  convert : A → B

/- Every selected parameter is rigid, and a requirement may mention either or
both. -/
def converted := infer_final% (A : Type) (B : Type) =>
  Convert.convert (B := B) (Literal.lit (A := A) 1)

example : {A B : Type} → [Convert A B] → [Literal A] → B := @converted

class ValueAt (n : Nat) where
  value : Fin (n + 1)

/- A selected parameter may be a value rather than a type. -/
def valueAt := infer_final% (n : Nat) => ValueAt.value (n := n)

example : {n : Nat} → [ValueAt n] → Fin (n + 1) := @valueAt

/- It may also live in an arbitrary sort. -/
def identityAt := infer_final% (A : Sort u) => (fun x : A => x)

example : {A : Sort u} → A → A := @identityAt

class SelectedValue {I : Type} (repr : I → Type) (i : I) where
  value : repr i

/- Later parameters may have kinds mentioning earlier ones. -/
def dependent := infer_final% (I : Type) (repr : I → Type) (i : I) =>
  SelectedValue.value (repr := repr) (i := i)

example : {I : Type} → {repr : I → Type} → {i : I} →
    [SelectedValue repr i] → repr i := @dependent

/- An explicit result annotation directs ordinary Lean elaboration without a
representation-specific expected-type rule. -/
def annotated := infer_final% (A : Type) => (Literal.lit 2 : A)

example : {A : Type} → [Literal A] → A := @annotated

end TapasTest.TaglessFinal.Inference
