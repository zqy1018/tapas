module

import Tapas

/-!
`infer_final` on declarations: which parameters a signature ends up binding, and where that
cannot be decided.

The recursion shapes themselves, and the parametricity theorems derived from them, are covered by
`TapasTest.Parametricity.ControlFlow.Recursion`, whose definitions are written with this same
command. What is left here is what only inference decides.
-/

namespace TapasTest.TaglessFinal.RecursiveInference

universe u

class Arithmetic (A : Type u) where
  literal : Nat → A
  add : A → A → A

class Scale (A : Type u) where
  double : A → A

instance : Arithmetic Nat where
  literal n := n
  add := Nat.add

instance : Scale Nat := ⟨fun n => n + n⟩

/- A `where` helper is lifted to a declaration of its own and binds only the interfaces it uses,
while the definition it was split out of binds those of the whole block. Here `go` never scales,
so `Scale` reaches `scaleTotal` alone. -/
infer_final (A : Type u)
def scaleTotal (xs : List Nat) : A := Scale.double (go xs (Arithmetic.literal 0))
where
  go : List Nat → A → A
    | [], acc => acc
    | x :: rest, acc => go rest (Arithmetic.add acc (Arithmetic.literal x))

example : ({A : Type u} → [Scale A] → [Arithmetic A] → List Nat → A) := @scaleTotal

example : ({A : Type u} → [Arithmetic A] → List Nat → A → A) := @scaleTotal.go

#guard scaleTotal (A := Nat) [2, 3, 5] == 20

/- The functions of a `mutual` block settle one shared set. `alternate` never mentions `Scale`,
but binds it all the same, which is what lets its call to `emphasize` supply it. -/
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

#guard alternate (A := Nat) 5 == 4

/-! ## Several selected parameters -/

class Convert (A : Type) (B : Type) where
  conv : A → B

instance : Convert Nat String := ⟨toString⟩

-- One constraint mentioning both selected parameters is abstracted once.
infer_final (A : Type) (B : Type)
def convAll : List A → List B
  | [] => []
  | x :: rest => Convert.conv x :: convAll rest

example : ({A B : Type} → [Convert A B] → List A → List B) := @convAll

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

class Indexed (n : Nat) (A : Type u) where
  peek : A

-- A requirement depending on a definition's own parameter is generalized over it.
infer_final (A : Type u)
def scanIndex : Nat → A
  | 0 => Arithmetic.literal 0
  | k + 1 => Arithmetic.add (Indexed.peek (n := k)) (scanIndex k)

example : ({A : Type u} → [Arithmetic A] → [(n : Nat) → Indexed n A] → Nat → A) := @scanIndex

/- A `where` helper sees its parent's parameters, but the parent's signature is built outside
them, so the same requirement cannot be generalized there. -/
/--
error: interface inference: the inferred requirement
  Indexed k A
mentions `k`, which is local to a body of this block and so cannot appear in a signature. Write the requirement out as a binder instead.
-/
#guard_msgs in
infer_final (A : Type u)
def atIndex (k : Nat) : Nat → A
  | 0 => go 3
  | j + 1 => atIndex k j
where
  go : Nat → A
    | 0 => Indexed.peek (n := k)
    | i + 1 => go i

end TapasTest.TaglessFinal.RecursiveInference
