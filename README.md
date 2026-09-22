# Tapas: tagless final and parametricity

Tapas is a Lean library for writing programs against abstract interfaces and
proving relationships between their interpretations. It infers the required type
class parameters, generates logical relations, and derives parametricity theorems
checked by Lean's kernel. These theorems lift compatibility proofs for individual
operations to guarantees about whole programs.

## A small example

Write an arithmetic expression once, then choose whether to evaluate or print it:

```lean
import Tapas

universe u v

class Arith (A : Type u) where
  lit : Nat → A
  add : A → A → A

def expression := infer_final% (A : Type u) =>
  Arith.add (A := A) (Arith.lit 1) (Arith.lit 2)

instance : Arith Nat := ⟨id, Nat.add⟩
instance : Arith String := ⟨toString, fun x y => s!"({x} + {y})"⟩

#eval expression (A := Nat)     -- 3
#eval expression (A := String)  -- "(1 + 2)"

derive_interface_rel Arith (repr := A)
derive_parametric expression (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Arith A] [Arith B] (h : Arith.Rel R) :
    R (expression (A := A)) (expression (A := B)) :=
  expression.parametric R h
```

`infer_final%` infers the interface `{A : Type u} → [Arith A] → A`.
`Arith.Rel R` asks that the two interpretations of `lit` and `add` preserve `R`;
`expression.parametric` proves that the complete expression then preserves it too.
Choosing a relation and proving compatibility of the interpretations remain the
user's obligations.

## Usage examples

[TapasTest](TapasTest/) contains usage examples alongside regression tests. These
examples include the programs, interpretations, and proofs needed to demonstrate
each application:

- **Multiple interpretations:** [Carrier.lean](TapasTest/EndToEnd/Carrier.lean)
  evaluates, prints, and reifies arithmetic expressions, proving that evaluating
  the syntax agrees with direct execution.
- **Typed languages:** [Indexed.lean](TapasTest/EndToEnd/Indexed.lean) uses a
  representation indexed by object-language types, including functions and
  application, and proves agreement between two interpretations.
- **Data refinement:** [Store](TapasTest/Applications/Monad/Store/README.md)
  implements a logical store with an update journal, preserving results and
  logical state even through nested sandboxes.
- **Ghost state:** [Ghost](TapasTest/Applications/Monad/Ghost/README.md) uses ghost
  state in loop invariants and execution, proves semantic erasure, and checks
  that specialization removes ghost updates from IR.
- **Reification and verification:** [Freer](TapasTest/Applications/Monad/Freer/README.md)
  proves roundtrips and effect lowering; its
  [extraction example](TapasTest/Applications/Monad/Freer/Extraction.lean) transfers
  proofs from operation specifications to concrete executions.
- **Monad stack selection:** [StackSuggestion](TapasTest/Applications/Monad/StackSuggestion/Programs.lean)
  uses inferred capabilities to suggest transformer stacks and shows how their
  order affects state and exceptions.

## Further reading

- [Interface inference](Tapas/TaglessFinal/Inference.lean): `infer_final%` for
  expressions and `infer_final` for declarations.
- [Logical relations](Tapas/LogicalRelation/README.md): relations for interfaces
  and program types, their proof obligations, and supported representation shapes.
- [Monadic programs](Tapas/Applications/Monad/README.md): `infer_effects%`,
  `derive_effect_rel`, recursion, and `infer_effects_partial%` for least-fixpoint loops.

## Build and tests

Use the Lean version pinned in [lean-toolchain](lean-toolchain):

```sh
lake build
lake test
```

The test suite also checks rejected derivations and the axiom dependencies of
proofs, including generated certificates.
