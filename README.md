# Tagless Final Style and Parametricity

Tapas separates three operations: abstracting missing instance arguments,
generating logical relations, and proving that a definition preserves a relation.

## Instance inference

```lean
import Tapas

universe u v

class Arith (A : Type u) where
  lit : Nat → A
  add : A → A → A

def atoms := inferFinal% (A : Type u) =>
  [Arith.lit (A := A) 1, Arith.add (Arith.lit 2) (Arith.lit 3)]

example : {A : Type u} → [Arith A] → List A := @atoms

derive_interface_rel Arith (repr := A)
derive_parametric atoms (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [left : Arith A] [right : Arith B] (h : Arith.Rel R left right) :
    Tapas.LogicalRelation.ListRel R (atoms (A := A)) (atoms (A := B)) :=
  atoms.parametric R h
```

`inferFinal% (A : ...) (B : ...) => body` introduces rigid Lean parameters and
abstracts unresolved class dictionaries mentioning any selected parameter.
Parameter kinds, dependencies, and the body's result type are unrestricted by
this mechanism. Concrete instances are used normally; duplicate and derivable
requirements are minimized. Unrelated missing instances and non-class holes
remain errors.

The entry point does not assume that the result is `A` or `repr ?i`. Use explicit
operation parameters, as above, or annotate the body when Lean needs a type.
`TaglessFinal.inferInterfaceBody` exposes the shared mechanism with a selector
and an optional expected type; it has no dependency on logical relations.

## Logical relations and proofs

`derive_interface_rel C (repr := A)` generates a class `C.Rel` with a preservation
condition for every flattened operation. `derive_type_rel T (repr := A)` generates
a relation between values of a final type binding `A`. Ordinary parameters remain
shared; the selected parameter uses the **shared-index interpretation**:

- `A : Type u` gives `A → B → Prop`.
- `repr : (n : Nat) → Fin n → Type u` gives
  `∀ {n} {i : Fin n}, repr n i → repr' n i → Prop`.
- Arbitrary-length telescopes use the same construction. Index domains can
  depend on earlier shared indices or contain higher-kinded parameters.

`LogicalRelation.Aliases` contains optional names such as `ComputationRelation`
and `IndexedRelation`; `Basic` contains only the relation registries. The generator
`sharedIndexRelation source target (some name)` always constructs the relation
type first, then uses an application of `name` only if its arguments can be
inferred and the application is definitionally equal to that type. Otherwise it
keeps the generated type. Omitting the name leaves the type expanded. The legacy
monadic entry points request `ComputationRelation` for readability.

This is a semantic choice, separate from instance inference. It is not full
heterogeneous parametricity: the two interpretations share indices. Relating
different indices, associated type fields, and dependent results over related
values require further translation rules. They are currently rejected.

`derive_parametric p (repr := A)` translates the elaborated definition into a
kernel-checked `p.parametric` theorem. Its result may be a selected value, an
independent value, a function, or a registered container. Local hypotheses,
interface preservation fields, registered helper theorems, and constructors of
registered inductive relators provide proof rules. Unknown helpers still need
`derive_parametric` or `register_parametric`; polymorphism alone is not treated
as a certificate. Generated relations and proof rules survive module import.

The public derivation commands currently select one parameter at a time. The
lower-level relation/proof context holds paired parameters and their relations;
it does not classify representations by arity. `@[effect_relator]` and the legacy
registry names remain for compatibility.

## Monad applications

`Tapas.Applications.Monad` retains `inferEffects%`, its monadic expected type,
and `inferPartialEffects%`. Ordinary loops and opt-in least-fixpoint loops retain
their distinct semantics. Recursive proofs use functional induction; partial
fixpoints retain their order assumptions and admissibility premises.

`derive_effect_rel` and `derive_type_rel` without explicit selection retain
the legacy monadic selection behavior. Without `(repr := A)`, `derive_parametric`
selects a parameter from the result head, as in the original monadic programs;
container and independent results require explicit selection.

## Validation

Run `lake build` and `lake test`. `TapasTest` covers inference signatures and
failures, carrier and indexed languages, dependent and higher-kinded shared
indices, container results and imported proofs, interpreter correctness,
universes, rollback, recursion, and partial-loop boundaries. Tests audit the
axioms of generated certificates. Loom and Freer examples are not included.
