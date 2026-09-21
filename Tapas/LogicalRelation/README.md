# Logical Relation

Logical relations between two interpretations of the same interface or program.

A *representation* is the *parameter* (following the terminology in [TaglessFinal/Inference.lean](../TaglessFinal/Inference.lean); thus a representation must correspond to a binder) deciding how the object language's expressions
are represented, and the one allowed to differ between two interpretations; see
[TaglessFinal/Inference.lean](../TaglessFinal/Inference.lean) for how one is chosen.
The *base relation* `R` is the relation between the two interpretations of the
representation; it is chosen rather than derived, and a generated relation
quantifies over it. A *logical relation* extends `R` to compound types by recursion
on type structure: arguments mentioning no representation are shared, arguments
mentioning one are related, and a function must send related inputs to related
outputs.

[Translation.lean](Translation.lean) implements that recursion;
everything else here either feeds it or packages its result.

## Shape of the base relation

`R` takes its shape from the representation parameter, by the *shared-index interpretation*
in [Representation.lean](Representation.lean): open the parameter's whole
telescope, keep the indices shared, and put a binary relation at the final sort.

| Representation | Base relation |
| --- | --- |
| `A : Type u` | `A → B → Prop` |
| `repr : Ty → Type u` | `∀ ⦃t : Ty⦄, repr t → repr' t → Prop` |
| `m : Type u → Type v` | `∀ ⦃α : Type u⦄, m α → n α → Prop` |

The two interpretations share every index but need not share the final universe, so
`repr t` may be a runtime value where `repr' t` is a syntax tree. 

Relating values at
*different* indices is a different interpretation, and is not supported.

### Base relation aliasing

The complete base relation type is constructed first, then
[BaseRelationAliasing.lean](BaseRelationAliasing.lean) tries names registered with
`@[base_relation_alias]`. A name is used only when its arguments can be inferred
and its application is definitionally equal to the generated type; otherwise the
expanded type is retained. Each representation pair is matched independently.

[Common/BaseRelationAliases.lean](Common/BaseRelationAliases.lean) defines
some aliases that can be registered where desired:

```lean
section
open Tapas.LogicalRelation
attribute [local base_relation_alias 1100] ComputationRelation
attribute [local base_relation_alias] IndexedRelation
-- Derive relations here using these names when they apply.
end
```

Higher priorities are tried first (the default is 1000); ties are ordered by fully
qualified name. Both names apply to the monadic shape, so the higher priority above
prefers `ComputationRelation`. Registrations may also be global or scoped. They do
not assign existing metavariables or change declarations already generated.

## Three kinds of relation

| Kind | Relates | Origin |
| --- | --- | --- |
| relator | two applications of a type constructor `F` | written by hand, registered with `@[relator]` |
| interface relation `C.Rel` | two dictionaries of an interface `C` | `derive_interface_rel C (repr := A)` |
| type relation `T.Rel` | two values of a `Type`-valued definition `T` | `derive_type_rel T (repr := A)` |

An *interface* is a structure or typeclass whose fields are the operations of the object
language, so an interface relation states one condition per operation: related
arguments give related results. 

```lean
class Arith (A : Type u) where
  lit : Nat → A
  add : A → A → A

derive_interface_rel Arith (repr := A)
-- Arith.Rel R : Prop                           -- with [left : Arith A] [right : Arith B]
-- Arith.Rel.lit : ∀ n, R (left.lit n) (right.lit n)
-- Arith.Rel.add : ∀ x x', R x x' → ∀ y y', R y y' → R (left.add x y) (right.add x' y')
```

The recursion needs a relator or an interface relation exactly when it meets a head
symbol it cannot decompose further, which makes those two the extension points of
the translation. [Registry.lean](Registry.lean) holds the tables it looks them up
in; when neither has an entry, the derivation fails rather than inventing a relation.

Generating a relation does not prove that any particular term is related to itself.
That is a separate obligation, discharged by [Parametricity](../Parametricity) for a
given definition, or by hand for a given interpreter.

## Endpoint rules

After opening function binders, the translation relates `left : T` and `right : T'`
using the rules below. These are the leaf cases of the binder walk, possibly not the leaf cases of a recursion; for example, a relator may
still recurse into its arguments. 

In a walk, typically there is a *context* being maintained through, which contains representation pairs and their base relations
`(repr, repr', R)`. 
An expression is *independent* when it contains neither side
of any pair.

Each rule has an applicability condition **P**. Note that all rules below require matching arity of the two applications.

* **Representation values:** `T = repr is`, `T' = repr' is'`.

  **P:** the heads match a pair in the context; corresponding indices are **independent and definitionally equal**. Indices containing a representation are rejected,
  not recursively related.
  
  The result is `R is left right`. 
* **Interface dictionaries:** `T = D qs`, `T' = D qs'`.
  
  **P:** `D` has a registered interface relation and the arguments at its `reprParamIdx` **directly match** a representation
  pair (so containing a representation is insufficient: `D (List repr)` does
  not match the pair for `repr`). All other arguments must be definitionally equal across the two sides.

  The result applies the registered relation using that pair's `R` and the shared
  parameters. 
* **Relator applications:** `T = F as`, `T' = F as'`, with at least one side
  mentioning a representation.

  **P:** `F` has a registered relator; each shared argument is **independent and definitionally equal** on both
  sides. Each lifted argument admits a **recursively** constructed relation (so `F (F repr)` is allowed).

  The result applies the relator with those relations and the two endpoints.
* **Ordinary values:** 

  **P:** `T` and `T'` are independent, definitionally equal,
  and **not sorts**.
  
  The result is `left = right`.

These conditions determine the responsibilities of three modules:

* [Registry.lean](Registry.lean) stores the information needed to interpret **P**:
  the interface's `reprParamIdx`, and the relator's shared/lifted argument roles
  and relation-parameter positions (`relationParamIdxs`). The registered relation's
  type supplies its typing and universe constraints.
* [Translation.lean](Translation.lean) checks **P** against the two types and the
  current representation pairs, then constructs the relation. Registration alone
  does not establish applicability.
* [Representation.lean](Representation.lean) uses the sharing requirements in **P**
  to collect universe parameters that must stay fixed. This analysis does not itself establish **P**.

### Rule selection and failure

Rules are tried in the order above. An interface registration without a matching
representation pair permits relator fallback. Once a representation or interface
pair matches, failed sharing checks are errors; a selected relator's failure is
also an error.

## Modules

The translation and the tables it consults:

| Module | Contents |
| --- | --- |
| [Registry.lean](Registry.lean) | the two lookup tables and the `@[relator]` attribute |
| [Representation.lean](Representation.lean) | the representation parameter's base relation, and the universes both interpretations share |
| [BaseRelationAliasing.lean](BaseRelationAliasing.lean) | `@[base_relation_alias]` and definitionally equal abbreviations for generated base relation types |
| [Translation.lean](Translation.lean) | `relationAt`, the recursion above, and the shapes it rejects |

### [Derive/](Derive)

The commands, and the one spelling they share for saying which binders are
representations. [Derive.lean](Derive.lean) only gathers these.

| Module | Contents |
| --- | --- |
| [SelectionFrontend.lean](Derive/SelectionFrontend.lean) | the marker, the rules saying which binders are representations, and the `(repr := ...)` syntax the commands share |
| [InterfaceRelation.lean](Derive/InterfaceRelation.lean) | `derive_interface_rel`, generating interface relations |
| [TypeRelation.lean](Derive/TypeRelation.lean) | `derive_type_rel`, generating type relations |

### [Common/](Common)

Entries a client would otherwise have to write, registered or offered for
registration. Nothing above depends on them. [Common.lean](Common.lean) only gathers
these.

| Module | Contents |
| --- | --- |
| [Relators.lean](Common/Relators.lean) | relators registered for common type constructors |
| [BaseRelationAliases.lean](Common/BaseRelationAliases.lean) | common base relation aliases |
