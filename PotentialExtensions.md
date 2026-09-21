# Potential extensions

## Multiple representation parameters in interface relations

**Status: deferred until a concrete application requires it.** Do not pursue this
extension, or refactor existing APIs in preparation for it, solely for generality.
The current model of one selected representation with all other interface
parameters shared remains the default.

An interface could select several representation parameters and take one base
relation for each. For example:

```lean
class Language (Term : Type u) (Value : Type v) where
  eval  : Term → Value
  quote : Value → Term
```

Comparing two interpretations could use `RT : Term → Term' → Prop` and
`RV : Value → Value' → Prop`. The interface relation would require:

```lean
∀ t t', RT t t' → RV (left.eval t) (right.eval t')
∀ v v', RV v v' → RT (left.quote v) (right.quote v')
```

The underlying relation translator already accepts several representation pairs.
The interface generator and registry currently select and record only one
representation position, and interface relation application requires all other
parameters to be shared. Supporting several selected positions would extend
these mechanisms while retaining the existing relation construction rules.

Any initial implementation should preserve the current shared-index semantics.
Several base relations suffice for operations such as `Term → Value`, but do not
automatically support changing a representation used as another representation's
index. For example, with both `m` and `A` selected, relations
`Rm : ∀ {α}, m α → n α → Prop` and `RA : A → B → Prop` do not relate `m A` to
`n B`: `Rm` requires the same index on both sides. Such uses, and dependent kinds
such as `B : A → Type`, would require a further extension and should remain
unsupported initially.

Universe constraints must be collected jointly for all selected representations,
their shared index domains, and the remaining shared parameters. A single
consistent universe substitution should then be applied to the target
declaration. Processing representations independently must not accidentally fix
another selected representation's universes or break universe sharing already
present in the declaration.

Interface application would reuse the supplied base relation for each selected
position. This would not make interface arguments behave like relator arguments,
whose relations are constructed recursively. Extending public program derivation
to select several representations would also need its own scope and validation;
it does not follow merely from extending interface relations.

## Multiple representation parameters in program derivation

**Status: deferred.** Revisit when a concrete application requires it; do not
generalize `derive_parametric` or refactor its APIs in preparation for it now.

The following is a source review as of 2026-09-21, not an implemented or validated
generalization. The one-representation restriction in `deriveMember` is an
implementation boundary, not a requirement of parametricity. For example:

```lean
def applyFn {A B : Type} (f : A → B) (x : A) : B := f x
```

Selecting both `A` and `B` would introduce `RA : A → A' → Prop` and
`RB : B → B' → Prop`. Given `f' : A' → B'` and `x' : A'`, its theorem would
conclude `RB (applyFn f x) (applyFn f' x')` from:

```lean
hf : ∀ a a', RA a a' → RB (f a) (f' a')
hx : RA x x'
```

### Existing support and remaining assumptions

`LogicalRelation/Translation.lean` already carries an
`Array RelatedRepresentation`; `withRelatedTelescope` introduces a target
representation and base relation for each selected binder. `ProofContext` also
carries this array. The `TwoPairs` example in `TapasTest/EndToEnd/Shapes.lean`
checks a generated type relation with two base relations and differing universes.
This supports reusing the translation machinery, but does not establish that
whole-program proof generation already works for multiple selected parameters.

`Parametricity/Program.lean` still assumes one representation when it:

* matches `candidates` against `#[repr]` and collects universe constraints using
  that representation alone;
* takes `t.representations[0]?` and builds the final theorem's binders around
  `#[pair.target, pair.relation]`;
* prepares an optional admissibility premise for that one base relation.

Removing only the cardinality check would therefore be insufficient: the final
theorem could omit another base relation used by its proof. Generalization needs
joint universe constraint collection and complete, dependency-respecting binder
assembly, while preserving the existing single-representation theorem API.
Admissibility must be handled for the relation actually needed by the recursive
computation, rather than assuming the first selected representation supplies it.

Programs with several independent representations need not require interfaces
with several varying parameters. A program can use a function `A → B`, or
separate interfaces for `A` and `B`, while each interface still varies in only
one parameter. An interface such as `Language Term Value` requires the separate
registry and interface-generation extension described above: the current
`InterfaceRelationInfo.reprParamIdx` records only one position, and translation
requires other interface arguments to agree between interpretations.

### Scope and estimated difficulty

These are qualitative estimates from source inspection; no generalization
prototype or performance experiment was run for this review.

| Scope | Estimated difficulty | Main work |
| --- | --- | --- |
| Non-recursive programs with independent representations | Low to moderate | Joint universe analysis and theorem binder assembly; reuse existing translation and proof search where possible |
| Structural, well-founded and mutual recursion | Moderate | Check relational motives, fixed/varying argument correspondence and recursive hypotheses |
| Interfaces with several varying parameters | Moderate to high | Change relation metadata, generation, application and affected callers |
| Multiple representations with `partial_fixpoint` | Moderate to high | Establish and supply admissibility for the required relation, including any composition |
| Changing representation indices or dependent representation kinds | High | Extend the relation semantics, beyond parameter bookkeeping |

If resumed, a bounded first stage would cover non-recursive programs whose
selected representation kinds and indices do not depend on another selected
representation. They may still share universe parameters. Validate a function
between two representations, a result containing both (such as a product),
separate existing interface relations, and differing universes. Check the
generated theorem statements, their uses and axioms, and preservation of the
single-representation regression suite. Treat recursion, fixpoints and
multi-parameter interfaces as separate follow-ups.

The shared-index restriction above remains in force: supporting independent
`A` and `B` does not by itself support simultaneously varying `m` and `A` in
`m A`, or a dependent representation kind such as `B : A → Type`.
