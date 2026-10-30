# Specialization in vcgen and specification normalization

The comparison varies the representation of specifications and the operation specs.
These choices enter the two proof routes in different ways.

## Where specialization happens

`vcgen` works through Lean's `WP` interface, whose predicate transformers use
`PredTrans`. It applies `@[spec]` lemmas rather than unfolding that representation.
A hand-written lemma can summarize an operation on a whole transformer stack;
library specs instead use lifting rules to reach an inner layer.

Specification normalization instantiates the polymorphic program in a specification
monad and unfolds it. Both the representation and the operation definitions can be
chosen. Their unfolding contributes to normalization and kernel-checking costs.

To justify a representation, we prove that its soundness relation is preserved by
`pure` and `bind`, once for all cases ([Specification.lean](Specification.lean)).
Each operation also needs a soundness proof ([Models.lean](Models.lean)); in these
cases most follow by definitional unfolding. Parametricity then supplies the
program's soundness bridge. For vcgen, a hand-written `@[spec]` lemma states the
operation's contract directly; library operations already have such lemmas.

## The tiers

| Tier | Normalization | vcgen |
|---|---|---|
| `custom-monad` | Function-type `Spec` with hand-written operation specs | — |
| `hand-written-specs` | `PredTrans` with hand-written operation specs | The upstream operation specs |
| `library` | `PredTrans` with Lean's instances | Library operation specs |

The two `PredTrans` tiers share their VCs and soundness bridges in
[Conditions.lean](Conditions.lean), varying only the operation instances.
Comparing them isolates operation specialization; comparing `custom-monad` with
`hand-written-specs` also changes the representation. In vcgen's library tier, the
upstream operation specs are erased so that the library rules are used.

The custom monad is `Spec Pred α := (α → Pred) → Pred`. It omits exception
postconditions and interprets an uncaught throw as `False`. This suffices for the
eight goals, which use `⊥` as their exception postcondition.

## Case-specific choices

- **Deep add/sub:** hand-written specs access the inner state directly; library
  specs and instances lift through the transformer stack.
- **ReaderState:** the reader and state are both `Nat`. The normalization library
  tier explicitly selects Lean's lifting state instance to reach the state rather
  than the reader.
- **PurePrecond:** `flipp`'s specs are procedure contracts, so every tier keeps them.
  Its two `PredTrans` tiers coincide.

The library normalization tier reuses Lean's instances, with adapters for our
inferred interfaces where needed (for example, `Throw` delegates to Lean's `throw`).
The hand-written tiers instead supply operation definitions tailored to each
assertion type. Both provide operation soundness proofs.
