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

## Capability inference for recursive definitions

**Status: deferred.** Recursive programs keep writing their monad and capability
binders out by hand. Do not extend `infer_effects%` itself in preparation for
this; the extension is a new command, not a wider term elaborator.

`infer_effects%` is a term elaborator: it applies to a definition whose value is
one term. Every recursive definition in
`TapasTest/Applications/Monad/ControlFlow/Recursion.lean` therefore states
`{m : Type → Type v} [Monad m] [MonadStateOf Nat m]` itself, while the
non-recursive ones beside them are inferred. This section records why, and what a
command-level frontend would have to do.

### What can be converted today

`viaRec` alone, which is not recursive: it is a `Nat.rec` application, and
`infer_effects% Nat.rec get (fun j ih => set j *> ih) k` infers
`[Monad m] [MonadStateOf Nat m]` and leaves the `derive_parametric` error it is
there to record unchanged. *Verified.* Nothing else in that file is a single
term.

### Two obstacles

The first is syntactic. `termination_by` and `decreasing_by` (`halve`), `mutual`
(`evenSteps`, `oddSteps`), `partial_fixpoint` (`pfix`), `partial` (`spin`) and
`where` (`outer`) are part of the `def` command. A term elaborator receives the
value and nothing else, so it cannot see them.

The second is why the first cannot be worked around by rephrasing inside a term.
Recursion needs a signature *before* the body: the equation compiler builds
`brecOn` or `WellFounded.fix` over a settled one. Capability inference reads the
signature *off* the body, and a recursive occurrence needs its capability
dictionaries at the use site, before the body it is in has been elaborated. A
term elaborator has nowhere to put the missing binders and no way to revisit the
occurrences once it knows them; the next section is about the place that does.

*Verified*, by rephrasing the two cases that a term elaborator can reach:

* `let rec go : Nat → _ | 0 => pure 0 | k + 1 => do set k; let r ← go k; pure (r + 1)`
  inside an `infer_effects%` body reports
  `interface inference: unresolved argument of type Nat → m Nat`.
* A `where` helper on a definition whose value is `infer_effects% ...` reports
  `don't know how to synthesize implicit argument m`. The helper's body is
  elaborated outside the elaborator's scope, where `m` does not exist.

### A command-level frontend

Lean already solves the same shape for `let rec`, which is where this should be
built from rather than from a second elaboration pass. The pieces, as of Lean
4.32.0:

* `Lean.Elab.Term.withFunLocalDecls` (`Lean/Elab/MutualDef.lean`) elaborates a
  recursive body with the function bound as an ordinary *local hypothesis*, and
  converts those occurrences back into constant applications afterwards. This is
  what stands in for the recursive occurrence, and it is the same answer
  Hindley-Milner gives for a binding group: the occurrence stays monomorphic
  while the constraints are collected, and generalization happens once at the
  end.
* `Lean.Elab.MutualDef.MutualClosure` lifts `let rec` functions, which are
  encoded as `let f : A := ?m; body` with a synthetic opaque placeholder. After
  the body is elaborated it computes, by *fixpoint* over the group, the free
  variables each lifted function actually uses, abstracts them into that
  function's signature, rewrites the call sites, and assigns the placeholder.
  That is this extension's job exactly, one step removed: the capabilities to
  abstract are unassigned instance metavariables rather than free variables.
* `Lean.Elab.PreDefinition` takes `type : Expr` and `value : Expr`, and
  `addPreDefinitions` dispatches structural recursion, well-founded recursion,
  `mutual` and `partial_fixpoint` from there. None of them re-elaborates syntax.

So the shape is one elaboration, not two: elaborate the body with the function
as a local hypothesis of its written signature, collect the capabilities with the
existing `abstractTCArgsCore`, abstract them into the signature and rewrite the
recursive occurrences to pass them, then hand a `PreDefinition` to
`addPreDefinitions`. `termination_by`, `mutual` and `partial_fixpoint` follow
from the last step rather than needing anything of their own. The earlier
concerns about elaborating the body twice, and about `where` and `let rec`
emitting their auxiliary declarations twice, do not arise.

What remains to be settled, which was not tried:

* The local hypothesis standing for the recursive occurrence carries the
  signature *as written*, without the capability binders. Whether the capability
  set collected under it agrees with the one the finished signature binds is the
  question to answer first, and the only one the pieces above do not answer.
* A `mutual` block settles no signature until the capability sets of all its
  functions have been collected and merged. `MutualClosure` already merges by
  fixpoint over the group, so this may come for free.
* `pfix` needs `[∀ α, CCPO (m α)]` and `[MonoBind m]`, which
  `infer_effects_partial%` supplies and `infer_effects%` does not. The command
  has to compose with the frontend that adds them, rather than choose one of the
  two.

### Prior art, and what it costs

Two of the three below reach declaration level by going through the delaborator.
That is the cost the plan above avoids, and the reason to read them before
copying either.

*Veil* -- the library this repository's `abstractTCArgsCore` and
`simplifyAndAbstractMVar` come from -- does reach declaration level, by
delaborating each inferred instance type back into binder syntax and re-issuing
the declaration. It has to emit an `abbrev` for each inferred type first, with
the reason in its own comment: "to avoid delaboration round-trips that can fail
or be slow". Its `simplifyMVarType` also throws on the delayed assignments that
`collapseDelayedAssignments` now carries out here, and for the same trigger, a
tactic block under a binder.

Mathlib's `variable?` infers missing instance binders by elaborating binders one
at a time, pretty-printing whatever instance fails to synthesize into new binder
syntax, and restarting, bounded by a `maxSteps` gas. Its own documentation says
there are no guarantees the result is the correct list of binders.

Lean's `withAutoBoundImplicit` is the same restart-and-retry loop done at the
expression level -- it catches the auto-bound exception, restores the saved
state, introduces a `withLocalDecl`, and retries -- and is worth reading for how
it undoes a failed attempt, but it discovers one binder per exception and applies
only to a declaration header.
