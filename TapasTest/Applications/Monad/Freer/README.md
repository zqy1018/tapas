# Freer ↔ Tagless final, and applications

A minimal experiment in converting between freer and tagless-final representations.

- [Basic.lean](Basic.lean): `Freer`, monad instances, `fold`, `toFinal` / `toFreer`, and general proofs.
- [StateAdapter.lean](StateAdapter.lean): adapt an ordinary `MonadStateOf` program to `Final`,
  reusing its parametricity certificate to prove the roundtrip.
- [FinalPrograms.lean](FinalPrograms.lean): write sequential, branching, and recursive programs
  directly as `Final` values, derive their parametricity, and instantiate the roundtrip theorems.
- [WP.lean](WP.lean): verify a reified program from operation specifications, then transfer its
  postcondition to the original final program under any handler satisfying those specifications.
- [Lowering.lean](Lowering.lean): replace pair requests with individual reads and prove that
  executing the resulting program preserves the original program's behavior.
- [Extraction.lean](Extraction.lean): verify a program at an instantiation that reifies its
  uninterpreted operations, and transfer the result to the instantiation that executes them.

## Key theorems in [Basic.lean](Basic.lean)

- `toFreer_toFinal`:
  `toFreer (toFinal t) = t`.
  Holds for every freer program, using `Freer.fold_self`, proved by structural induction.
- `toFinal_rel`:
  every freer program gives final interpretations satisfying `Final.Rel`,
  which `derive_type_rel` generates from the type of `Final`.
  This relation requires related results for any monad dictionaries and handlers
  that preserve a computation relation, including across computation universes.
- `toFinal_toFreer_rel`:
  `toFinal (toFreer p) h = q h`, assuming `Final.Rel p q` and a lawful target monad.
  Here `p` and `q` can be two universe instances of the same program: reification
  uses the universe of `Freer E`, while execution may use a smaller universe.
- `toFinal_toFreer`:
  `toFinal (toFreer p) (m := m) = p (m := m)`, assuming `Final.Rel p p` and a lawful `m`.
  This specializes `toFinal_toFreer_rel` to `q := p` and applies function extensionality
  over handlers. Here `m` uses the same computation universe as `Freer E`.

The tagless-final-to-freer direction is pointwise equality in lawful monads under an explicit
parametricity certificate. There is no unconditional equality of arbitrary raw
`Final` programs, whose type also admits unlawful monad dictionaries.

## Verification from operation specifications ([WP.lean](WP.lean))

- `sumInputs_spec` proves the result bound in `Freer InputOp`, the concrete monad of
  uninterpreted requests, using their operation specifications.
- `sumInputs_correct` uses `fold_sound` and parametricity to transfer that proof to
  any interpretation satisfying those specifications.
- `sumInputs_run_bound` specializes this to an execution bound for the original program
  with any choice function that respects the input bounds.

## Effect lowering ([Lowering.lean](Lowering.lean))

- `fold_lower` turns agreement on each translated request into agreement on every request tree.
  The handlers must agree on the translation; monad laws alone do not imply this.
- `difference_correct` combines the lowering theorem with parametricity and roundtrip to
  relate the compiled request tree to the original `Final` program.
- `difference_run_eq` gives equality of both the returned value and remaining input for
  every input list, including exhausted input.

## Extraction as an instantiation ([Extraction.lean](Extraction.lean))

Instantiating a program at `Symbolic n` reifies its advice and base-state operations;
instantiating it at `Exec n` executes them. Both use the same definition written
with `infer_effects%`.

- **Verify from specifications:** `spend_spec` and `spendRounds_spec` prove that
  the remaining balance plus the amount spent equals the initial balance. The
  proof covers every suggestion allowed by `adviceSpec`, without choosing an advisor.
- **Connect the executions:** `spend_extracted` and `spendRounds_extracted` use
  parametricity to prove that interpreting the reified requests equals executing
  the original program, for any lawful base monad and any advisor interpretation.
- **Transfer correctness:** `spend_correct` and `spendRounds_correct` combine that
  equality with `interpret_sound`. Each advisor only needs a `Sound` proof that its
  operations satisfy their specifications; `half_sound` and `greedy_sound` provide
  two examples that reuse the same program proofs.

The WP examples use `Id` as the base monad and bounded loops; the extraction
equalities hold for arbitrary lawful base monads.
