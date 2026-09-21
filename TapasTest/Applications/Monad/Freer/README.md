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
