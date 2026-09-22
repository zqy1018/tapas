# Ghost state

Ghost state through type classes: usable in proofs, executable as ordinary state,
and erasable from compiled IR. Parametricity connects these interpretations,
proving erasure for programs whose parametricity theorem has been established.

- [Basic.lean](Basic.lean): the capability, interpretations, and relations.
- [Programs.lean](Programs.lean): executions, erasure certificates, and changes of
  ghost-state representation.
- [WP.lean](WP.lean): `for` and `while` invariants that observe ghost state, with
  correctness transferred to executions without it.

## One interface, two interpretations

`MonadGhostOf I m` exposes `ghost : I → m PUnit`. Updates may inspect and transform
ghost state, but return no ghost values to the program.

- **`stateGhost`** executes updates in `StateT σ m`, using `GhostUpdateStep I σ`.
  The state is available to execution and WP assertions.
- **`erasedGhost`** interprets every update as `pure ⟨⟩` in the base monad.

## What parametricity gives

- **Erasure:** `Erase σ m` states `∀ s, Prod.fst <$> withGhost s = noGhost`.
  `Erase.monadRel` requires a lawful base monad; `Erase.ghostRel` holds for every
  update function. `countVals_certificate` applies `countVals.parametric` to these
  proofs. Partial fixpoints additionally use `Erase.admissible`, proved for `Option`.
- **Representation changes:** `Reindex` relates executions when each update
  respects the state mapping, including histories mapped to their lengths.
- **Correctness transfer:** WP invariants track `g = initial + 2 * acc`.
  Parametricity transfers the proved results to erased executions, including
  `countWhile (m := Option) n = some n`.

IR elimination relies on compiler specialization. Checked with
`trace.compiler.ir.result`, `countVals` specialized at `Plain` or `PlainOpt`
contains no ghost state or updates; `Counted` retains them. The unspecialized
function still calls the type class interface. Parametricity proves semantic
erasure; these IR checks confirm the optimization for the examples.
