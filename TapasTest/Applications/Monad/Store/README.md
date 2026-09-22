# Data refinement

One program, two store representations: a logical map and an executable update
journal. Parametricity proves that changing the representation preserves returned
values and the logical contents of the final store.

- [Basic.lean](Basic.lean): the capability, interpretations, and refinement relation.
- [Programs.lean](Programs.lean): transfers, nested sandboxes, executions, and
  refinement certificates, including a rejected implementation.

## One interface, two interpretations

`Store m` exposes `fetch`, `store`, and `sandbox`. A sandbox runs a computation,
keeps its return value, and restores the initial store. Programs use this interface
without naming the state representation.

- **`Source`** stores a logical map `String → Nat`; writes update the function.
- **`Target`** stores a journal `List (String × Nat)`; writes prepend entries.
  `decode` reads the most recent matching entry, returning zero for missing keys.

## What parametricity gives

The relation `R source target` states, for every initial journal:

```lean
source (decode journal) = ((target journal).1, decode (target journal).2)
```

- **Operation proofs:** `monadRel` proves that `pure` and `bind` preserve `R`;
  `storeRel` proves it for each store operation. For `sandbox`, related bodies
  must give related sandboxed executions.
- **Program certificates:** once a program's parametricity theorem is proved,
  these operation proofs establish refinement. `certificate` is simply
  `transfer.parametric amount R monadRel storeRel`; `transfer_correct` exposes the
  execution equality. `sandboxCertificate` handles nesting with the same proofs.

Refinement compares logical contents, so redundant or shadowed journal entries
are allowed. The tests demonstrate this and reject a `sandbox` implementation
that fails to restore state.
