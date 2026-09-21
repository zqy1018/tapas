# Data refinement

Using parametricity for data refinement: two interpretations of one
capability, differing in a representation the capability does not mention.

- [Basic.lean](Basic.lean): the capability, its two interpretations, 
  the relation `R` that defines refinement, and the obligations.
- [Programs.lean](Programs.lean): programs written once against `Store`, their
  certificates, executions, and the negative checks.

## The obligations, proved by hand

- **`monadRel`**: `Monad.Rel R`, from `pure_rel` and `bind_rel` through
  `Monad.Rel.ofPureBind`, both monads being lawful.
- **`storeRel`**: `Store.Rel R`, the class `derive_effect_rel Store` generates. Its
  three fields are the refinement's proof obligations, one per operation. `fetch` and
  `store` are equations; `sandbox` takes a computation, so its obligation is that
  related bodies give related results.

## What parametricity gives

- **`transfer_correct`**: `R (transfer (m := Source) amount) (executable amount)`, proved
  by `transfer.parametric amount R monadRel storeRel`.
- **`sandboxCertificate`**: the same for `nestedSandbox`, one `sandbox` inside
  another. Nesting adds no obligation.
