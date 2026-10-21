module

import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.Freer.Basic
meta import TapasTest.Applications.Monad.Freer.Basic

public section

/-!
Composing signatures.

A signature is a request type `E : Type u → Type v`, and a program names the signatures it
uses, with one `MonadLiftT` each. Two signatures compose as their sum, `Sig.sum E₁ E₂`, a request
of either, and `Freer` turns a sum of signatures into the sum of their request trees:

- a handler of `Sig.sum E₁ E₂` is a handler of each summand (`Sig.sum.elim`);
- the capabilities `MonadLiftT E₁ m` and `MonadLiftT E₂ m` together are the capability
  `MonadLiftT (Sig.sum E₁ E₂) m`, in both directions (`MonadLiftT.sum`, `MonadLiftT.sumLeft`,
  `MonadLiftT.sumRight`), and so are the relations between two instances (`MonadLiftT.Rel.sum`,
  `MonadLiftT.Rel.sumLeft`, `MonadLiftT.Rel.sumRight`); a program over a sum and a program over
  its summands are interchangeable, together with their parametricity obligations;
- `Freer` is functorial in the signature (`Freer.rename`, `Freer.fold_rename`).

`Inj E₁ E` says that `E₁` is a summand of `E`, found by instance search through nested sums,
and gives `MonadLiftT E₁ (Freer E)`: a program over several signatures runs at the request trees
of their sum without naming the sum.

A monad is a signature once its structure is forgotten. `FreerT E m` of `Extraction.lean` is
`Freer (Sig.sum E m)`: the requests of `E` kept uninterpreted among the computations of `m`.
-/

namespace TapasTest.Applications.Monad.Freer.Signature

open TapasTest.Applications.Monad.Freer.Basic Tapas.LogicalRelation

universe u v w x y

/-! ## Sums of signatures -/

/-- The sum of two signatures: a request of either. -/
abbrev Sig.sum (E₁ : Type u → Type v) (E₂ : Type u → Type w) : Type u → Type (max v w) :=
  fun β => PSum (E₁ β) (E₂ β)

/-- A handler of a sum, from a handler of each summand. -/
@[expose] def Sig.sum.elim {E₁ : Type u → Type v} {E₂ : Type u → Type w} {F : Type u → Type x}
    (h₁ : (β : Type u) → E₁ β → F β) (h₂ : (β : Type u) → E₂ β → F β) :
    (β : Type u) → Sig.sum E₁ E₂ β → F β
  | _, .inl op => h₁ _ op
  | _, .inr op => h₂ _ op

/-- A signature within a larger one: an injection of its requests, found by instance search
through nested sums. -/
class Inj (E₁ : Type u → Type v) (E : Type u → Type w) where
  inj : {β : Type u} → E₁ β → E β

instance Inj.refl {E : Type u → Type v} : Inj E E := ⟨id⟩

instance (priority := low) Inj.sumRight {E₁ : Type u → Type v} {E₀ : Type u → Type w}
    {E₂ : Type u → Type x} [Inj E₁ E₂] : Inj E₁ (Sig.sum E₀ E₂) :=
  ⟨fun op => .inr (Inj.inj op)⟩

instance Inj.sumLeft {E₁ : Type u → Type v} {E₂ : Type u → Type w} : Inj E₁ (Sig.sum E₁ E₂) :=
  ⟨.inl⟩

/- Why this is a `MonadLiftT` instance and not a `MonadLift` one. The first parameter of
`MonadLift` is a `semiOutParam`: instance search may ask for `MonadLift ?n (Freer E)` with `?n`
unassigned, as `instMonadLiftTOfMonadLift` does on its way to a `MonadLiftT`. An instance of
`MonadLift E₁ (Freer E)` must therefore determine `E₁` from `Freer E` alone, before any of its
premises is solved, and the premise `Inj E₁ E` cannot be solved with `E₁` unknown; Lean rejects
such an instance when it is declared ("cannot find synthesization order"). Both parameters of
`MonadLiftT` are inputs, so a goal `MonadLiftT E₁ (Freer E)` supplies `E₁`, and `Inj E₁ E` is
found. The low priority prefers the route through the `MonadLift` instances below when one
applies, so that a lift into a sum's own request trees is the usual transformer-stack lift. -/
/-- A summand of `E` is requested at the request trees of `E`. -/
instance (priority := low) {E₁ : Type u → Type v} {E : Type u → Type w} [Inj E₁ E] :
    MonadLiftT E₁ (Freer E) :=
  ⟨fun op => .impure (Inj.inj op) .pure⟩

/- Why these two are `MonadLift` instances, and why only for the summands of one sum. Lifting
of the other capabilities is keyed on `MonadLift`, one step of a transformer stack:
`instMonadStateOfOfMonadLift` gives `MonadStateOf σ n` from `[MonadLift m n]` and
`MonadStateOf σ m`, and the instance for `MonadReaderOf` is alike; so is the unfolding of lifts
by `mvcgen`, which rewrites `liftM` to steps of `MonadLift.monadLift`. `MonadLiftT` is the
transitive closure of these steps and is never consumed in that way. This is what `FreerT E m`,
`Freer (Sig.sum E m)`, relies on: `get` and `set` of `m` are available at `FreerT E m`, and a
lifted computation keeps its specification there (`lift_spec` in `Extraction.lean`).

These instances are admissible where the one above is not because their semi-output parameter
is determined by the other parameter, `E₁` and `E₂` occurring in `Freer (Sig.sum E₁ E₂)`, and
they have no premises. A summand of a nested sum is not determined that way, and reaches the
request trees through the `MonadLiftT` instance above only. Where both routes apply, they give
the same lift, `impure (inj op) pure`. -/
instance {E₁ : Type u → Type v} {E₂ : Type u → Type w} : MonadLift E₁ (Freer (Sig.sum E₁ E₂)) :=
  ⟨fun op => .impure (.inl op) .pure⟩

instance {E₁ : Type u → Type v} {E₂ : Type u → Type w} : MonadLift E₂ (Freer (Sig.sum E₁ E₂)) :=
  ⟨fun op => .impure (.inr op) .pure⟩

/-! ## Request trees over a sum -/

/-- A request tree over `E₁` as one over `E₂`, along a translation of requests. -/
@[expose] def Freer.rename {E₁ : Type u → Type v} {E₂ : Type u → Type w} {α : Type u}
    (f : (β : Type u) → E₁ β → E₂ β) : Freer E₁ α → Freer E₂ α
  | .pure a => .pure a
  | .impure op k => .impure (f _ op) fun x => Freer.rename f (k x)

/-- Interpreting a renamed tree interprets the translated requests. -/
theorem Freer.fold_rename {E₁ : Type u → Type v} {E₂ : Type u → Type w} {α : Type u}
    {m : Type u → Type y} [Monad m] (h : (β : Type u) → E₂ β → m β)
    (f : (β : Type u) → E₁ β → E₂ β) (t : Freer E₁ α) :
    Freer.fold h (Freer.rename f t) = Freer.fold (fun β op => h β (f β op)) t := by
  induction t with
  | pure a => rfl
  | impure op k ih => simp only [Freer.rename, Freer.fold, ih]

/-! ## Capabilities for a sum and for its summands -/

section Capabilities

variable {E₁ : Type u → Type v} {E₂ : Type u → Type w} {m : Type u → Type x}

/-- A capability for a sum, from capabilities for its summands. -/
@[expose, instance_reducible] def MonadLiftT.sum [MonadLiftT E₁ m] [MonadLiftT E₂ m] :
    MonadLiftT (Sig.sum E₁ E₂) m :=
  ⟨fun {α} op => Sig.sum.elim (F := m) (fun _ => MonadLiftT.monadLift) (fun _ => MonadLiftT.monadLift) α op⟩

/-- A capability for the left summand, from one for the sum. -/
@[expose, instance_reducible] def MonadLiftT.sumLeft [MonadLiftT (Sig.sum E₁ E₂) m] :
    MonadLiftT E₁ m :=
  ⟨fun op => MonadLiftT.monadLift (m := Sig.sum E₁ E₂) (PSum.inl op)⟩

/-- A capability for the right summand, from one for the sum. -/
@[expose, instance_reducible] def MonadLiftT.sumRight [MonadLiftT (Sig.sum E₁ E₂) m] :
    MonadLiftT E₂ m :=
  ⟨fun op => MonadLiftT.monadLift (m := Sig.sum E₁ E₂) (PSum.inr op)⟩

variable {n : Type u → Type y} {R : ComputationRelation m n}

/-- Two instances for a sum are related when their instances for the summands are. -/
theorem MonadLiftT.Rel.sum [MonadLiftT E₁ m] [MonadLiftT E₁ n] [MonadLiftT E₂ m] [MonadLiftT E₂ n]
    (h₁ : MonadLiftT.Rel (m := E₁) R) (h₂ : MonadLiftT.Rel (m := E₂) R) :
    MonadLiftT.Rel (m := Sig.sum E₁ E₂) (left := MonadLiftT.sum) (right := MonadLiftT.sum) R :=
  MonadLiftT.Rel.mk (left := MonadLiftT.sum) (right := MonadLiftT.sum) R
    fun {α} (op : Sig.sum E₁ E₂ α) => match op with
      | PSum.inl op => h₁.monadLift op
      | PSum.inr op => h₂.monadLift op

/-- Two instances for the left summand are related when the instances for the sum are. -/
theorem MonadLiftT.Rel.sumLeft [MonadLiftT (Sig.sum E₁ E₂) m] [MonadLiftT (Sig.sum E₁ E₂) n]
    (h : MonadLiftT.Rel (m := Sig.sum E₁ E₂) R) :
    MonadLiftT.Rel (m := E₁) (left := MonadLiftT.sumLeft (E₂ := E₂))
      (right := MonadLiftT.sumLeft (E₂ := E₂)) R :=
  MonadLiftT.Rel.mk (left := MonadLiftT.sumLeft (E₂ := E₂)) (right := MonadLiftT.sumLeft (E₂ := E₂))
    R fun op => h.monadLift (PSum.inl op)

/-- Two instances for the right summand are related when the instances for the sum are. -/
theorem MonadLiftT.Rel.sumRight [MonadLiftT (Sig.sum E₁ E₂) m] [MonadLiftT (Sig.sum E₁ E₂) n]
    (h : MonadLiftT.Rel (m := Sig.sum E₁ E₂) R) :
    MonadLiftT.Rel (m := E₂) (left := MonadLiftT.sumRight (E₁ := E₁))
      (right := MonadLiftT.sumRight (E₁ := E₁)) R :=
  MonadLiftT.Rel.mk (left := MonadLiftT.sumRight (E₁ := E₁)) (right := MonadLiftT.sumRight (E₁ := E₁))
    R fun op => h.monadLift (PSum.inr op)

end Capabilities

/-! ## Example -/

/-- A request for a number. -/
inductive Ask : Type → Type where
  | ask : Ask Nat

/-- A request to record a number. -/
inductive Tell : Type → Type where
  | tell : Nat → Tell Unit

/-- Ask for a number and record its double. -/
def relay := infer_effects% do
  let n ← liftM Ask.ask
  liftM (Tell.tell (2 * n))

derive_parametric relay

-- Over the sum of its signatures, the program is a request tree, with each request injected
-- into the sum by `Inj`.
example : relay (m := Freer (Sig.sum Ask Tell)) =
    .impure (.inl .ask) fun n => .impure (.inr (.tell (2 * n))) .pure := rfl

/-- Answer every question with `21`. -/
def answer : (β : Type) → Ask β → StateM (List Nat) β
  | _, .ask => pure 21

/-- Record every number told. -/
def record : (β : Type) → Tell β → StateM (List Nat) β
  | _, .tell n => modify (· ++ [n])

-- Interpreting the sum is interpreting each summand.
#guard Id.run ((Freer.fold (Sig.sum.elim answer record) (relay (m := Freer (Sig.sum Ask Tell)))).run []) ==
  ((), [42])

/-- The requests of the sum, injected summand by summand into a larger sum. -/
def widen : (β : Type) → Sig.sum Ask Tell β → Sig.sum Ask (Sig.sum Tell Ask) β :=
  Sig.sum.elim (fun _ op => Inj.inj op) (fun _ op => Inj.inj op)

-- The renamed tree over the larger sum interprets as the original tree.
example (h : (β : Type) → Sig.sum Ask (Sig.sum Tell Ask) β → StateM (List Nat) β) :
    Freer.fold h (Freer.rename widen (relay (m := Freer (Sig.sum Ask Tell)))) =
      Freer.fold (fun β op => h β (widen β op)) (relay (m := Freer (Sig.sum Ask Tell))) :=
  Freer.fold_rename h widen _

#guard_axioms Freer.fold_rename, MonadLiftT.Rel.sum, MonadLiftT.Rel.sumLeft,
  MonadLiftT.Rel.sumRight ⊆ [propext, Quot.sound]
#guard_axioms relay.parametric ⊆ []

end TapasTest.Applications.Monad.Freer.Signature
