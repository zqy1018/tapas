module

import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.Freer.Basic

public section

/-!
Equalities of programs transfer from an adequate model to every interpretation.

A program written against a request type `E` has one request tree: its instance at `Freer E`.
An interpretation of the requests is a `MonadLiftT E m` instance into a lawful monad. By
parametricity, the program's instance at that monad is `toFinal` applied to its request tree
(`toFinal_toFreer_rel` in `Basic.lean`). An equality of request trees therefore holds in every
interpretation.

An interpretation is *adequate* when request trees with the same interpretation are equal. An
adequate interpretation, used for reasoning, is called a *model* below. Two programs equal in
a model have equal request trees, and are therefore equal in every interpretation. In the
diagram, `P[M]` is the program `P` instantiated at `M`:

```
P[M] <--- toFinal --- P[Freer E] ------ toFinal -----> P[m]
 |                     |                                |
 | heq                 | toFreer_eq_of_adequate         | eq_of_toFreer_eq
 v                     v                                v
Q[M] <--- toFinal --- Q[Freer E] ------ toFinal -----> Q[m]
```

The request trees are themselves an interpretation. Adequacy is therefore exactly the
condition for equalities in a model to hold in every interpretation (`adequate_iff`), and a
model can only prove equalities of request trees.

The same diagram works with a relation between results in place of equality (`transfer_rel`).
The relation between request trees is `TreeRel`, and the relations between computations are
given by relators.
-/

namespace TapasTest.Applications.Monad.Freer.Transfer

open Tapas.LogicalRelation TapasTest.Applications.Monad.Freer.Basic

universe u v w

/-! ## Adequacy -/

section Adequacy

variable {E : Type u → Type v} {M : Type u → Type w} [Monad M]

-- NOTE: Adequacy depends on the selected `MonadLiftT` instance, not just on the target monad.

/-- An interpretation is adequate when request trees with the same interpretation are equal. -/
@[expose] def Adequate [MonadLiftT E M] : Prop :=
  ∀ {α : Type u} (t t' : Freer E α),
    toFinal t (m := M) = toFinal t' (m := M) → t = t'

/-- Interpreting the requests as themselves is adequate. -/
theorem adequate_self : Adequate (E := E) (M := Freer E) := by
  intro α t t' h
  simpa only [toFinal, Freer.fold_self] using h

-- The request trees are among the interpretations, so the quantification ranges over the
-- universe of `Freer E`.
/-- An interpretation is adequate exactly when request trees with the same interpretation have
the same interpretation in every monad. -/
theorem adequate_iff [MonadLiftT E M] :
    Adequate (E := E) (M := M) ↔ ∀ {α : Type u} (t t' : Freer E α),
      toFinal t (m := M) = toFinal t' (m := M) →
      ∀ {m : Type u → Type (max (u + 1) v)} [Monad m] [MonadLiftT E m],
        toFinal t (m := m) = toFinal t' (m := m) := by
  constructor
  · intro had α t t' heq m _ _
    rw [had t t' heq]
  · intro hall α t t' heq
    exact adequate_self t t' (hall t t' heq (m := Freer E))

end Adequacy

/-! ## Transfer -/

section Transfer

/-
A program appears at two universes: `p` at the universe of the request trees, where its request
tree is `toFreer @p`, and `p'` at the universe of the model `M` and of the interpretation `m`.
`Final.Rel @p @p'` relates the two instances.
-/
variable {E : Type u → Type v} {α : Type u}
  {p q : Final.{u, v, max (u + 1) v} E α}
  {p' q' : Final.{u, v, w} E α}
  {M : Type u → Type w} [Monad M] [LawfulMonad M] [MonadLiftT E M]
  {m : Type u → Type w} [Monad m] [LawfulMonad m] [MonadLiftT E m]
variable (hp : Final.Rel @p @p') (hq : Final.Rel @q @q')
include hp hq

/-- In a model, two programs with the same interpretation have the same request tree. -/
theorem toFreer_eq_of_adequate
    (had : Adequate (E := E) (M := M))
    (heq : p' (m := M) = q' (m := M)) : toFreer @p = toFreer @q :=
  had _ _ ((toFinal_toFreer_rel @p @p' hp).trans
    (heq.trans (toFinal_toFreer_rel @q @q' hq).symm))

/-- Two programs with the same request tree are equal in every lawful interpretation. -/
theorem eq_of_toFreer_eq
    (htree : toFreer @p = toFreer @q) : p' (m := m) = q' (m := m) := by
  rw [← toFinal_toFreer_rel @p @p' hp, ← toFinal_toFreer_rel @q @q' hq, htree]

/-- Two programs equal in a model are equal in every lawful interpretation. -/
theorem transfer (had : Adequate (E := E) (M := M))
    (heq : p' (m := M) = q' (m := M)) : p' (m := m) = q' (m := m) :=
  eq_of_toFreer_eq hp hq (toFreer_eq_of_adequate hp hq had heq)

end Transfer

/-! ## Related results -/

/-
Two request trees are related when they make the same requests in the same order and their
results are related; with equality between results, this is equality (`TreeRel.eq`). A
relator relates the computations of a monad for every relation between results, compatibly
with `pure` and `bind`. Every interpretation maps related request trees to computations related
by any relator (`TreeRel.fold`).
-/

-- NOTE: This relator is written by hand because Tapas does not yet derive relators for
-- inductive types.
/-- Two request trees make the same requests in the same order, and their results are related
by `S`. -/
inductive TreeRel {E : Type u → Type v} {α β : Type u} (S : α → β → Prop) :
    Freer E α → Freer E β → Prop
  | pure {a : α} {b : β} : S a b → TreeRel S (.pure a) (.pure b)
  | impure {γ : Type u} (op : E γ) {k : γ → Freer E α} {k' : γ → Freer E β} :
      (∀ x, TreeRel S (k x) (k' x)) → TreeRel S (.impure op k) (.impure op k')

theorem TreeRel.eq {E : Type u → Type v} {α : Type u} {t t' : Freer E α}
    (h : TreeRel Eq t t') : t = t' := by
  induction h with
  | pure h => rw [h]
  | impure op _ ih => exact congrArg (Freer.impure op) (funext ih)

/-
NOTE: This manual structure works around Tapas's shared-index limitation: generated
`Monad.Rel` compares `m α` with `n α` at the same result type. Relational transfer needs
relations between `m α` and `m β` parameterized by `S : α → β → Prop`, so the corresponding
`pure` and `bind` conditions are stated by hand. The additional `refl` condition relates
each interpreted request to itself in `TreeRel.fold`.
-/
/-- Relations between the computations of a monad, one for every relation between results,
that `pure` and `bind` respect and that relate every computation to itself. -/
structure MonadRelator (m : Type u → Type w) [Monad m] where
  rel : {α β : Type u} → (α → β → Prop) → m α → m β → Prop
  pure : ∀ {α β : Type u} {S : α → β → Prop} {a : α} {b : β}, S a b → rel S (pure a) (pure b)
  bind : ∀ {α β γ δ : Type u} {S : α → β → Prop} {S' : γ → δ → Prop} {x : m α} {y : m β}
    {f : α → m γ} {g : β → m δ}, rel S x y → (∀ a b, S a b → rel S' (f a) (g b)) →
      rel S' (x >>= f) (y >>= g)
  refl : ∀ {γ : Type u} (x : m γ), rel Eq x x

/-- Every interpretation maps related request trees to related computations. -/
theorem TreeRel.fold {E : Type u → Type v} {m : Type u → Type w} [Monad m]
    [MonadLiftT E m] (RT : MonadRelator m) {α β : Type u} {S : α → β → Prop}
    {t : Freer E α} {t' : Freer E β} (hrel : TreeRel S t t') :
    RT.rel S (toFinal t (m := m)) (toFinal t' (m := m)) := by
  induction hrel with
  | pure hs => exact RT.pure hs
  | impure op _ ih => exact RT.bind (RT.refl (monadLift op)) fun a b hab => by subst hab; exact ih a

/-- An interpretation is relationally adequate when request trees with related interpretations
are related. -/
@[expose] def RelAdequate {E : Type u → Type v} {M : Type u → Type w} [Monad M]
    [MonadLiftT E M] (RM : MonadRelator M) : Prop :=
  ∀ {α β : Type u} (S : α → β → Prop) (t : Freer E α) (t' : Freer E β),
    RM.rel S (toFinal t (m := M)) (toFinal t' (m := M)) → TreeRel S t t'

/-- Relational adequacy implies adequacy. -/
theorem adequate_of_relAdequate {E : Type u → Type v} {M : Type u → Type w} [Monad M]
    [MonadLiftT E M] {RM : MonadRelator M} (had : RelAdequate (E := E) RM) :
    Adequate (E := E) (M := M) :=
  fun t t' h => (had Eq t t' (h ▸ RM.refl _)).eq

section TransferRel

variable {E : Type u → Type v} {α β : Type u} {S : α → β → Prop}
  {p : Final.{u, v, max (u + 1) v} E α} {q : Final.{u, v, max (u + 1) v} E β}
  {p' : Final.{u, v, w} E α} {q' : Final.{u, v, w} E β}
  {M : Type u → Type w} [Monad M] [LawfulMonad M] [MonadLiftT E M]
  {m : Type u → Type w} [Monad m] [LawfulMonad m] [MonadLiftT E m]

/-- Two programs related in a relationally adequate model are related in every lawful
interpretation, by every relator. -/
theorem transfer_rel (hp : Final.Rel @p @p') (hq : Final.Rel @q @q') {RM : MonadRelator M}
    (had : RelAdequate (E := E) RM)
    (hrel : RM.rel S (p' (m := M)) (q' (m := M))) (RT : MonadRelator m) :
    RT.rel S (p' (m := m)) (q' (m := m)) := by
  rw [← toFinal_toFreer_rel @p @p' hp, ← toFinal_toFreer_rel @q @q' hq]
  apply TreeRel.fold RT
  apply had
  rw [← toFinal_toFreer_rel @p @p' hp, ← toFinal_toFreer_rel @q @q' hq] at hrel
  exact hrel

end TransferRel

/-! ## Examples -/

/-- A request for a number. -/
inductive Ask : Type → Type where
  | ask : Ask Nat

/-- Ask for two numbers and add them. -/
def addAsks := infer_effects% do
  let a ← liftM Ask.ask
  let b ← liftM Ask.ask
  pure (a + b)

/-- Ask for two numbers and add them in the other order. -/
def addAsksSwapped := infer_effects% do
  let a ← liftM Ask.ask
  let b ← liftM Ask.ask
  pure (b + a)

derive_parametric addAsks
derive_parametric addAsksSwapped

/-- Answer from a list of numbers, where a missing number is `0`. -/
def answerFromList : (β : Type) → Ask β → StateM (List Nat) β
  | _, .ask => modifyGet fun input => (input.headD 0, input.tail)

local instance : MonadLift Ask (StateM (List Nat)) := ⟨answerFromList _⟩

-- The request trees of the two programs are equal, so the programs agree in every lawful
-- interpretation. This is the case where the model is the request trees themselves.
example : addAsksSwapped (m := StateM (List Nat)) = addAsks (m := StateM (List Nat)) :=
  eq_of_toFreer_eq addAsksSwapped.parametric addAsks.parametric
    (by simp [toFreer, addAsks, addAsksSwapped, Nat.add_comm])

/-- Answer every request with `0`. -/
def answerZero : (β : Type) → Ask β → Id β
  | _, .ask => pure 0

/-- Fixing every answer is not adequate: continuations are never observed at other answers. -/
theorem answerZero_not_adequate :
    letI : MonadLift Ask Id := ⟨answerZero _⟩
    ¬ Adequate (E := Ask) (M := Id) := fun had =>
  nomatch had (Freer.impure Ask.ask Freer.pure) (Freer.pure 0) rfl

#guard_uses adequate_iff ⊇ [adequate_self]
#guard_uses transfer ⊇ [toFreer_eq_of_adequate, eq_of_toFreer_eq]
#guard_uses transfer_rel ⊇ [TreeRel.fold]
#guard_uses adequate_of_relAdequate ⊇ [TreeRel.eq]
#guard_axioms answerZero_not_adequate, TreeRel.fold ⊆ []
#guard_axioms adequate_self, adequate_iff, TreeRel.eq, adequate_of_relAdequate ⊆ [Quot.sound]
#guard_axioms toFreer_eq_of_adequate, eq_of_toFreer_eq, transfer, transfer_rel ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.Transfer
