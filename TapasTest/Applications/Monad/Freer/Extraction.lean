module

import TapasTest.Applications.Monad.Freer.WP
import Std.Tactic.Do

/-!
One program, two instantiations. A nondeterministic choice is reified on top of a base monad,
so that a verification covers every possible answer, while an execution gives one answer to
each choice. Parametricity relates the two instantiations, so every postcondition the
verification proves also holds of the execution, without revisiting the program. The main
result is `spendRounds_correct`.

A choice is requested by the type of its answers, and some types have no values. The type of a
reified program does not tell which types it chooses from, so an interpretation of it has to
answer every type, which is impossible for a type without values. The signature of the program
does tell, and an execution only has to answer those types.
-/

namespace TapasTest.Applications.Monad.Freer.Extraction

open Std.Do Tapas.Parametricity Tapas.LogicalRelation
open TapasTest.Applications.Monad.Freer.Basic
open TapasTest.Applications.Monad.Freer.WP (wpMonad)

universe u v w

/-- Uninterpreted operations of `E`, interleaved with computations of `m`. -/
abbrev FreerT (E : Type u → Type v) (m : Type u → Type w) :=
  Freer (fun β => PSum (E β) (m β))

instance {E : Type u → Type v} {m : Type u → Type w} : MonadLift m (FreerT E m) where
  monadLift x := .impure (.inr x) .pure

/-! ## Choosing a value of a type -/

/-- Choose a value of `τ`. -/
class MonadChoice (τ : Type u) (m : Type u → Type v) where
  pick : m τ

derive_effect_rel MonadChoice

/-- A request for a value of the given type. -/
inductive Choice : Type → Type where
  | pick (τ : Type) : Choice τ

-- A request exists for every type, whether or not the type has values.
/-- Choices are reified as requests. -/
instance {m : Type → Type w} {τ : Type} : MonadChoice τ (FreerT Choice m) where
  pick := .impure (.inl (.pick τ)) .pure

/-- Demonic choice: the postcondition must hold for every value. -/
def pickAny {ps : PostShape.{u}} {α : Type u} : PredTrans ps α where
  trans Q := spred(∀ a, Q.1 a)
  conjunctiveRaw := by
    intro Q₁ Q₂
    refine SPred.bientails.iff.mpr ⟨?_, ?_⟩
    · exact SPred.and_intro (SPred.forall_mono fun _ => SPred.and_elim_l)
        (SPred.forall_mono fun _ => SPred.and_elim_r)
    · exact SPred.forall_intro fun a =>
        SPred.and_intro (SPred.and_elim_l.trans (SPred.forall_elim a))
          (SPred.and_elim_r.trans (SPred.forall_elim a))

-- Fixing the requested type does not fix the answer: any value of the type is allowed, and a
-- verification has to hold for all of them.
/-- The answer may be any value of the requested type. -/
def choiceSpec {ps : PostShape} : (α : Type) → Choice α → PredTrans ps α
  | _, .pick _ => pickAny

/-- Executions keep the balance in the state of an arbitrary base monad. -/
abbrev Exec (n : Type → Type v) := StateT Nat n

/-- Verification adds uninterpreted choices on top of the balance. -/
abbrev Symbolic (n : Type → Type v) := FreerT Choice (Exec n)

variable {n : Type → Type v} {ps : PostShape} [Monad n] [WPMonad n ps]

/- The specification of a base request is that monad's own `wp`, so this single instance
gives the weakest precondition calculus of the whole stack. -/
local instance symbolicWP : WPMonad (Symbolic n) (.arg Nat ps) :=
  wpMonad (fun _ req => match req with
    | .inl op => choiceSpec _ op
    | .inr x => wp x)

-- The constraint on an answer lives in its type. This entry states it as a postcondition, the
-- form in which the verification-condition generator can use it.
/-- A choice from a subtype returns a value satisfying its predicate. -/
@[spec]
theorem pick_spec {α : Type} {p : α → Prop} :
    ⦃⌜True⌝⦄ (MonadChoice.pick : Symbolic n {x // p x}) ⦃⇓ a => ⌜p a⌝⦄ :=
  SPred.forall_intro fun a => SPred.pure_intro a.property

-- FIXME: Make this general advice, library-level
/- A lifted operation has three spellings, and they are not interchangeable.

* In a program whose monad is still a parameter, write `liftM`. Automatic lifting in `do`
  only fires when it can synthesise `MonadLiftT`; with the monad abstract it reports a type
  mismatch instead. The explicit call is also what leaves the instance for `infer_effects%`
  to abstract. At a monad with the instance in scope, `do` does insert the lift by itself.
* In a `@[spec]` lemma, write `MonadLift.monadLift`. Before matching a specification, the
  verification condition generator rewrites `liftM` and `MonadLiftT.monadLift` away, using
  `liftM`, `Spec.UnfoldLift.monadLift_trans` and `Spec.UnfoldLift.monadLift_refl`, which are
  tagged `@[spec]` themselves. A specification stated with either of the two never applies,
  and nothing reports this: the lemma still compiles, and only the proofs needing it fail.
* Elsewhere, use the operation of the class actually assumed.
-/

/- NOTE: Specifications are matched syntactically, so a transformer needs this entry even where it
holds by `rfl`: Std provides `Spec.monadLift_StateT` and its siblings for the transformers it
knows, and this is the one for `FreerT`. -/
/-- A base computation keeps its own weakest precondition. -/
@[spec]
theorem lift_spec {α : Type} (x : Exec n α) (Q : PostCond α (.arg Nat ps)) :
    ⦃wp⟦x⟧ Q⦄ (MonadLift.monadLift x : Symbolic n α) ⦃Q⦄ := .rfl

/-! ## Programs choosing within the balance -/

/-- Spend an amount chosen within the balance. -/
def spend := infer_effects% do
  let balance ← get
  let ⟨amount, _⟩ ← MonadChoice.pick (τ := {x : Nat // x ≤ balance})
  set (balance - amount)
  pure amount

derive_parametric spend

/-- Spend once per round, returning the total. -/
def spendRounds (rounds : Nat) := infer_effects% do
  let mut total := 0
  for _ in [0:rounds] do
    let balance ← get
    let ⟨amount, _⟩ ← MonadChoice.pick (τ := {x : Nat // x ≤ balance})
    set (balance - amount)
    total := total + amount
  pure total

derive_parametric spendRounds

-- The signature of a program records the types it chooses from, here one for each balance.
example : {m : Type → Type} → [Monad m] → [MonadStateOf Nat m] →
    [(balance : Nat) → MonadChoice {x : Nat // x ≤ balance} m] → m Nat := @spend

-- Reified, a program is a tree of requests, and its type is the same whatever types the
-- program chooses from.
example : spend (m := Symbolic Id) =
    .impure (.inr MonadStateOf.get) (fun balance =>
      .impure (.inl (.pick {x : Nat // x ≤ balance})) (fun amount =>
        .impure (.inr (set (balance - amount.val))) (fun _ => .pure amount.val))) := rfl

/-! ## Verification from the specification of choices -/

/- The proofs below fix the base monad, because the verification-condition generator
reduces an assertion of a concrete shape, whereas the relation below holds for any base
monad. No answer is chosen: the proofs cover every amount within the balance. -/
set_option mvcgen.warning false in
/-- Whatever amount is chosen, the balance decreases by the amount returned. -/
theorem spend_spec (initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spend (m := Symbolic Id)
      ⦃⇓ amount s => ⌜s + amount = initial⌝⦄ := by
  mvcgen [spend]
  all_goals (mleave; simp_all <;> omega)

set_option mvcgen.warning false in
/-- The rounds spend exactly the difference between the initial and the final balance. -/
theorem spendRounds_spec (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Symbolic Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ := by
  mvcgen [spendRounds] invariants
  | inv1 => ⇓ (_, total) s => ⌜s + total = initial⌝
  all_goals (mleave; simp_all +zetaDelta <;> omega)

-- Every amount within the balance is allowed, so no particular answer follows from the
-- specification alone.
example : ¬ (⦃fun s => ⌜s = 10⌝⦄ spend (m := Symbolic Id) ⦃⇓ amount _ => ⌜amount = 10⌝⦄) := by
  intro h
  have impossible := h 10 rfl ⟨0, Nat.zero_le _⟩
  cases impossible

/-! ## Relating the two instantiations -/

-- The reified program is not interpreted. An interpretation into `Exec Id` would answer every
-- request, and the request for a type without values has no answer.
example : ((τ : Type) → Choice τ → Exec Id τ) → False :=
  fun h => ((h Empty (.pick Empty)).run 0).run.1.elim

-- Parametricity relates the two instantiations along any relation that their operations
-- preserve. The relation chosen here is the conclusion wanted.
/-- The execution establishes every postcondition that the symbolic computation establishes. -/
def Refines : ComputationRelation (Symbolic n) (Exec n) :=
  fun {α} x y => ∀ Q : PostCond α (.arg Nat ps), wp⟦x⟧ Q ⊢ₛ wp⟦y⟧ Q

/- `Monad.Rel.ofPureBind` derives the fields for the other monad operations from those for
`pure` and `bind`, which needs both monads to be lawful. The case of `bind` holds because a
weakest precondition is monotone in its postcondition. -/
/-- The monad operations preserve the relation. -/
theorem refines_monad [LawfulMonad n] : Monad.Rel (Refines (n := n) (ps := ps)) :=
  Monad.Rel.ofPureBind _ (fun a Q => by simp only [WP.pure]; exact .rfl) (by
    intro α β x y f g hx hf Q
    simp only [WP.bind]
    exact ((wp x).mono (fun a => wp⟦f a⟧ Q, Q.2) (fun a => wp⟦g a⟧ Q, Q.2)
      ⟨fun a => hf a Q, .rfl⟩).trans (hx _))

-- The symbolic balance operations are those of the execution, lifted, and a lifted
-- computation keeps its weakest precondition, as in `lift_spec`.
/-- Both instantiations access the balance in the same way. -/
theorem refines_state : MonadStateOf.Rel (σ := Nat) (Refines (n := n) (ps := ps)) where
  get _ := .rfl
  set _ _ := .rfl
  modifyGet _ _ := .rfl

-- Every value is allowed, so the answer needs no condition of its own: the type of the choice
-- already constrains it.
/-- Answering a choice with a value, and doing nothing else, is related to the choice. -/
theorem refines_pure {τ : Type} (a : τ) :
    MonadChoice.Rel (right := ⟨pure a⟩) (Refines (n := n) (ps := ps)) :=
  .mk (left := (_)) (right := (_)) _ fun _ => by simp only [WP.pure]; exact SPred.forall_elim a

/-! ## Transferring the verification to executions -/

/- Neither proof unfolds the program: each composes the verification with the parametricity
theorem of the program, applied to `Refines`. Of its premises, only the one for choices depends
on the advisor, with one instance for each balance, as the program chooses from one type for
each balance. It cannot be dropped for an arbitrary advisor: a value of the right type may be
returned by a computation that also changes the balance, and that computation is not related
to the choice. -/
/-- The verified property holds of every execution whose choices are related. -/
theorem spend_correct [∀ k, MonadChoice {x : Nat // x ≤ k} (Exec Id)]
    (hsound : ∀ k, MonadChoice.Rel (τ := {x : Nat // x ≤ k}) (Refines (n := Id)))
    (initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spend (m := Exec Id) ⦃⇓ amount s => ⌜s + amount = initial⌝⦄ :=
  (spend_spec initial).trans (spend.parametric _ refines_monad refines_state hsound _)

/-- Every execution whose choices are related spends exactly the difference between the initial
and the final balance. -/
theorem spendRounds_correct [∀ k, MonadChoice {x : Nat // x ≤ k} (Exec Id)]
    (hsound : ∀ k, MonadChoice.Rel (τ := {x : Nat // x ≤ k}) (Refines (n := Id)))
    (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ :=
  (spendRounds_spec rounds initial).trans
    (spendRounds.parametric rounds _ refines_monad refines_state hsound _)

/-! ## Two executable advisors -/

-- An advisor has to produce an amount within the balance, as the type of the choice demands.
-- Both advisors below answer with `pure`, so `refines_pure` relates their choices, and the
-- proofs above apply to them unchanged.

section Half

/-- Choose half of the balance. -/
local instance (k : Nat) : MonadChoice {x : Nat // x ≤ k} (Exec Id) where
  pick := pure ⟨k / 2, Nat.div_le_self _ _⟩

example (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ :=
  spendRounds_correct (fun _ => refines_pure _) rounds initial

#guard ((spend (m := Exec Id)).run 10).run == (5, 5)
#guard ((spendRounds (m := Exec Id) 3).run 100).run == (87, 13)

end Half

section Greedy

/-- Choose the whole balance. -/
local instance (k : Nat) : MonadChoice {x : Nat // x ≤ k} (Exec Id) where
  pick := pure ⟨k, Nat.le_refl _⟩

example (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ :=
  spendRounds_correct (fun _ => refines_pure _) rounds initial

#guard ((spend (m := Exec Id)).run 10).run == (10, 0)
#guard ((spendRounds (m := Exec Id) 3).run 100).run == (100, 0)

end Greedy

/-! ## A choice no execution can make -/

-- A program choosing an amount strictly below the balance would have
-- `[(balance : Nat) → MonadChoice {x : Nat // x < balance} m]` in its signature. The symbolic
-- instantiation provides it, but `Exec Id` cannot: at a zero balance, there is no amount below.
example : (∀ k, MonadChoice {x : Nat // x < k} (Exec Id)) → False :=
  fun inst => nomatch ((inst 0).pick.run 0).run.1

#guard_uses spend_correct ⊇ [spend_spec, spend.parametric, refines_monad, refines_state]
#guard_uses spendRounds_correct ⊇ [spendRounds_spec, spendRounds.parametric, refines_monad,
  refines_state]
#guard_axioms spend.parametric ⊆ []
#guard_axioms pickAny, choiceSpec, pick_spec, lift_spec, spend_spec, spendRounds_spec,
  refines_monad, refines_state, refines_pure, spend_correct, spendRounds_correct,
  spendRounds.parametric ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Freer.Extraction
