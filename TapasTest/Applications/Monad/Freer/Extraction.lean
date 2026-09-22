import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Freer.WP
import Std.Tactic.Do

/-!
One program, two instantiations. Uninterpreted operations are reified on top of a base
monad, so that a verification uses their specifications, while an execution interprets
them. Parametricity identifies the two instantiations, so the proved postcondition
transfers to the execution without revisiting the program.
-/

namespace TapasTest.Applications.Monad.Freer.Extraction

open Std.Do Tapas.Parametricity Tapas.LogicalRelation
open TapasTest.Applications.Monad.Freer.Basic
open TapasTest.Applications.Monad.Freer.WP (wpMonad fold_sound)

universe u v w

/-- Uninterpreted operations of `E`, interleaved with computations of `m`. -/
abbrev FreerT (E : Type u → Type v) (m : Type u → Type w) :=
  Freer (fun β => PSum (E β) (m β))

instance {E : Type u → Type v} {m : Type u → Type w} : MonadLift m (FreerT E m) where
  monadLift x := .impure (.inr x) .pure

instance {E : Type u → Type v} {m : Type u → Type w} : MonadLift E (FreerT E m) where
  monadLift op := .impure (.inl op) .pure

/-- Read an operation handler as an interpretation of every request. -/
def interpret {E : Type u → Type v} {m : Type u → Type w}
    (handler : (β : Type u) → E β → m β) : (β : Type u) → PSum (E β) (m β) → m β
  | _, .inl op => handler _ op
  | _, .inr x => x

/-- Demonic choice: the postcondition must hold for every permitted answer. -/
def pickDemonic {ps : PostShape.{u}} {α : Type u} (p : α → Prop) : PredTrans ps α where
  trans Q := spred(∀ (a : {x : α // p x}), Q.1 a.1)
  conjunctiveRaw := by
    intro Q₁ Q₂
    refine SPred.bientails.iff.mpr ⟨?_, ?_⟩
    · exact SPred.and_intro (SPred.forall_mono fun _ => SPred.and_elim_l)
        (SPred.forall_mono fun _ => SPred.and_elim_r)
    · exact SPred.forall_intro fun a =>
        SPred.and_intro (SPred.and_elim_l.trans (SPred.forall_elim a))
          (SPred.and_elim_r.trans (SPred.forall_elim a))

/-! ## An uninterpreted effect and the programs using it -/

/-- A request for an amount to spend, not exceeding the given balance. -/
inductive Advice : Type → Type where
  | suggest : Nat → Advice Nat

-- Fixing the request syntax does not fix the answer: any amount within the balance is
-- allowed, and a verification has to hold for all of them.
/-- The answer may be any value within the requested bound. -/
def adviceSpec {ps : PostShape} : (α : Type) → Advice α → PredTrans ps α
  | _, .suggest bound => pickDemonic (fun amount => amount ≤ bound)

/-- Executions keep the balance in the state of an arbitrary base monad. -/
abbrev Exec (n : Type → Type v) := StateT Nat n

/-- Verification adds uninterpreted advice on top of the balance. -/
abbrev Symbolic (n : Type → Type v) := FreerT Advice (Exec n)

variable {n : Type → Type v} {ps : PostShape} [Monad n] [WPMonad n ps]

/- The specification of a base request is that monad's own `wp`, so this single instance
gives the weakest precondition calculus of the whole stack. -/
local instance symbolicWP : WPMonad (Symbolic n) (.arg Nat ps) :=
  wpMonad (fun _ req => match req with
    | .inl op => adviceSpec _ op
    | .inr x => wp x)

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
* Elsewhere, use the operation of the class actually assumed, as `handler` does below with
  `MonadLiftT`.
-/

/-- A suggestion returns an amount within the requested bound. -/
@[spec]
theorem suggest_spec (bound : Nat) :
    ⦃⌜True⌝⦄ (MonadLift.monadLift (Advice.suggest bound) : Symbolic n Nat)
      ⦃⇓ amount => ⌜amount ≤ bound⌝⦄ :=
  SPred.forall_intro fun amount => SPred.pure_intro amount.2

/- NOTE: Specifications are matched syntactically, so a transformer needs this entry even where it
holds by `rfl`: Std provides `Spec.monadLift_StateT` and its siblings for the transformers it
knows, and this is the one for `FreerT`. -/
/-- A base computation keeps its own weakest precondition. -/
@[spec]
theorem lift_spec {α : Type} (x : Exec n α) (Q : PostCond α (.arg Nat ps)) :
    ⦃wp⟦x⟧ Q⦄ (MonadLift.monadLift x : Symbolic n α) ⦃Q⦄ := .rfl

/-- Spend an amount chosen by the advisor. -/
def spend := infer_effects% do
  let balance ← get
  let amount ← liftM (Advice.suggest balance)
  set (balance - amount)
  pure amount

derive_parametric spend

/-- Spend once per round, returning the total. -/
def spendRounds (rounds : Nat) := infer_effects% do
  let mut total := 0
  for _ in [0:rounds] do
    let balance ← get
    let amount ← liftM (Advice.suggest balance)
    set (balance - amount)
    total := total + amount
  pure total

derive_parametric spendRounds

example : spend (m := Symbolic Id) =
    .impure (.inr MonadStateOf.get) (fun balance =>
      .impure (.inl (.suggest balance)) (fun amount =>
        .impure (.inr (set (balance - amount))) (fun _ => .pure amount))) := rfl

/-! ## Interpreting the requests -/

/-- Requests are executed by the lifting capability of the executable monad. -/
def handler (n : Type → Type v) [Monad n] [MonadLiftT Advice (Exec n)] :
    (α : Type) → Advice α → Exec n α := fun _ op => monadLift op

/-- An interpretation is sound when its answers satisfy the specification of each request. -/
abbrev Sound (n : Type → Type v) [Monad n] {ps : PostShape} [WPMonad n ps]
    [MonadLiftT Advice (Exec n)] : Prop :=
  ∀ α (op : Advice α) (Q : PostCond α (.arg Nat ps)),
    (adviceSpec α op).apply Q ⊢ₛ wp⟦handler n α op⟧ Q

section Execution

variable [MonadLiftT Advice (Exec n)]

/-- Interpreting requests preserves every postcondition proved from their specifications. -/
theorem interpret_sound (hsound : Sound (ps := ps) n)
    {α : Type} (tree : Symbolic n α) (Q : PostCond α (.arg Nat ps)) :
    wp⟦tree⟧ Q ⊢ₛ wp⟦Freer.fold (interpret (handler n)) tree⟧ Q := by
  refine fold_sound _ (interpret (handler n)) ?_ tree Q
  intro α req Q
  cases req with
  | inl op => exact hsound α op Q
  | inr x => exact .rfl

variable [LawfulMonad n]

theorem state_rel : MonadStateOf.Rel (σ := Nat) (graph (interpret (handler n))) :=
  MonadStateOf.Rel.mk _
    (Freer.fold_monadLift (interpret (handler n)) (.inr MonadStateOf.get))
    (fun s => Freer.fold_monadLift (interpret (handler n)) (.inr (set s)))
    (fun f => Freer.fold_monadLift (interpret (handler n)) (.inr (MonadStateOf.modifyGet f)))

theorem advice_rel : MonadLiftT.Rel (m := Advice) (graph (interpret (handler n))) :=
  MonadLiftT.Rel.mk _ (fun op => Freer.fold_monadLift (interpret (handler n)) (.inl op))

-- The reified program and the executed one are two instantiations of the same definition,
-- in different computation universes. Their parametricity theorem identifies them, for
-- every base monad and every interpretation.
/-- Interpreting the reified program gives the program run by the executable monad. -/
theorem spend_extracted :
    Freer.fold (interpret (handler n)) (spend (m := Symbolic n)) = spend (m := Exec n) :=
  spend.parametric _ (graph_monad _) state_rel advice_rel

theorem spendRounds_extracted (rounds : Nat) :
    Freer.fold (interpret (handler n)) (spendRounds (m := Symbolic n) rounds) =
      spendRounds (m := Exec n) rounds :=
  spendRounds.parametric rounds _ (graph_monad _) state_rel advice_rel

end Execution

/-! ## Verification against the operation specifications -/

/- The proofs below fix the base monad, because the verification-condition generator
reduces an assertion of a concrete shape, whereas the results above hold for any base
monad. No executable handler is chosen: the proofs use the specification of `suggest`,
and the balance is the state of the base monad. -/
set_option mvcgen.warning false in
/-- Whatever the advisor suggests, the balance decreases by the amount returned. -/
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

-- Every answer within the bound is allowed, so no advisor's own behaviour follows from
-- the specification alone.
example : ¬ (⦃fun s => ⌜s = 10⌝⦄ spend (m := Symbolic Id) ⦃⇓ amount _ => ⌜amount = 10⌝⦄) := by
  intro h
  have impossible := h 10 rfl ⟨0, Nat.zero_le _⟩
  cases impossible

-- Neither proof unfolds the program: they compose its symbolic verification with the
-- soundness of the chosen interpretation.
/-- The verified property holds of the execution under any sound interpretation. -/
theorem spend_correct [MonadLiftT Advice (Exec Id)] (hsound : Sound Id) (initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spend (m := Exec Id) ⦃⇓ amount s => ⌜s + amount = initial⌝⦄ := by
  rw [← spend_extracted]
  exact (spend_spec initial).trans (interpret_sound hsound _ _)

theorem spendRounds_correct [MonadLiftT Advice (Exec Id)] (hsound : Sound Id)
    (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ := by
  rw [← spendRounds_extracted]
  exact (spendRounds_spec rounds initial).trans (interpret_sound hsound _ _)

/-! ## Two executable advisors -/

section Half

/-- Suggest half of the balance. -/
local instance : MonadLift Advice (Exec Id) where
  monadLift | .suggest bound => pure (bound / 2)

theorem half_sound : Sound Id := by
  rintro α ⟨bound⟩ Q s h
  exact h ⟨bound / 2, Nat.div_le_self _ _⟩

example (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ :=
  spendRounds_correct half_sound rounds initial

#guard ((spend (m := Exec Id)).run 10).run == (5, 5)
#guard ((spendRounds (m := Exec Id) 3).run 100).run == (87, 13)

end Half

section Greedy

/-- Suggest the whole balance. -/
local instance : MonadLift Advice (Exec Id) where
  monadLift | .suggest bound => pure bound

theorem greedy_sound : Sound Id := by
  rintro α ⟨bound⟩ Q s h
  exact h ⟨bound, Nat.le_refl _⟩

example (rounds initial : Nat) :
    ⦃fun s => ⌜s = initial⌝⦄ spendRounds (m := Exec Id) rounds
      ⦃⇓ total s => ⌜s + total = initial⌝⦄ :=
  spendRounds_correct greedy_sound rounds initial

#guard ((spend (m := Exec Id)).run 10).run == (10, 0)
#guard ((spendRounds (m := Exec Id) 3).run 100).run == (100, 0)

end Greedy

#guard_uses spend_correct ⊇ [spend_spec, spend_extracted, interpret_sound]
#guard_uses spendRounds_correct ⊇ [spendRounds_spec, spendRounds_extracted, interpret_sound]
#guard_uses spend_extracted ⊇ [spend.parametric, graph_monad]
#guard_axioms spend.parametric ⊆ []
#guard_axioms pickDemonic, adviceSpec, suggest_spec, lift_spec, spend_spec, spendRounds_spec,
  interpret_sound, state_rel, advice_rel, spend_extracted, spendRounds_extracted,
  spend_correct, spendRounds_correct, half_sound, greedy_sound, spendRounds.parametric
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Freer.Extraction
