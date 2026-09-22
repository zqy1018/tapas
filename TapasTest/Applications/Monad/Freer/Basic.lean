module

public import Tapas

public section

/-!
Freer syntax, its final encoding, and interpretation laws. Requests are first-order;
continuations are Lean functions, and this inductive representation does not model
divergence.
-/

namespace TapasTest.Applications.Monad.Freer.Basic

open Tapas.Parametricity Tapas.LogicalRelation

universe u v w w'

-- Reified requests and their continuations. No Functor instance for E is needed.
inductive Freer (E : Type u → Type v) (α : Type u) : Type (max (u + 1) v) where
  | pure : α → Freer E α
  | impure {β : Type u} : E β → (β → Freer E α) → Freer E α

namespace Freer

variable {E : Type u → Type v} {α β γ : Type u}

@[expose] def bind (t : Freer E α) (f : α → Freer E β) : Freer E β :=
  match t with
  | .pure a => f a
  | .impure op k => .impure op (fun x => bind (k x) f)

instance : Monad (Freer E) where
  pure := .pure
  bind := bind

theorem bind_pure (t : Freer E α) : bind t .pure = t := by
  induction t with
  | pure a => rfl
  | impure op k ih => simp only [bind]; exact congrArg (impure op) (funext ih)

theorem assoc (t : Freer E α) (f : α → Freer E β) (g : β → Freer E γ) :
    bind (bind t f) g = bind t (fun a => bind (f a) g) := by
  induction t with
  | pure a => rfl
  | impure op k ih => simp only [bind]; exact congrArg (impure op) (funext ih)

instance : LawfulMonad (Freer E) :=
  LawfulMonad.mk' _ (fun x => bind_pure x) (fun _ _ => rfl) assoc

instance : MonadLift E (Freer E) where
  monadLift op := .impure op .pure

@[expose] def fold {m : Type u → Type w} [Monad m]
    (h : (β : Type u) → E β → m β) (t : Freer E α) : m α :=
  match t with
  | .pure a => Pure.pure a
  | .impure op k => h _ op >>= fun x => fold h (k x)

-- `fold.parametric` says that folding the same syntax tree with two handlers gives
-- related computations whenever the handlers map each request to related computations
-- and the relation preserves the monad operations.
derive_parametric fold (repr := m)

theorem fold_monadLift {m : Type u → Type w} [Monad m] [LawfulMonad m]
    (h : (β : Type u) → E β → m β) (op : E α) : fold h (monadLift op) = h _ op := by
  change (h _ op >>= fun x => Pure.pure x) = h _ op
  simp

theorem fold_bind {m : Type u → Type w} [Monad m] [LawfulMonad m]
    (h : (β : Type u) → E β → m β) (t : Freer E α) (f : α → Freer E β) :
    fold h (bind t f) = fold h t >>= fun a => fold h (f a) := by
  induction t with
  | pure a => simp [fold, bind]
  | impure op k ih => simp only [fold, bind, ih, bind_assoc]

theorem fold_self (t : Freer E α) : fold (m := Freer E) (fun _ => monadLift) t = t := by
  induction t with
  | pure a => rfl
  | impure op k ih =>
    change impure op (fun x => fold (fun _ => monadLift) (k x)) = impure op k
    exact congrArg (impure op) (funext ih)

end Freer

-- A final program accepts an interpretation of every request.
abbrev Final (E : Type u → Type v) (α : Type u) :=
  {m : Type u → Type w} → [Monad m] → ((β : Type u) → E β → m β) → m α

-- Relational parametricity between two final programs, read off the type of `Final`: it
-- quantifies over all computation relations that preserve the monad operations, and requires
-- the handlers to map each request to related computations. The two programs may use different
-- computation universes, so `Final.Rel` also relates two universe instances of the same
-- declaration, as reification and execution need; `Final.Rel p p` is the same-universe case.
derive_type_rel Final (repr := m)

@[expose] def toFinal {E : Type u → Type v} {α : Type u} (t : Freer E α) :
    Final.{u, v, w} E α := fun {m} _ h => Freer.fold (m := m) h t

-- `toFinal.parametric` uses `Freer.fold.parametric` to show that every syntax tree
-- gives a final encoding related to itself by `Final.Rel`, even across different
-- computation universes. `toFinal_rel` below states this result explicitly.
derive_parametric toFinal (repr := m)

/-- Every reified program gives related final interpretations. -/
theorem toFinal_rel {E : Type u → Type v} {α : Type u} (t : Freer E α) :
    Final.Rel (toFinal.{u, v, w} t) (toFinal.{u, v, w'} t) :=
  toFinal.parametric t

-- Reification needs an output universe large enough to instantiate m := Freer E.
@[expose] def toFreer {E : Type u → Type v} {α : Type u}
    (p : Final.{u, v, max (u + 1) v} E α) : Freer E α :=
  p (m := Freer E) (fun _ => monadLift)

theorem toFreer_toFinal {E : Type u → Type v} {α : Type u} (t : Freer E α) :
    toFreer (toFinal t) = t := Freer.fold_self t

-- Interpreting syntax gives a relation preserved by the monad operations.
@[expose] def graph {E : Type u → Type v} {m : Type u → Type w} [Monad m]
    (h : (β : Type u) → E β → m β) : ComputationRelation (Freer E) m :=
  fun {_} t x => Freer.fold h t = x

theorem graph_monad {E : Type u → Type v} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] (h : (β : Type u) → E β → m β) :
    Monad.Rel (graph h) :=
  Monad.Rel.ofPureBind (m := Freer E) (n := m) (graph h) (fun _ => rfl) (by
    intro α β x y f g hx hf
    change Freer.fold h (Freer.bind x f) = y >>= g
    rw [Freer.fold_bind, hx]
    exact congrArg (fun k => y >>= k) (funext hf))

/--
Reify `p` and interpret it in any lawful target monad. A relational parametricity
certificate identifies the result with `q`, which may be the same declaration at
a different computation universe. This is pointwise equality in lawful monads;
the raw `Final` type also admits unlawful dictionaries.
-/
theorem toFinal_toFreer_rel {E : Type u → Type v} {α : Type u}
    (p : Final.{u, v, max (u + 1) v} E α) (q : Final.{u, v, w} E α)
    (hpq : Final.Rel p q) {m : Type u → Type w} [Monad m] [LawfulMonad m]
    (h : (β : Type u) → E β → m β) :
    toFinal (toFreer p) h = q h :=
  hpq (m := Freer E) (m' := m) (graph h) (graph_monad h)
    (fun _ => monadLift) h (fun _ op => Freer.fold_monadLift h op)

/-- Reifying a self-related final program preserves its interpretation in any lawful monad. -/
theorem toFinal_toFreer {E : Type u → Type v} {α : Type u}
    (p : Final.{u, v, max (u + 1) v} E α) (hp : Final.Rel p p)
    {m : Type u → Type (max (u + 1) v)} [Monad m] [LawfulMonad m] :
    toFinal (toFreer p) (m := m) = p (m := m) := by
  funext h
  exact toFinal_toFreer_rel p p hp h

end TapasTest.Applications.Monad.Freer.Basic
