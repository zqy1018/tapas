import Tapas

/-!
Interpret a logical key-value store using a finite
update journal. Only the capability interface and operation proofs are specific
to this representation; program proofs use the existing parametricity generator.
-/

namespace TapasTest.Applications.Monad.Store.Basic

open Tapas.Parametricity Tapas.LogicalRelation

class Store (m : Type → Type v) where
  fetch : String → m Nat
  store : String → Nat → m Unit
  /-- Run a computation, retaining its return value but restoring the initial store. -/
  sandbox : {α : Type} → m α → m α

derive_effect_rel Store

abbrev LogicalStore := String → Nat
abbrev Journal := List (String × Nat)

/-- Most recent writes shadow older ones; absent keys contain zero. -/
def decode : Journal → LogicalStore
  | [] => fun _ => 0
  | (key, value) :: rest => fun query => if query = key then value else decode rest query

abbrev Source := StateM LogicalStore
abbrev Target := StateM Journal

-- Both interpretations are registered, so a program instantiated at `Source` or
-- `Target` needs no dictionary written out, and `Store.Rel R` finds the pair `R`
-- relates. An interpretation that is deliberately wrong, as in `Programs.lean`, is
-- named at the use site instead.
instance sourceStore : Store Source where
  fetch key := fun state => (state key, state)
  store key value := fun state => ((), fun query => if query = key then value else state query)
  sandbox body := fun state => ((body state).1, state)

instance targetStore : Store Target where
  fetch key := fun journal => (decode journal key, journal)
  store key value := fun journal => ((), (key, value) :: journal)
  sandbox body := fun journal => ((body journal).1, journal)

/-- Preserve returned values and logical final stores for every represented initial store.
The target's journal layout and shadowed entries are intentionally unobservable. -/
def R : ComputationRelation Source Target := fun {_} source target =>
  ∀ journal, source (decode journal) = ((target journal).1, decode (target journal).2)

theorem pure_rel {α : Type} (a : α) : R (pure a) (pure a) := by
  intro journal
  rfl

theorem bind_rel {α β : Type} {x : Source α} {y : Target α}
    {f : α → Source β} {g : α → Target β}
    (hxy : R x y) (hfg : ∀ a, R (f a) (g a)) : R (x >>= f) (y >>= g) := by
  intro journal
  change f (x (decode journal)).1 (x (decode journal)).2 =
    ((g (y journal).1 (y journal).2).1, decode (g (y journal).1 (y journal).2).2)
  rw [hxy journal]
  exact hfg (y journal).1 (y journal).2

theorem monadRel : Monad.Rel R :=
  Monad.Rel.ofPureBind R pure_rel bind_rel

theorem storeRel : Store.Rel (left := sourceStore) (right := targetStore) R :=
  Store.Rel.mk R
    (fetch := by intro key journal; rfl)
    (store := by intro key value journal; rfl)
    (sandbox := by
      intro α source target h journal
      change ((source (decode journal)).1, decode journal) = ((target journal).1, decode journal)
      rw [h journal])

/-- The certificate gives a semantic statement without exposing journal representation to the program. -/
theorem run_eq {α : Type} {source : Source α} {target : Target α}
    (h : R source target) (journal : Journal) :
    source (decode journal) = ((target journal).1, decode (target journal).2) :=
  h journal

end TapasTest.Applications.Monad.Store.Basic
