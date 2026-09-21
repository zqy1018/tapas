import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Store.Basic

open Tapas.Parametricity Tapas.LogicalRelation TapasTest.Applications.Monad.Store.Basic

namespace TapasTest.Applications.Monad.Store.Programs

def increment (key : String) (amount : Nat) := infer_effects% do
  let old ← Store.fetch key
  Store.store key (old + amount)
  pure (old + amount)

derive_parametric increment

-- The helper's generated translation is reused both inside and outside sandbox.
def transfer (amount : Nat) := infer_effects% do
  let balance ← Store.fetch "balance"
  let fee ← Store.fetch "fee"
  if amount + fee ≤ balance then
    let preview ← Store.sandbox do
      Store.store "balance" (balance - amount - fee)
      let received ← increment "received" amount
      let remaining ← Store.fetch "balance"
      pure (remaining, received)
    Store.store "balance" preview.1
    let received ← increment "received" amount
    Store.store "fee" (fee + 1)
    pure (some (preview.1, received))
  else
    pure none

derive_parametric transfer

-- Check the full generated interface: no representation-specific hypothesis is added.
example (amount : Nat) {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] [Store m] [Store n]
    (relation : ComputationRelation m n) (hm : Monad.Rel relation)
    (hs : Store.Rel relation) :
    relation (transfer (m := m) amount) (transfer (m := n) amount) :=
  transfer.parametric amount relation hm hs

def executable (amount : Nat) : Target (Option (Nat × Nat)) := transfer (m := Target) amount

theorem certificate (amount : Nat) : R (transfer (m := Source) amount) (executable amount) :=
  transfer.parametric amount R monadRel storeRel

-- Universal correctness, retaining the original source program in the statement.
theorem transfer_correct (amount : Nat) (journal : Journal) :
    transfer (m := Source) amount (decode journal) =
      ((executable amount journal).1, decode (executable amount journal).2) :=
  run_eq (certificate amount) journal

def initial : Journal :=
  [("balance", 20), ("received", 3), ("fee", 2), ("balance", 999)]

-- Shadowed values are retained physically; sandbox's temporary writes are absent.
def expected : Option (Nat × Nat) × Journal :=
  (some (13, 8), [("fee", 3), ("received", 8), ("balance", 13)] ++ initial)

theorem successful_transfer : executable 5 initial = expected := rfl
#guard (executable 5 initial).run == expected

theorem rejected_transfer : executable 30 initial = (none, initial) := rfl
#guard (executable 30 initial).run == (none, initial)

-- Missing keys read zero; a second successful call uses the updated fee and balance.
example : executable 1 [] = (none, []) := rfl
example : executable 0 [] =
    (some (0, 0), [("fee", 1), ("received", 0), ("balance", 0)]) := rfl
example : executable 4 expected.2 =
    (some (6, 12), [("fee", 4), ("received", 12), ("balance", 6)] ++ expected.2) := rfl

-- Nested higher-order operations restore their own initial stores, even on an existing key.
def nestedSandbox := infer_effects% do
  Store.sandbox do
    Store.store "balance" 100
    let inner ← Store.sandbox do
      Store.store "balance" 200
      Store.fetch "balance"
    let outer ← Store.fetch "balance"
    pure (inner, outer)

derive_parametric nestedSandbox

def sandboxExecutable : Target (Nat × Nat) := nestedSandbox (m := Target)

theorem sandboxCertificate : R (nestedSandbox (m := Source)) sandboxExecutable :=
  nestedSandbox.parametric R monadRel storeRel

example : sandboxExecutable initial = ((200, 100), initial) := rfl
#guard (sandboxExecutable initial).run == ((200, 100), initial)

-- The relation does not impose a unique target representation of a source computation.
def redundantWrite : Target Nat := fun journal =>
  (7, ("scratch", decode journal "scratch") :: journal)

theorem redundant_write_related : R (pure 7) redundantWrite := by
  intro journal
  apply Prod.ext
  · rfl
  · funext key
    change decode journal key =
      if key = "scratch" then decode journal "scratch" else decode journal key
    split <;> simp_all

example : (pure 7 : Target Nat) [] ≠ redundantWrite [] := by
  change (7, ([] : Journal)) ≠ (7, [("scratch", 0)])
  decide
example : R (pure 7) (pure 7) := pure_rel 7

-- A target interpretation that omits restoration cannot satisfy Store.Rel.
abbrev badTargetStore : Store Target := { targetStore with sandbox := fun body => body }

theorem bad_sandbox_not_related :
    ¬ Store.Rel (left := sourceStore) (right := badTargetStore) R := by
  intro h
  have hs := h.sandbox (sourceStore.store "x" 1) (badTargetStore.store "x" 1) (h.store "x" 1)
  have impossible := congrArg (fun result => result.2 "x") (hs [])
  change 0 = 1 at impossible
  cases impossible

-- The helper's translation is registered, and reused both inside the sandbox and outside it.
#guard_parametric increment
#guard_uses transfer.parametric ⊇ [increment.parametric]
#guard_uses certificate ⊇ [transfer.parametric]
#guard_uses sandboxCertificate ⊇ [nestedSandbox.parametric]

#guard_axioms Store.Rel.fetch, Store.Rel.store, Store.Rel.sandbox, pure_rel, bind_rel,
  monadRel, storeRel, run_eq, increment.parametric, transfer.parametric, certificate,
  transfer_correct, nestedSandbox.parametric, sandboxCertificate, redundant_write_related,
  bad_sandbox_not_related ⊆ [propext, Classical.choice, Quot.sound]

-- The generated theorem, in full: one relation, one premise per interface, and the two
-- interpretations may live in different universes.
/--
info: TapasTest.Applications.Monad.Store.Programs.transfer.parametric.{u_1, u_1_target} (amount : Nat) {m : Type → Type u_1}
  {m' : Type → Type u_1_target} (R : ⦃x : Type⦄ → m x → m' x → Prop) [instMonad : Monad m] [instMonad' : Monad m']
  (instMonad_rel : Monad.Rel R) [effect0 : Store m] [effect0' : Store m'] (effect0_rel : Store.Rel R) :
  R (transfer amount) (transfer amount)
-/
#guard_msgs in
#check transfer.parametric

#guard_axioms transfer.parametric ⊆ []
#guard_axioms certificate, transfer_correct ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Store.Programs
