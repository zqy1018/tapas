import TapasTest.TestingUtils

open Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.EffectRelation

universe u v w q

/- Every state operation uses the actual dictionaries and shares pure arguments. -/
example {σ : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) [left : MonadStateOf σ m] [right : MonadStateOf σ n]
    (h : MonadStateOf.Rel (σ := σ) R) (s : σ) {α : Type u} (f : σ → α × σ) :
    R left.get right.get ∧ R (left.set s) (right.set s) ∧
      R (left.modifyGet f) (right.modifyGet f) :=
  ⟨h.get, h.set s, h.modifyGet f⟩

/- Exception universes are independent of value and computation universes. -/
example {ε : Type q} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) [left : MonadExceptOf ε m] [right : MonadExceptOf ε n]
    (h : MonadExceptOf.Rel (ε := ε) R) {α : Type u}
    (x : m α) (y : n α) (k : ε → m α) (k' : ε → n α)
    (hxy : R x y) (hk : ∀ e, R (k e) (k' e)) :
    R (left.tryCatch x k) (right.tryCatch y k') :=
  h.tryCatch x y hxy k k' hk

example {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n)
    [left : MonadWithReaderOf ρ m] [right : MonadWithReaderOf ρ n]
    (h : MonadWithReaderOf.Rel (ρ := ρ) R) {α : Type u}
    (f : ρ → ρ) (x : m α) (y : n α) (hxy : R x y) :
    R (left.withReader f x) (right.withReader f y) :=
  h.withReader f x y hxy

/- The base monad of a lift stays fixed; only its target is translated. -/
example {base : Type u → Type q} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) [left : MonadLiftT base m] [right : MonadLiftT base n]
    (h : MonadLiftT.Rel (m := base) R) {α : Type u} (x : base α) :
    R (left.monadLift x) (right.monadLift x) :=
  h.monadLift x

class Emit (ω : Type u) (m : Type u → Type v) where
  emit : ω → m PUnit

class ScopedEmit (ω : Type u) (m : Type u → Type v) extends Emit ω m where
  scope {α : Type u} : m α → (ω → m α) → m α

derive_effect_rel ScopedEmit

/- Inherited operations and user-defined higher-order operations use the same generator. -/
example {ω : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) [left : ScopedEmit ω m] [right : ScopedEmit ω n]
    (h : ScopedEmit.Rel (ω := ω) R) (a : ω) : R (left.emit a) (right.emit a) :=
  h.emit a

example {ω : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) [left : ScopedEmit ω m] [right : ScopedEmit ω n]
    (h : ScopedEmit.Rel (ω := ω) R) {α : Type u}
    (x : m α) (y : n α) (k : ω → m α) (k' : ω → n α)
    (hxy : R x y) (hk : ∀ a, R (k a) (k' a)) :
    R (left.scope x k) (right.scope y k') :=
  h.scope x y hxy k k' hk

/- Aliases can hide the monad's kind, an operation's binders, and handler computations. -/
set_option linter.checkUnivs false in
abbrev EffectConstructor := Type u → Type v
abbrev Action (m : EffectConstructor.{u, v}) (α : Type u) := m α
abbrev Handler (m : EffectConstructor.{u, v}) (α β : Type u) := α → Action m β
abbrev ScopeOperation (m : EffectConstructor.{u, v}) :=
  {α : Type u} → Action m α → Handler m α α → Action m α

class AliasedScope (m : outParam EffectConstructor.{u, v}) where
  scope : ScopeOperation m

derive_effect_rel AliasedScope

example {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) (left : AliasedScope m) (right : AliasedScope n)
    (h : AliasedScope.Rel (left := left) (right := right) R) {α : Type u}
    (x : m α) (y : n α) (k : α → m α) (k' : α → n α)
    (hxy : R x y) (hk : ∀ a, R (k a) (k' a)) :
    R (left.scope x k) (right.scope y k') :=
  h.scope x y hxy k k' hk

class Choose {α : Type u} (p : α → Prop) (m : Type u → Type v) where
  choose : m α

derive_effect_rel Choose

/- Predicate-indexed capabilities, implicit parameters, and pointwise dictionaries. -/
example {α : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) (p : Nat → α → Prop)
    (left : ∀ x, Choose (p x) m) (right : ∀ x, Choose (p x) n)
    (h : ∀ x, Choose.Rel (left := left x) (right := right x) R) (x : Nat) :
    R (left x).choose (right x).choose :=
  (h x).choose

def choiceFamilyRelation {α : Type u} {m : Type u → Type v} {n : Type u → Type w}
    (R : ComputationRelation m n) (p : Nat → α → Prop)
    (left : ∀ x, Choose (p x) m) (right : ∀ x, Choose (p x) n) : Prop :=
  ∀ x, Choose.Rel (left := left x) (right := right x) R

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let info ← getConstInfoDefn ``choiceFamilyRelation
  lambdaTelescope info.value fun args expected => do
    let #[_, m, n, rel, _, left, right] := args
      | throwError "unexpected test telescope"
    let actual ← relationAt #[⟨m, n, rel⟩] left right .marked
    unless ← isDefEq actual expected do
      throwError "capability-family relation differs from its expected type: {actual}"

/- The generated class can be constructed with ordinary structure syntax. -/
example {σ : Type u} {m : Type u → Type v} (inst : MonadStateOf σ m) :
    MonadStateOf.Rel (left := inst) (right := inst) (fun {_} x y => x = y) where
  get := rfl
  set _ := rfl
  modifyGet _ := rfl

abbrev firstReader : MonadReaderOf Nat Id where read := 1
abbrev secondReader : MonadReaderOf Nat Id where read := 2

/- Being instances of the same capability does not make dictionaries related. -/
example : ¬ MonadReaderOf.Rel (left := firstReader) (right := secondReader)
    (fun {_} x y => x = y) := by
  intro h
  have bad := h.read
  change (1 : Nat) = 2 at bad
  cases bad

/- A concrete graph relation exercises the complete Monad builder. -/
theorem idToOption : Monad.Rel (fun {α} (x : Id α) (y : Option α) => some x.run = y) := by
  apply Monad.Rel.ofPureBind
  · intro α a
    rfl
  · intro α β x y f g h hf
    cases h
    exact hf x

example {α β : Type} (f : Id (α → β)) (x : Unit → Id α) :
    some (Seq.seq f x).run = Seq.seq (some f.run) (fun u => some (x u).run) := by
  exact idToOption.seq f (some f.run) rfl x (fun u => some (x u).run) (fun _ => rfl)

/- Overriding an applicative method is visible even when pure and bind agree. -/
abbrev dropsMapConst : Monad Option :=
  { (inferInstance : Monad Option) with mapConst := fun _ _ => none }

example : ¬ Monad.Rel (right := dropsMapConst) (fun {α : Type} (x y : Option α) => x = y) := by
  intro h
  have bad := h.mapConst (α := Unit) (β := Unit) () (some ()) (some ()) rfl
  change some () = (none : Option Unit) at bad
  cases bad

class FixedReader (m : Type → Type) where
  read : m Nat

derive_effect_rel FixedReader

example {m n : Type → Type} (R : ComputationRelation m n)
    [left : FixedReader m] [right : FixedReader n] (h : FixedReader.Rel R) :
    R left.read right.read := by
  cases h with
  | mk related => exact related

class SharedUniverse (σ : Type v) (m : Type u → Type v) where
  send {α : Type u} : σ → α → m α

derive_effect_rel SharedUniverse

example {σ : Type v} {m n : Type u → Type v} (R : ComputationRelation m n)
    [left : SharedUniverse σ m] [right : SharedUniverse σ n]
    (h : SharedUniverse.Rel (σ := σ) R) (s : σ) {α : Type u} (x : α) :
    R (left.send s x) (right.send s x) := h.send s x

/- Missing type support must fail before any relation declaration is installed. -/
class Nested (m : Type → Type) where
  operations : Array (m Nat)

/--
error: while deriving TapasTest.Applications.Monad.EffectRelation.Nested.Rel.operations:
logical relation: unsupported representation-dependent type:
Array (m Nat)
register a relator for Array with `@[relator]`
or, if it is an interface, generate its relation with `derive_interface_rel Array (repr := ...)`
-/
#guard_msgs in
derive_effect_rel Nested

class Associated (m : Type → Type) where
  Carrier : Type
  run : Carrier → m Nat

/--
error: while deriving TapasTest.Applications.Monad.EffectRelation.Associated.Rel.Carrier:
logical relation: associated type fields are unsupported
-/
#guard_msgs in
derive_effect_rel Associated

class Dependent (m : Type → Type) where
  run : (x : m Nat) → (x = x) → m Nat

/--
error: while deriving TapasTest.Applications.Monad.EffectRelation.Dependent.Rel.run:
logical relation: dependent representation arguments are unsupported
-/
#guard_msgs in
derive_effect_rel Dependent

/-- error: logical relation: select exactly one monad parameter with `(monad := name)` -/
#guard_msgs in
derive_effect_rel MonadLift

derive_effect_rel MonadLift (monad := n)

/-- error: logical relation: declaration already exists: TapasTest.Applications.Monad.EffectRelation.Choose.Rel -/
#guard_msgs in
derive_effect_rel Choose

/- A projection collision happens after the relation's inductive declaration was added. -/
class Collision (m : Type → Type) where
  run : m Nat

def Collision.Rel.run : Nat := 42

/-- error: (kernel) constant has already been declared 'TapasTest.Applications.Monad.EffectRelation.Collision.Rel.run' -/
#guard_msgs in
derive_effect_rel Collision

/- The relators of `LogicalRelation.Relators` lift the computation relation through containers
of computations. -/
class Batch (m : Type u → Type v) where
  first? {α : Type u} : List (m α) → Option (m α)
  handlers : List (Nat → m PUnit)
  split {α : Type u} : Sum Nat (m α) → m α
  pending {α : Type u} : Option (List (m α))
  tagged {α : Type u} : m α → Nat × m α

derive_effect_rel Batch

/- Relators apply in argument and result positions, to handlers, nested containers, and
arguments free of the monad (`Sum.LiftRel Eq R`), also when the computation universe varies. -/
example {m : Type u → Type v} {n : Type u → Type w} (R : ComputationRelation m n)
    [left : Batch m] [right : Batch n] (h : Batch.Rel R) {α : Type u}
    (x : m α) (y : n α) (hxy : R x y) :
    Option.Rel (R (α := α)) (left.first? [x]) (right.first? [y]) ∧
      ListRel (fun f g => ∀ i, R (f i) (g i)) left.handlers right.handlers ∧
      R (left.split (.inr x)) (right.split (.inr y)) ∧
      Option.Rel (ListRel (R (α := α))) (left.pending (α := α)) (right.pending (α := α)) ∧
      (left.tagged x).1 = (right.tagged y).1 ∧ R (left.tagged x).2 (right.tagged y).2 :=
  ⟨h.first? [x] [y] (.cons hxy .nil), h.handlers, h.split (.inr x) (.inr y) (.inr hxy), h.pending,
    (h.tagged x y hxy).fst, (h.tagged x y hxy).snd⟩

inductive ExceptRel {ε : Type u} {α : Type v} {β : Type w} (r : α → β → Prop) :
    Except ε α → Except ε β → Prop
  | error (e : ε) : ExceptRel r (.error e) (.error e)
  | ok {a b} : r a b → ExceptRel r (.ok a) (.ok b)

attribute [relator] ExceptRel

class Recover (ε : Type u) (m : Type u → Type v) where
  recover {α : Type u} : Except ε (m α) → m α

derive_effect_rel Recover

/- Arguments that a relator does not lift are shared. -/
example {ε : Type u} {m : Type u → Type v} {n : Type u → Type w} (R : ComputationRelation m n)
    [left : Recover ε m] [right : Recover ε n] (h : Recover.Rel (ε := ε) R) {α : Type u}
    (e : ε) : R (left.recover (.error e : Except ε (m α))) (right.recover (.error e)) :=
  h.recover _ _ (.error e)

class LeakyError (m : Type → Type) where
  leak : Except (m Unit) Nat

/--
error: while deriving TapasTest.Applications.Monad.EffectRelation.LeakyError.Rel.leak:
logical relation: relator TapasTest.Applications.Monad.EffectRelation.ExceptRel shares an argument, which must be independent of the representation and equal on both sides:
m Unit
and
m' Unit
-/
#guard_msgs in
derive_effect_rel LeakyError

/- A registered relator takes precedence over unfolding a type constructor that is a
definition, as for quotient-based collections. -/
def Bag (α : Type u) := List α

def Bag.Rel {α : Type u} {β : Type v} (r : α → β → Prop) (xs : Bag α) (ys : Bag β) : Prop :=
  ListRel r xs ys

attribute [relator] Bag.Rel

class Bagged (m : Type → Type) where
  bag : Bag (m Nat)

derive_effect_rel Bagged

-- Unfolding `Bag` would have produced `ListRel` and no mention of the registered relator.
#guard_uses type Bagged.Rel.bag ⊇ [Bag.Rel]

def notARelator (x : Nat) : Prop := x = 0

/-- error: logical relation: relator TapasTest.Applications.Monad.EffectRelation.notARelator must have type `… → F α … → F β … → Prop` -/
#guard_msgs in
attribute [relator] notARelator

def sameSize {α β : Type} (xs : Array α) (ys : Array β) : Prop := xs.size = ys.size

/--
error: logical relation: relator TapasTest.Applications.Monad.EffectRelation.sameSize must take exactly one relation of type
  α → β → Prop
-/
#guard_msgs in
attribute [relator] sameSize

def optionAll {α : Type u} {β : Type v} (r : α → β → Prop) : Option α → Option β → Prop :=
  Option.Rel r

/-- error: logical relation: relator Option.Rel is already registered for Option -/
#guard_msgs in
attribute [relator] optionAll

/- `derive_type_rel` relates two interpretations of a type that binds its own monad, such as
the type of a capability-polymorphic program. -/
abbrev Program (σ : Type u) (α : Type u) :=
  {m : Type u → Type v} → [Monad m] → [MonadStateOf σ m] → m α

derive_type_rel Program (repr := m)

/-- The relation the type asks for: an arbitrary computation relation preserved by every
capability the program uses, at possibly different computation universes. -/
def expectedProgramRel {σ α : Type u} (p : Program.{u, v} σ α) (q : Program.{u, w} σ α) : Prop :=
  ∀ {m : Type u → Type v} {n : Type u → Type w} (R : ComputationRelation m n)
    [lm : Monad m] [rn : Monad n], Monad.Rel R →
    ∀ [ls : MonadStateOf σ m] [rs : MonadStateOf σ n], MonadStateOf.Rel (σ := σ) R →
      R (@p m lm ls) (@q n rn rs)

-- `@p` keeps Lean from inserting the program's implicit arguments at the use site, as it also
-- has to for a hand-written relation.
example {σ α : Type u} (p : Program.{u, v} σ α) (q : Program.{u, w} σ α) :
    Program.Rel (@p) (@q) ↔ expectedProgramRel (@p) (@q) := Iff.rfl

/- The same translation runs inside a capability: an operation taking a program of its own. -/
class Runner (m : Type u → Type v) where
  run {α : Type u} : ({n : Type u → Type v} → [Monad n] → n α) → m α

-- `run` binds a monad of its own, which the guess does not reach: name it too.
derive_effect_rel Runner (monad := m, n)

example {m : Type u → Type v} {n : Type u → Type w} (R : ComputationRelation m n)
    [left : Runner m] [right : Runner n] (h : Runner.Rel R) {α : Type u}
    (p : {k : Type u → Type v} → [Monad k] → k α) (q : {k : Type u → Type w} → [Monad k] → k α)
    (hpq : ∀ {k : Type u → Type v} {k' : Type u → Type w} (S : ComputationRelation k k')
      [Monad k] [Monad k'], Monad.Rel S → S (p (k := k)) (q (k := k'))) :
    R (left.run p) (right.run q) :=
  h.run p q hpq

/-- error: logical relation: declaration already exists: TapasTest.Applications.Monad.EffectRelation.Program.Rel -/
#guard_msgs in
derive_type_rel Program

/-- error: logical relation: expected a definition whose value is a type, got Nat -/
#guard_msgs in
derive_type_rel Nat

def notAType : Nat := 0

/-- error: logical relation: expected a definition whose value is a type, got TapasTest.Applications.Monad.EffectRelation.notAType -/
#guard_msgs in
derive_type_rel notAType

#guard_no_interface_rel Nested, Associated, Dependent, Collision, LeakyError, notAType

open Lean in
run_cmd do
  let env ← getEnv
  for (typeConstructor, relator) in [(``Option, ``Option.Rel), (``Sum, ``Sum.LiftRel),
      (``List, ``ListRel), (``Prod, ``ProdRel)] do
    unless (getRelator? env typeConstructor).map (·.relator) == some relator do
      throwError "the relator table does not map {typeConstructor} to {relator}"
  unless (getRelator? env ``Array).isNone do
    throwError "a rejected relator registration changed the relator table"
  let some monadInfo := getInterfaceRelation? env ``Monad
    | throwError "imported relation metadata is missing"
  unless monadInfo.fields == #[`map, `mapConst, `pure, `seq, `seqLeft, `seqRight, `bind] do
    throwError "Monad relation omitted or changed operation fields"
  unless (getInterfaceRelation? env ``Choose).isSome do
    throwError "duplicate generation removed existing metadata"

#guard_axioms Monad.Rel.pure, Monad.Rel.bind, MonadStateOf.Rel.modifyGet,
  MonadExceptOf.Rel.tryCatch, ScopedEmit.Rel.scope, AliasedScope.Rel.scope, Choose.Rel.choose,
  Monad.Rel.ofPureBind, idToOption ⊆ [propext, Quot.sound, Classical.choice]

end TapasTest.Applications.Monad.EffectRelation
