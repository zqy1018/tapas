module

public import TapasTest.TestingUtils

public section

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.Program

def pureProgram {α : Type u} (a : α) := infer_effects% pure a
derive_parametric pureProgram (repr := m)

example {α : Type u} {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (R : ComputationRelation m n)
    (hm : Monad.Rel R) (a : α) :
    R (pureProgram (m := m) a) (pureProgram (m := n) a) :=
  pureProgram.parametric a R hm

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

def manyBinds := infer_effects% do
  let a ← tick
  let b ← tick
  let c ← tick
  let d ← tick
  let e ← tick
  let f ← tick
  let g ← tick
  let h ← tick
  pure (a + b + c + d + e + f + g + h)
derive_parametric manyBinds

-- Registered translations take priority even for exact field-forwarding wrappers.
def reusesPure := infer_effects% pureProgram 23
derive_parametric reusesPure

def localFunction (b : Bool) := infer_effects% do
  let next := fun n : Nat => do
    set n
    tick
  if b then next 1 else next 2
derive_parametric localFunction

def pureLet := infer_effects% do
  let n ← tick
  let incremented := n + 1
  set incremented
  pure incremented
derive_parametric pureLet

def applicative := infer_effects% do
  let next := (· + 1) <$> tick
  Prod.mk <$> next <*> tick
derive_parametric applicative

class Emit (m : Type → Type v) where
  emit : String → m Unit

derive_effect_rel Emit

def emitProgram := infer_effects% do
  Emit.emit "hello"
  tick
derive_parametric emitProgram

class Choose {α : Type u} (p : α → Prop) (m : Type u → Type v) where
  choose : m α

derive_effect_rel Choose

def dependentChoice := infer_effects% do
  let n ← get
  let x ← Choose.choose (p := fun x : Fin 10 => x.val ≤ n)
  pure x.val
derive_parametric dependentChoice

example {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] [MonadStateOf Nat m] [MonadStateOf Nat n]
    [lc : ∀ k : Nat, Choose (fun x : Fin 10 => x.val ≤ k) m]
    [rc : ∀ k : Nat, Choose (fun x : Fin 10 => x.val ≤ k) n]
    (R : ComputationRelation m n) (hm : Monad.Rel R)
    (hs : MonadStateOf.Rel (σ := Nat) R)
    (hc : ∀ k, Choose.Rel (left := lc k) (right := rc k) R) :
    R (dependentChoice (m := m)) (dependentChoice (m := n)) :=
  dependentChoice.parametric R hm hs hc

def handler := infer_effects% do
  try
    throw "failure"
  catch e =>
    pure <| String.length e
derive_parametric handler

def tiedError {m : Type → Type v} [Monad m]
    [MonadExceptOf (ULift.{v} Unit) m] : m Nat :=
  throwThe (ULift.{v} Unit) ⟨()⟩
derive_parametric tiedError

example {m n : Type → Type v} [Monad m] [Monad n]
    [MonadExceptOf (ULift.{v} Unit) m] [MonadExceptOf (ULift.{v} Unit) n]
    (R : ComputationRelation m n) (hm : Monad.Rel R)
    (he : MonadExceptOf.Rel (ε := ULift.{v} Unit) R) :
    R (tiedError (m := m)) (tiedError (m := n)) := tiedError.parametric R hm he

def scopedReader := infer_effects% do
  withTheReader Nat (· + 1) do
    let n ← readThe Nat
    pure (n + 2)
derive_parametric scopedReader

def lifted {base : Type u → Type w} {α : Type u} (x : base α) := infer_effects% do
  let a ← monadLift x
  pure a
derive_parametric lifted (repr := m)

abbrev tickAlias := @tick
def throughAlias := infer_effects% tickAlias
derive_parametric throughAlias

infer_effects
def functionArgument (x : m Nat) (f : Nat → m Nat) : m Nat := x >>= f
derive_parametric functionArgument

@[expose] def unknownHelper := infer_effects% pure (37 : Nat)
@[expose] def usesUnknown := infer_effects% unknownHelper
/-- error: parametricity: no applicable translation for TapasTest.Applications.Monad.Program.unknownHelper; use `derive_parametric TapasTest.Applications.Monad.Program.unknownHelper` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric usesUnknown

@[parametric] theorem unusableTranslation {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] (R : ComputationRelation m n) (h : False) :
    R (unknownHelper (m := m)) (unknownHelper (m := n)) := h.elim

-- Preserve the failed premise's error when no alternative rule succeeds.
/--
error: parametricity: missing relational premise:
False
-/
#guard_msgs in
derive_parametric usesUnknown

theorem manualTranslation {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] (R : ComputationRelation m n)
    (h : ∀ {α} (a : α), R (pure a) (pure a)) :
    R (unknownHelper (m := m)) (unknownHelper (m := n)) := h 37
attribute [parametric] manualTranslation
-- Repeated registration must not duplicate the rule.
attribute [parametric] manualTranslation
derive_parametric usesUnknown

-- `as` puts the theorem in the current namespace instead of the source's. Deriving a
-- definition from another library is what it is for: the registry reads the theorem's
-- conclusion and never its name, so nothing is lost, and `List.forIn'.parametric` stays
-- free for that library's own users to claim.
derive_parametric List.forIn'.loop as listLoopRel (repr := m)
derive_parametric List.forIn' as listRel (repr := m)

example {m : Type → Type} {m' : Type → Type} [Monad m] [Monad m']
    (R : ComputationRelation m m') (hm : Monad.Rel R) (xs : List Nat) (init : Nat)
    (f : (a : Nat) → a ∈ xs → Nat → m (ForInStep Nat))
    (f' : (a : Nat) → a ∈ xs → Nat → m' (ForInStep Nat))
    (hf : ∀ a h b, R (f a h b) (f' a h b)) :
    R (xs.forIn' init f) (xs.forIn' init f') := listRel R hm xs init f f' hf

open Lean in
run_cmd do
  for n in [``List.forIn'.loop, ``List.forIn'] do
    if (← getEnv).contains (n ++ `parametric) then
      throwError "`as` still claimed {n ++ `parametric}"
    if (getParametricRules (← getEnv) n).isEmpty then
      throwError "the renamed theorem was not registered for {n}"

-- The rule is keyed by the conclusion, so the source's own name stays available.
derive_parametric List.forIn' (repr := m)

-- A recursive block declares one theorem per member, which one name cannot cover.
infer_effects
mutual
def pingRel : Nat → m Bool
  | 0 => pure true
  | k + 1 => pongRel k
def pongRel : Nat → m Bool
  | 0 => pure false
  | k + 1 => pingRel k
end

/--
error: parametricity: TapasTest.Applications.Monad.Program.pingRel is derived together with [TapasTest.Applications.Monad.Program.pongRel], so `as` cannot name the result
-/
#guard_msgs in
derive_parametric pingRel as bothRel

class NamedState (m : Type → Type v) extends MonadStateOf Nat m where
  name : m String

derive_effect_rel NamedState

def inherited := infer_effects% do
  let _ ← NamedState.name
  tick
derive_parametric inherited

def dependentParameter {m : Type → Type v} (x : m Nat) (_h : x = x) : m Nat := x
/--
error: logical relation: dependent representation arguments are unsupported
-/
#guard_msgs in
derive_parametric dependentParameter

class NeedsUnsupported (m : Type → Type) where
  run : Array (m Nat) → m Nat
def unsupported {m : Type → Type} [NeedsUnsupported m] : m Nat :=
  NeedsUnsupported.run #[]
-- `NeedsUnsupported.Rel` is never generated -- `Array (m Nat)` has no relator, which
-- `TapasTest/Applications/Monad/EffectRelation.lean` covers. What matters here is what
-- `derive_parametric` does when the interface it needs has no relation.
/--
error: logical relation: unsupported representation-dependent type:
NeedsUnsupported m
generate its relation with `derive_interface_rel TapasTest.Applications.Monad.Program.NeedsUnsupported (repr := ...)`
-/
#guard_msgs in
derive_parametric unsupported

-- Relator premises can be passed on, and registered inductive relators also
-- construct proofs for matching value constructors.
class Fallback (m : Type → Type) where
  orDefault : Option (m Nat) → m Nat

derive_effect_rel Fallback

infer_effects
def viaFallback (x : Option (m Nat)) : m Nat := do
  let a ← Fallback.orDefault x
  pure (a + 1)
derive_parametric viaFallback

infer_final (m : Type → Type)
def wrapsSome (x : m Nat) : m Nat :=
  Fallback.orDefault (some x)
/- The registered `Option.Rel` constructors now establish the previously
missing premise `Option.Rel R (some x) (some x')` from the relation on `x`. -/
derive_parametric wrapsSome

example {m n : Type → Type} (R : ComputationRelation m n)
    [Fallback m] [Fallback n] (h : Fallback.Rel R)
    (x : m Nat) (y : n Nat) (hxy : R x y) :
    R (wrapsSome x) (wrapsSome y) := wrapsSome.parametric R h x y hxy

class RolledBack (m : Type → Type v) where
  run : m Nat

derive_effect_rel RolledBack

def unregistered := infer_effects% pure false
def failsAfterRelation := infer_effects% do
  let _ ← RolledBack.run
  unregistered
/-- error: parametricity: no applicable translation for TapasTest.Applications.Monad.Program.unregistered; use `derive_parametric TapasTest.Applications.Monad.Program.unregistered` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric failsAfterRelation

noncomputable def observesMonad {m : Type → Type} [Monad m] : m Bool := by
  classical
  exact if Subsingleton (m Unit) then pure true else pure false
/-- error: parametricity: condition depends on the representation or differs between interpretations -/
#guard_msgs in
derive_parametric observesMonad

-- This is also a concrete counterexample for the lawful Id-to-Option graph relation.
example : some (observesMonad (m := Id)).run ≠ observesMonad (m := Option) := by
  have hi : Subsingleton (Id Unit) := ⟨fun a b => by cases a; cases b; rfl⟩
  have ho : ¬ Subsingleton (Option Unit) := by
    intro h
    have bad := @Subsingleton.elim (Option Unit) h (some ()) none
    cases bad
  simp [observesMonad, hi, ho]

/-- error: parametricity: declaration already exists: TapasTest.Applications.Monad.Program.tick.parametric -/
#guard_msgs in
derive_parametric tick

/-- error: parametricity: TapasTest.Applications.Monad.Program.tick is not a proof -/
#guard_msgs in
attribute [parametric] tick

theorem differentHeadsTranslation {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] (R : ComputationRelation m n)
    (h : ∀ {α} (a : α), R (pure a) (pure a)) :
    R (unknownHelper (m := m)) (pure 37 : n Nat) := h 37

/-- error: parametricity: TapasTest.Applications.Monad.Program.differentHeadsTranslation must conclude `R (f ...) (f ...)` for the same constant `f` -/
#guard_msgs in
attribute [parametric] differentHeadsTranslation

theorem localHeadTranslation (f : Nat → Nat) (n : Nat) : f n = f n := rfl

/-- error: parametricity: TapasTest.Applications.Monad.Program.localHeadTranslation must conclude `R (f ...) (f ...)` for the same constant `f` -/
#guard_msgs in
attribute [parametric] localHeadTranslation

theorem nonRelationalTranslation : True := True.intro

/-- error: parametricity: TapasTest.Applications.Monad.Program.nonRelationalTranslation must conclude `R (f ...) (f ...)` for the same constant `f` -/
#guard_msgs in
attribute [parametric] nonRelationalTranslation

/-- error: parametricity: parametricity theorems can only be registered globally -/
#guard_msgs in
attribute [local parametric] manualTranslation

/-- error: parametricity: parametricity theorems can only be registered globally -/
#guard_msgs in
attribute [scoped parametric] manualTranslation

/-- error: Unexpected attribute argument: This attribute takes no arguments -/
#guard_msgs in
attribute [parametric 1000] manualTranslation

#guard_no_parametric dependentParameter, unsupported, failsAfterRelation, observesMonad

-- A helper's translation is reused rather than expanded, and a registered forwarding wrapper
-- is not unfolded before its rule is looked up.
#guard_uses manyBinds.parametric ⊇ [tick.parametric]
#guard_uses reusesPure.parametric ⊇ [pureProgram.parametric]

-- The rule search backtracks from the inapplicable rule to the hand-written one.
#guard_uses usesUnknown.parametric ⊇ [manualTranslation]
#guard_uses usesUnknown.parametric ∩ [unusableTranslation] = ∅

-- A local function and an ordinary local value keep their sharing in the generated proof.
#guard_binds localFunction.parametric ⊇ [next, next', next_rel]
#guard_binds pureLet.parametric ⊇ [incremented]

open Lean in
run_cmd do
  -- A failed registration leaves the registry, including its order, exactly as it was.
  unless getParametricRules (← getEnv) ``unknownHelper ==
      #[``unusableTranslation, ``manualTranslation] do
    throwError "failed registration changed the registry"

#guard_axioms pureProgram.parametric, tick.parametric, manyBinds.parametric,
  reusesPure.parametric, localFunction.parametric, pureLet.parametric, applicative.parametric,
  emitProgram.parametric, dependentChoice.parametric, handler.parametric, tiedError.parametric,
  scopedReader.parametric, lifted.parametric, throughAlias.parametric,
  functionArgument.parametric, usesUnknown.parametric, inherited.parametric,
  viaFallback.parametric ⊆ [propext, Quot.sound, Classical.choice]

-- The two shapes whose proofs share subterms stay free of every axiom.
#guard_axioms manyBinds.parametric, localFunction.parametric ⊆ []

end TapasTest.Applications.Monad.Program
