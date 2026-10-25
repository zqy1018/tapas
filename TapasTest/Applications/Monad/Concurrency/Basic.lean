module

import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.IO.Basic
public import TapasTest.Applications.Monad.Freer.Signature
public import Std.Sync.Mutex
public import Std.Sync.Channel

public section

/-!
Concurrent programs as request trees, with an interleaving semantics and a runtime.

A thread's program is a request tree (`Freer`, from `Freer/Basic.lean`) over `WithSpawn E`: the
requests of a first-order signature `E`, and spawning a thread, given by its request tree. The
spawned thread is itself a tree over `WithSpawn E`, so `WithSpawn` is nested through `Freer`;
every thread has the same type, and any thread may spawn. Signatures compose as sums (`Sig.sum` of `Freer/Signature.lean`), a program names
only the signatures it uses, and `Inj` finds a signature in a sum. Programs spawn through the capability
`MonadSpawn`, whose argument is a program of the same monad; at the request trees it is the
request `WithSpawn.spawn`.

The requests get two interpretations:

- `next exec` lists the configurations one step away: one thread makes one request. A
  first-order request acts on the shared state as `exec` says, and may be disabled; a spawn
  adds a thread. `Reach` is the closure of `next`, `run` follows a schedule through it, and
  `searchSchedule` searches it. Every proof about concurrency in this directory is a proof about
  `Reach`; what is trusted is that the runtime interleaves requests this way.
- `WithSpawn.io h` runs the requests with a handler `h` for `E`, and spawns with `IO.asTask`.

A program written against `MonadLiftT E₁ m`, for signatures `E₁` of `E`, and `MonadSpawn m` is
one program at both interpretations. `liftRel` and `spawnRel` say that the runtime interprets
each capability as the request trees do, so by parametricity the program's instance at `IO` is
the fold of its request tree with `WithSpawn.io h`; no IO primitive is unfolded, and no axiom
about one is assumed.

The resources of the examples, a mutex, a reference and a channel, are signatures with their
semantics and their handlers at the end of this file.
-/

namespace TapasTest.Applications.Monad.Concurrency.Basic

open TapasTest.Applications.Monad.Freer.Basic TapasTest.Applications.Monad.Freer.Signature
open TapasTest.Applications.Monad.IO.Basic Tapas.LogicalRelation

/-! ## Spawning on top of a signature -/

/-- The requests of a thread: those of the first-order signature `E`, and spawning a thread,
given by its request tree. -/
inductive WithSpawn (E : Type → Type) : Type → Type 1 where
  | base {β : Type} : E β → WithSpawn E β
  | spawn : Freer (WithSpawn E) Unit → WithSpawn E Unit

/-- A thread's program with its requests reified. -/
abbrev Thread (E : Type → Type) (α : Type) := Freer (WithSpawn E) α

/-- A signature of `E` is a signature of `WithSpawn E`, so it is requested at `Thread E`
through `MonadLiftT`. -/
instance [Inj E₁ E] : Inj E₁ (WithSpawn E) := ⟨fun op => .base (Inj.inj op)⟩

/-- Spawning a thread, as a capability: the argument is a program of the same monad. -/
class MonadSpawn (m : Type → Type u) where
  spawn : m Unit → m Unit

export MonadSpawn (spawn)

derive_effect_rel MonadSpawn

/-- At the request trees, spawning is the request `WithSpawn.spawn`. -/
instance : MonadSpawn (Thread E) := ⟨fun t => .impure (.spawn t) .pure⟩

-- No theorem depends on the priority: `IO.asTask` is never unfolded. A dedicated thread keeps
-- a thread that blocks on a mutex from occupying the thread pool.
/-- In `IO`, spawning runs the program on a new thread. -/
instance : MonadSpawn IO := ⟨fun c => do let _ ← IO.asTask c (prio := .dedicated); pure ()⟩

/-! ## Finalizers -/

-- Lean's `try ... finally` is `tryFinally` of `MonadFinally`, a library definition without a
-- parametricity rule, so finalizers are a capability of their own, with `tryFinally` as its
-- instance at `IO`.
/-- Running a finalizer after a computation, also when the computation throws. -/
class MonadFinalizer (m : Type → Type u) where
  withFinalizer {α : Type} : m α → m Unit → m α

export MonadFinalizer (withFinalizer)

derive_effect_rel MonadFinalizer

/-- At the request trees there are no exceptions, so the finalizer runs after the computation. -/
instance : MonadFinalizer (Thread E) := ⟨fun x f => do let a ← x; f; pure a⟩

/-- In `IO`, a finalizer runs in a `finally`. -/
instance : MonadFinalizer IO := ⟨fun x f => tryFinally x f⟩

/-! ## Interleaving semantics -/

/-- The semantics of a signature on a state: the outcomes of a request, each a result and the
new state. A request that blocks has no outcome. -/
abbrev Exec (E : Type → Type) (σ : Type) := (β : Type) → E β → σ → List (β × σ)

/-- The semantics of a signature on a part of a larger state. -/
@[expose] def Exec.zoom {E : Type → Type} {σ τ : Type} (get : σ → τ) (set : σ → τ → σ)
    (e : Exec E τ) : Exec E σ :=
  fun _ op s => (e _ op (get s)).map fun (v, t) => (v, set s t)

/-- A configuration: the threads, the first of which is the main thread, and the shared state. -/
structure Config (E : Type → Type) (σ : Type) where
  threads : List (Thread E Unit)
  shared : σ

/-- One request of a thread: its remaining program, the new shared state, and the threads it
spawned. -/
@[expose] def threadNext {E : Type → Type} {σ : Type} (exec : Exec E σ) (t : Thread E Unit)
    (s : σ) : List (Thread E Unit × σ × List (Thread E Unit)) :=
  match t with
  | .pure _ => []
  | .impure (.base op) k => (exec _ op s).map fun (v, s') => (k v, s', [])
  | .impure (.spawn t) k => [(k (), s, [t])]

/-- One request of one of the threads `ts`, where `pre` are the threads before them. Spawned
threads join the end of the list. -/
@[expose] def threadsNext {E : Type → Type} {σ : Type} (exec : Exec E σ)
    (pre : List (Thread E Unit)) : List (Thread E Unit) → σ → List (Config E σ)
  | [], _ => []
  | t :: rest, s =>
    ((threadNext exec t s).map fun (t', s', new) => ⟨pre ++ t' :: rest ++ new, s'⟩) ++
      threadsNext exec (pre ++ [t]) rest s

/-- The configurations one step away: one thread makes one request. -/
@[expose] def next {E : Type → Type} {σ : Type} (exec : Exec E σ) (c : Config E σ) :
    List (Config E σ) :=
  threadsNext exec [] c.threads c.shared

/-- The configurations reachable by some interleaving. -/
inductive Reach {E : Type → Type} {σ : Type} (exec : Exec E σ) : Config E σ → Config E σ → Prop
  | refl (c : Config E σ) : Reach exec c c
  | step {c c' c'' : Config E σ} : c' ∈ next exec c → Reach exec c' c'' → Reach exec c c''

theorem mem_threadsNext {E : Type → Type} {σ : Type} {exec : Exec E σ}
    {pre ts : List (Thread E Unit)} {s : σ} {c' : Config E σ}
    (h : c' ∈ threadsNext exec pre ts s) :
    ∃ pre' t rest t' s' new, ts = pre' ++ t :: rest ∧ (t', s', new) ∈ threadNext exec t s ∧
      c' = ⟨pre ++ pre' ++ t' :: rest ++ new, s'⟩ := by
  induction ts generalizing pre with
  | nil => cases h
  | cons t rest ih =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨⟨t', s', new⟩, hmem, rfl⟩ := List.mem_map.mp h
      exact ⟨[], t, rest, t', s', new, rfl, hmem, by simp⟩
    · obtain ⟨pre', t₀, rest', t', s', new, rfl, hmem, rfl⟩ := ih h
      exact ⟨t :: pre', t₀, rest', t', s', new, rfl, hmem, by simp⟩

/-- A step is a request of one thread. -/
theorem mem_next {E : Type → Type} {σ : Type} {exec : Exec E σ} {c c' : Config E σ}
    (h : c' ∈ next exec c) :
    ∃ pre t rest t' s' new, c.threads = pre ++ t :: rest ∧ (t', s', new) ∈ threadNext exec t c.shared ∧
      c' = ⟨pre ++ t' :: rest ++ new, s'⟩ := by
  obtain ⟨pre, t, rest, t', s', new, hsplit, hmem, rfl⟩ := mem_threadsNext h
  exact ⟨pre, t, rest, t', s', new, hsplit, hmem, by simp⟩

/-! ## Exploring the semantics -/

/-- Every thread has returned. -/
@[expose] def Config.done {E : Type → Type} {σ : Type} (c : Config E σ) : Bool :=
  c.threads.all fun | .pure _ => true | .impure _ _ => false

/-- Follow a schedule, which chooses at each step one of the configurations in `next`. -/
@[expose] def run {E : Type → Type} {σ : Type} (exec : Exec E σ) (c : Config E σ) :
    List Nat → Option (Config E σ)
  | [] => some c
  | i :: sched =>
    match (next exec c)[i]? with
    | some c' => run exec c' sched
    | none => none

/-- A schedule only visits reachable configurations. -/
theorem run_sound {E : Type → Type} {σ : Type} {exec : Exec E σ} {c c' : Config E σ}
    {sched : List Nat} (h : run exec c sched = some c') : Reach exec c c' := by
  induction sched generalizing c with
  | nil => cases h; exact .refl _
  | cons i sched ih =>
    simp only [run] at h
    split at h
    · exact .step (List.mem_of_getElem? ‹_›) (ih h)
    · cases h

/-- Search, to a depth, for a schedule that reaches a configuration satisfying `bad`. -/
def searchSchedule {E : Type → Type} {σ : Type} (exec : Exec E σ) (bad : Config E σ → Bool) :
    Nat → Config E σ → Option (List Nat)
  | 0, c => if bad c then some [] else none
  | fuel + 1, c =>
    if bad c then some [] else
      (List.range (next exec c).length).findSome? fun i =>
        ((next exec c)[i]?).bind fun c' => (searchSchedule exec bad fuel c').map (i :: ·)

/-! ## The runtime -/

mutual
/-- Run a request with the handler `h` of its signature; a spawned thread runs its request tree
on a new thread. -/
def WithSpawn.io {E : Type → Type} (h : (β : Type) → E β → IO β) :
    (β : Type) → WithSpawn E β → IO β
  | _, .base op => h _ op
  -- NOTE: This interprets `t`. An execution does not go through this branch: it spawns
  -- through the `MonadSpawn IO` instance, with the spawned program compiled. The branch gives
  -- the request `WithSpawn.spawn` its meaning, which `spawnRel` needs.
  | _, .spawn t => do
    let _ ← IO.asTask (runThread h t) (prio := .dedicated)
    pure ()
/-- Run a thread's request tree with the handler `h` of its signature. -/
def runThread {E : Type → Type} (h : (β : Type) → E β → IO β) : Thread E Unit → IO Unit
  | .pure a => pure a
  | .impure op k => do runThread h (k (← WithSpawn.io h _ op))
end

theorem runThread_eq_fold {E : Type → Type} (h : (β : Type) → E β → IO β) (t : Thread E Unit) :
    runThread h t = Freer.fold (WithSpawn.io h) t := by
  induction t with
  | pure a => rfl
  | impure op k ih => simp only [runThread, Freer.fold, ih]

/-! ## The runtime interprets the capabilities as the request trees do -/

/-- Each request of a signature `E₁` of `E` runs as `h` says: the graph of
`Freer.fold (WithSpawn.io h)` relates the two `MonadLiftT E₁` instances. -/
theorem liftRel {E E₁ : Type → Type} [Inj E₁ E] (h : (β : Type) → E β → IO β) :
    letI : MonadLiftT E₁ IO := ⟨fun op => h _ (Inj.inj op)⟩
    MonadLiftT.Rel (m := E₁) (graph (WithSpawn.io h)) :=
  MonadLiftT.Rel.mk (left := (_)) (right := (_)) (graph (WithSpawn.io h))
    (fun op => Freer.fold_monadLift (WithSpawn.io h) (.base (Inj.inj op)))

/-- Spawning runs the spawned program: the same graph relates the two `MonadSpawn` instances. -/
theorem spawnRel {E : Type → Type} (h : (β : Type) → E β → IO β) :
    MonadSpawn.Rel (graph (WithSpawn.io h)) where
  spawn x y hxy := by
    have hxy' : Freer.fold (WithSpawn.io h) x = y := hxy
    change Freer.fold (WithSpawn.io h) (.impure (.spawn x) .pure) = _
    simp only [Freer.fold, bind_pure, WithSpawn.io, runThread_eq_fold, hxy']
    rfl

-- CHECK What are these?
/-- The runtime never throws when the handler of the signature does not. -/
theorem WithSpawn.io_noError {E : Type → Type} (h : (β : Type) → E β → IO β)
    (hh : ∀ β (op : E β), NoError (h β op)) (β : Type) (op : WithSpawn E β) :
    NoError (WithSpawn.io h β op) := by
  cases op with
  | base op => exact hh _ op
  | spawn t => exact NoError.bind (NoError.lift _) fun _ => NoError.pure ()

/-- A request tree run by a runtime that never throws never throws. -/
theorem fold_noError {E : Type → Type} (h : (β : Type) → E β → IO β)
    (hh : ∀ β (op : E β), NoError (h β op)) {α : Type} (t : Thread E α) :
    NoError (Freer.fold (WithSpawn.io h) t) := by
  induction t with
  | pure a => exact NoError.pure a
  | impure op k ih => exact NoError.bind (WithSpawn.io_noError h hh _ op) ih

/-- A finalizer runs after its computation: when the runtime never throws, the same graph
relates the two `MonadFinalizer` instances. -/
theorem finalizerRel {E : Type → Type} (h : (β : Type) → E β → IO β)
    (hh : ∀ β (op : E β), NoError (h β op)) : MonadFinalizer.Rel (graph (WithSpawn.io h)) where
  withFinalizer x y hxy f g hfg := by
    have hxy' : Freer.fold (WithSpawn.io h) x = y := hxy
    have hfg' : Freer.fold (WithSpawn.io h) f = g := hfg
    change Freer.fold (WithSpawn.io h) (Freer.bind x fun a => Freer.bind f fun _ => .pure a) =
      tryFinally y g
    rw [Freer.fold_bind, hxy', tryFinally_of_noError (hxy' ▸ fold_noError h hh x)]
    congr 1
    funext a
    rw [Freer.fold_bind, hfg']
    rfl

/-! ## Resources: a mutex, a reference, and a channel -/

/-- Lock or unlock a mutex. -/
inductive MutexOp : Type → Type where
  | lock : MutexOp Unit
  | unlock : MutexOp Unit

/-- The state of a mutex is whether it is held. Locking a held mutex blocks. -/
@[expose] def MutexOp.exec : Exec MutexOp Bool
  | _, .lock, held => if held then [] else [((), true)]
  | _, .unlock, _ => [((), false)]

@[expose] def MutexOp.io (mutex : Std.BaseMutex) : (β : Type) → MutexOp β → IO β
  | _, .lock => BaseIO.toIO mutex.lock
  | _, .unlock => BaseIO.toIO mutex.unlock

/-- Read or write a reference holding a `σ`. -/
inductive RefOp (σ : Type) : Type → Type where
  | read : RefOp σ σ
  | write : σ → RefOp σ Unit

/-- The state of a reference is its content. -/
@[expose] def RefOp.exec {σ : Type} : Exec (RefOp σ) σ
  | _, .read, s => [(s, s)]
  | _, .write v, _ => [((), v)]

@[expose] def RefOp.io {σ : Type} (ref : IO.Ref σ) : (β : Type) → RefOp σ β → IO β
  | _, .read => BaseIO.toIO ref.get
  | _, .write v => BaseIO.toIO (ref.set v)

/-- Send a message on a channel, or receive one. -/
inductive ChanOp : Type → Type where
  | send : ChanOp Unit
  | recv : ChanOp Unit

/-- The state of a channel is the number of messages sent but not yet received. Receiving from
an empty channel blocks. -/
@[expose] def ChanOp.exec : Exec ChanOp Nat
  | _, .send, q => [((), q + 1)]
  | _, .recv, q => if q = 0 then [] else [((), q - 1)]

@[expose] def ChanOp.io (channel : Std.Channel.Sync Unit) : (β : Type) → ChanOp β → IO β
  | _, .send => BaseIO.toIO (channel.send ())
  | _, .recv => BaseIO.toIO channel.recv

#guard_axioms mem_threadsNext, mem_next, run_sound ⊆ [propext, Quot.sound]
-- `Classical.choice` enters through `IO.asTask`, which `WithSpawn.io` calls.
#guard_axioms runThread_eq_fold, liftRel, spawnRel, WithSpawn.io_noError, fold_noError, finalizerRel
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Concurrency.Basic
