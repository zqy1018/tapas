module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.IO.Basic
public import TapasTest.Applications.Monad.Concurrency.Basic
meta import TapasTest.Applications.Monad.Concurrency.Basic

public section

/-!
A counter incremented by concurrent workers under a mutex: verified over every interleaving,
and run in IO.

The system composes three resources: a mutex, a counter, and a channel. The programs are
written once, against `MonadLiftT` for the signatures they use and `MonadSpawn`. `worker`
increments the counter under the mutex and then sends a message; `main w n` spawns `n` threads
running the program `w` and receives `n` messages. The main thread is the first thread of the
configuration; what it achieves is read off the shared state.

- `main_result`: in every interleaving of `main worker n`, once the main thread has returned,
  the counter is `n`. The proof is an invariant of every reachable configuration (`Inv`),
  checked against each request.
- `unlocked_loses_update`: for the worker without the mutex and two workers, some interleaving
  ends with the counter at `1`. `searchSchedule` finds the schedule, and `run` certifies it.
- `mainIO_eq`: the program at `IO` is the fold of the same request tree with the runtime
  handler. This is parametricity; no IO primitive is unfolded.
-/

namespace TapasTest.Applications.Monad.Concurrency.Counter

open TapasTest.Applications.Monad.Freer.Basic TapasTest.Applications.Monad.Freer.Signature
open TapasTest.Applications.Monad.IO.Basic TapasTest.Applications.Monad.Concurrency.Basic

/-! ## The system -/

/-- The signature: a mutex, a reference holding the counter, and a channel. -/
abbrev Sig := Sig.sum MutexOp (Sig.sum (RefOp Nat) ChanOp)

/-- The shared state: whether the mutex is held, the counter, and the number of messages sent
but not yet received. -/
structure Shared where
  locked : Bool
  counter : Nat
  queue : Nat
  deriving DecidableEq, Repr

/-- Each resource acts on its own field of the shared state. -/
@[expose] def exec : Exec Sig Shared :=
  Sig.sum.elim (Exec.zoom (·.locked) (fun s b => { s with locked := b }) MutexOp.exec)
    (Sig.sum.elim (Exec.zoom (·.counter) (fun s v => { s with counter := v }) RefOp.exec)
      (Exec.zoom (·.queue) (fun s q => { s with queue := q }) ChanOp.exec))

/-! ## The programs -/

/-- Increment the counter under the mutex, then report. -/
@[expose] def worker := infer_effects% do
  liftM MutexOp.lock
  let v ← liftM RefOp.read
  liftM (RefOp.write (v + 1))
  liftM MutexOp.unlock
  liftM ChanOp.send

/-- Increment the counter without the mutex, then report. -/
@[expose] def unlockedWorker := infer_effects% do
  let v ← liftM RefOp.read
  liftM (RefOp.write (v + 1))
  liftM ChanOp.send

derive_parametric worker
derive_parametric unlockedWorker

infer_effects
/-- Spawn `k` threads running `w`. -/
def spawnAll (w : m Unit) : Nat → m Unit
  | 0 => pure ()
  | k + 1 => do spawn w; spawnAll w k

infer_effects
/-- Receive `k` messages. -/
def recvAll : Nat → m Unit
  | 0 => pure ()
  | k + 1 => do liftM ChanOp.recv; recvAll k

infer_effects
/-- Spawn `n` threads running `w`, then receive `n` messages. -/
def main (w : m Unit) (n : Nat) : m Unit := do
  spawnAll w n
  recvAll n

derive_parametric spawnAll
derive_parametric recvAll
derive_parametric main

/-! ## Request trees -/

-- CHECK Things below require a better handling ...

/-- The worker's request tree: the worker at `Thread Sig`. -/
@[expose] def workerTree : Thread Sig Unit := worker (m := Thread Sig)

/-- The request tree of the worker without the mutex. -/
@[expose] def unlockedTree : Thread Sig Unit := unlockedWorker (m := Thread Sig)

/-- The requests of the system, as they appear in request trees. -/
abbrev lockReq : WithSpawn Sig Unit := .base (.inl .lock)
abbrev unlockReq : WithSpawn Sig Unit := .base (.inl .unlock)
abbrev readReq : WithSpawn Sig Nat := .base (.inr (.inl .read))
abbrev writeReq (v : Nat) : WithSpawn Sig Unit := .base (.inr (.inl (.write v)))
abbrev sendReq : WithSpawn Sig Unit := .base (.inr (.inr .send))
abbrev recvReq : WithSpawn Sig Unit := .base (.inr (.inr .recv))

/-- The main thread after its spawns: receive `k` messages. -/
def recvTree : Nat → Thread Sig Unit
  | 0 => .pure ()
  | k + 1 => .impure recvReq fun _ => recvTree k

/-- The main thread with `k` of its `n` spawns to go. -/
def spawnTree (w : Thread Sig Unit) (n : Nat) : Nat → Thread Sig Unit
  | 0 => recvTree n
  | k + 1 => .impure (.spawn w) fun _ => spawnTree w n k

/-- The request tree of `main w n`, spelled out. -/
theorem tree_main (w : Thread Sig Unit) (n : Nat) :
    main (m := Thread Sig) w n = spawnTree w n n := by
  have hrecv : ∀ k, recvAll (m := Thread Sig) k = recvTree k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg (Freer.impure recvReq) (funext fun _ => ih)
  have hspawn : ∀ k, (spawnAll (m := Thread Sig) w k >>= fun _ => recvAll n) = spawnTree w n k := by
    intro k
    induction k with
    | zero => exact hrecv n
    | succ k ih => exact congrArg (Freer.impure (.spawn w)) (funext fun _ => ih)
  exact hspawn n

/-- The initial configuration: the main thread alone, the mutex free, the counter `0`, and no
messages. -/
@[expose] def init (w : Thread Sig Unit) (n : Nat) : Config Sig Shared :=
  ⟨[main (m := Thread Sig) w n], ⟨false, 0, 0⟩⟩

/-! ## Once the main thread has returned, the counter is `n` -/

/-- Where a worker is in its program. -/
inductive Stage where
  | start
  | locked
  | read (v : Nat)
  | written
  | unlocked
  | done

/-- The worker's remaining program at each stage. -/
@[expose] def Stage.tree : Stage → Thread Sig Unit
  | .start => .impure lockReq fun _ => .impure readReq fun v => .impure (writeReq (v + 1)) fun _ =>
      .impure unlockReq fun _ => .impure sendReq fun _ => .pure ()
  | .locked => .impure readReq fun v => .impure (writeReq (v + 1)) fun _ =>
      .impure unlockReq fun _ => .impure sendReq fun _ => .pure ()
  | .read v => .impure (writeReq (v + 1)) fun _ => .impure unlockReq fun _ => .impure sendReq fun _ =>
      .pure ()
  | .written => .impure unlockReq fun _ => .impure sendReq fun _ => .pure ()
  | .unlocked => .impure sendReq fun _ => .pure ()
  | .done => .pure ()

theorem workerTree_eq : workerTree = Stage.start.tree := by rfl

/-- The worker holds the mutex. -/
def Stage.inCS : Stage → Bool
  | .locked | .read _ | .written => true
  | .start | .unlocked | .done => false

/-- The worker has written its increment. -/
def Stage.hasWritten : Stage → Bool
  | .written | .unlocked | .done => true
  | .start | .locked | .read _ => false

/-- The worker has sent its message. -/
def Stage.hasSent : Stage → Bool
  | .done => true
  | .start | .locked | .read _ | .written | .unlocked => false

/-- Where the main thread is in its program. -/
inductive MainStage where
  /-- `k + 1` spawns to go. -/
  | spawning (k : Nat)
  /-- `k + 1` messages to receive. -/
  | receiving (k : Nat)
  | done

/-- The main thread's remaining program at each stage. -/
@[expose] def MainStage.tree (n : Nat) : MainStage → Thread Sig Unit
  | .spawning k => spawnTree workerTree n (k + 1)
  | .receiving k => recvTree (k + 1)
  | .done => .pure ()

/-- The number of workers spawned. -/
def MainStage.spawned (n : Nat) : MainStage → Nat
  | .spawning k => n - (k + 1)
  | .receiving _ | .done => n

/-- The number of messages received. -/
def MainStage.received (n : Nat) : MainStage → Nat
  | .spawning _ => 0
  | .receiving k => n - (k + 1)
  | .done => n

/-- The stage is consistent with `n`. -/
def MainStage.wf (n : Nat) : MainStage → Prop
  | .spawning k | .receiving k => k + 1 ≤ n
  | .done => True

/-- The invariant of every configuration reachable from `init workerTree n`: the main thread
and each worker are at some stage of their programs; the stages account for the counter, the
mutex and the messages; at most one worker holds the mutex; and a worker that has read the
counter holds the mutex, so what it read is still the counter. -/
inductive Inv (n : Nat) (c : Config Sig Shared) : Prop where
  | mk (stages : List Stage) (mstage : MainStage)
    (threads_eq : c.threads = mstage.tree n :: stages.map Stage.tree)
    (wf : mstage.wf n)
    (length_eq : stages.length = mstage.spawned n)
    (counter_eq : c.shared.counter = stages.countP Stage.hasWritten)
    (locked_eq : c.shared.locked = stages.any Stage.inCS)
    (cs_le : stages.countP Stage.inCS ≤ 1)
    (read_eq : ∀ v, Stage.read v ∈ stages → v = c.shared.counter)
    (queue_eq : c.shared.queue + mstage.received n = stages.countP Stage.hasSent)

theorem Inv.of_init (n : Nat) : Inv n (init workerTree n) := by
  cases n with
  | zero =>
    exact ⟨[], .done, by simp [init, tree_main, MainStage.tree, spawnTree, recvTree], trivial, rfl,
      rfl, rfl, by decide, by simp, rfl⟩
  | succ n =>
    exact ⟨[], .spawning n, by simp [init, tree_main, MainStage.tree], by simp [MainStage.wf],
      by simp [MainStage.spawned], rfl, rfl, by decide, by simp, by simp [init, MainStage.received]⟩

-- A worker that has read holds the mutex, so no other worker is at a `read` stage.
private theorem not_read_of_cs {l₁ l₃ : List Stage} {stg : Stage} (hstg : stg.inCS = true)
    (hcs : (l₁ ++ stg :: l₃).countP Stage.inCS ≤ 1) (v : Nat) :
    Stage.read v ∉ l₁ ++ l₃ := by
  intro hv
  have : 0 < (l₁ ++ l₃).countP Stage.inCS := List.countP_pos_iff.mpr ⟨_, hv, rfl⟩
  simp [hstg] at hcs this
  omega

-- Spawning a worker adds a stage `start`; the main thread's new stage is given.
private theorem inv_spawn {n : Nat} {stages : List Stage} {mstage' : MainStage} {s : Shared}
    {m : Thread Sig Unit} (htree : m = mstage'.tree n) (hwf : mstage'.wf n)
    (hlen : stages.length + 1 = mstage'.spawned n)
    (hcnt : s.counter = stages.countP Stage.hasWritten)
    (hlk : s.locked = stages.any Stage.inCS) (hcs : stages.countP Stage.inCS ≤ 1)
    (hrd : ∀ v, Stage.read v ∈ stages → v = s.counter)
    (hq : s.queue + mstage'.received n = stages.countP Stage.hasSent) :
    Inv n ⟨m :: (stages.map Stage.tree ++ [workerTree]), s⟩ := by
  refine ⟨stages ++ [.start], mstage', by simp [htree, workerTree_eq], hwf, by simpa using hlen,
    by simpa [List.countP_cons, Stage.hasWritten] using hcnt,
    by simpa [List.any_cons, Stage.inCS] using hlk,
    by simpa [List.countP_cons, Stage.inCS] using hcs, ?_,
    by simpa [List.countP_cons, Stage.hasSent] using hq⟩
  intro v hv
  simp at hv
  exact hrd v hv

theorem Inv.step {n : Nat} {c c' : Config Sig Shared} (h : Inv n c) (hs : c' ∈ next exec c) :
    Inv n c' := by
  obtain ⟨ts, s⟩ := c
  obtain ⟨stages, mstage, hw, hwf, hlen, hcnt, hlk, hcs, hrd, hq⟩ := h
  dsimp only at hw hcnt hlk hrd hq
  subst hw
  obtain ⟨pre, t, rest, t', s', new, hsplit, hmem, rfl⟩ := mem_next hs
  dsimp only at hsplit hmem
  cases pre with
  | nil =>
    -- The main thread makes a request.
    simp only [List.nil_append, List.cons.injEq] at hsplit
    obtain ⟨rfl, rfl⟩ := hsplit
    simp only [List.nil_append]
    cases mstage with
    | spawning k =>
      simp only [MainStage.tree, spawnTree, threadNext, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, hs', rfl⟩ := hmem
      rw [hs']
      simp only [MainStage.wf, MainStage.spawned, MainStage.received] at hwf hlen hq
      -- The main thread spawns again, or starts receiving.
      cases k with
      | zero =>
        obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact inv_spawn (mstage' := .receiving n) rfl (by simp [MainStage.wf])
          (by simp [MainStage.spawned]; omega) hcnt hlk hcs hrd
          (by simpa [MainStage.received] using hq)
      | succ k =>
        exact inv_spawn (mstage' := .spawning k) rfl (by simp [MainStage.wf]; omega)
          (by simp [MainStage.spawned]; omega) hcnt hlk hcs hrd
          (by simpa [MainStage.received] using hq)
    | receiving k =>
      simp only [MainStage.tree, recvTree, recvReq, threadNext, exec, Sig.sum.elim, Exec.zoom,
        ChanOp.exec] at hmem
      simp only [MainStage.wf, MainStage.spawned, MainStage.received] at hwf hlen hq
      split at hmem
      · simp at hmem
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        rw [List.append_nil]
        -- One message fewer in the channel, one more received.
        have hinv : ∀ mstage' : MainStage, mstage'.tree n = recvTree k → mstage'.wf n →
            mstage'.spawned n = n → mstage'.received n = n - k →
            Inv n ⟨recvTree k :: stages.map Stage.tree, { s with queue := s.queue - 1 }⟩ := by
          intro mstage' htree hwf' hsp hrc
          exact ⟨stages, mstage', by rw [htree], hwf', by simp [hsp, hlen], hcnt, hlk, hcs, hrd,
            by simp [hrc]; omega⟩
        cases k with
        | zero => exact hinv .done rfl trivial rfl (by simp [MainStage.received])
        | succ k =>
          exact hinv (.receiving k) rfl (by simp [MainStage.wf]; omega) rfl
            (by simp [MainStage.received])
    | done => simp [MainStage.tree, threadNext] at hmem
  | cons t₀ pre =>
    -- A worker makes a request.
    simp only [List.cons_append, List.cons.injEq] at hsplit
    obtain ⟨rfl, hsplit⟩ := hsplit
    obtain ⟨l₁, l₂, rfl, rfl, hl₂⟩ := List.map_eq_append_iff.mp hsplit
    obtain ⟨stg, l₃, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp hl₂
    simp only [List.cons_append]
    cases stg with
    | start =>
      simp only [Stage.tree, lockReq, threadNext, exec, Sig.sum.elim, Exec.zoom, MutexOp.exec]
        at hmem
      split at hmem
      · simp at hmem
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        -- The mutex was free, so no worker held it; now this one does.
        have hany : (l₁ ++ Stage.start :: l₃).any Stage.inCS = false := by
          rw [← hlk]; simpa using ‹¬ s.locked = true›
        have hzero : (l₁ ++ l₃).countP Stage.inCS = 0 := by
          refine List.countP_eq_zero.mpr fun stg hstg => List.any_eq_false.mp hany stg ?_
          rcases List.mem_append.mp hstg with h | h
          · exact List.mem_append.mpr (.inl h)
          · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ h))
        refine ⟨l₁ ++ .locked :: l₃, mstage, by simp [Stage.tree], hwf, by simpa using hlen,
          by simpa [List.countP_cons, Stage.hasWritten] using hcnt, by simp [Stage.inCS], ?_, ?_,
          by simpa [List.countP_cons, Stage.hasSent] using hq⟩
        · rw [List.countP_append] at hzero
          have h₁ : l₁.countP Stage.inCS = 0 := by omega
          have h₃ : l₃.countP Stage.inCS = 0 := by omega
          simp only [List.countP_append, List.countP_cons, Stage.inCS, h₁, h₃]
          decide
        · intro v hv
          simp at hv
          exact hrd v (by simpa using hv)
    | locked =>
      simp only [Stage.tree, readReq, threadNext, exec, Sig.sum.elim, Exec.zoom, RefOp.exec,
        List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, hs', rfl⟩ := hmem
      rw [hs']
      refine ⟨l₁ ++ .read s.counter :: l₃, mstage, by simp [Stage.tree], hwf,
        by simpa using hlen, by simpa [List.countP_cons, Stage.hasWritten] using hcnt,
        by simpa [List.any_cons, Stage.inCS] using hlk,
        by simpa [List.countP_cons, Stage.inCS] using hcs, ?_,
        by simpa [List.countP_cons, Stage.hasSent] using hq⟩
      intro v hv
      simp at hv
      rcases hv with hv | rfl | hv
      · exact hrd v (by simp [hv])
      · rfl
      · exact hrd v (by simp [hv])
    | read v =>
      simp only [Stage.tree, writeReq, threadNext, exec, Sig.sum.elim, Exec.zoom, RefOp.exec,
        List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      have hv : v = s.counter := hrd v (by simp)
      refine ⟨l₁ ++ .written :: l₃, mstage, by simp [Stage.tree], hwf, by simpa using hlen, ?_,
        by simpa [List.any_cons, Stage.inCS] using hlk,
        by simpa [List.countP_cons, Stage.inCS] using hcs, ?_,
        by simpa [List.countP_cons, Stage.hasSent] using hq⟩
      · simp [List.countP_cons, Stage.hasWritten] at hcnt ⊢
        omega
      · intro v' hv'
        exfalso
        exact not_read_of_cs rfl hcs v' (by simpa using hv')
    | written =>
      simp only [Stage.tree, unlockReq, threadNext, exec, Sig.sum.elim, Exec.zoom, MutexOp.exec,
        List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      -- This worker held the mutex, so no other does; now nobody does.
      have hcs' : l₁.countP Stage.inCS = 0 ∧ l₃.countP Stage.inCS = 0 := by
        simp [List.countP_cons, Stage.inCS] at hcs
        omega
      refine ⟨l₁ ++ .unlocked :: l₃, mstage, by simp [Stage.tree], hwf, by simpa using hlen,
        by simpa [List.countP_cons, Stage.hasWritten] using hcnt, ?_, ?_, ?_,
        by simpa [List.countP_cons, Stage.hasSent] using hq⟩
      · simp [Stage.inCS, List.any_eq_false.mpr (List.countP_eq_zero.mp hcs'.1),
          List.any_eq_false.mpr (List.countP_eq_zero.mp hcs'.2)]
      · simp [Stage.inCS]; omega
      · intro v' hv'
        exfalso
        exact not_read_of_cs rfl hcs v' (by simpa using hv')
    | unlocked =>
      simp only [Stage.tree, sendReq, threadNext, exec, Sig.sum.elim, Exec.zoom, ChanOp.exec,
        List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine ⟨l₁ ++ .done :: l₃, mstage, by simp [Stage.tree], hwf, by simpa using hlen,
        by simpa [List.countP_cons, Stage.hasWritten] using hcnt,
        by simpa [List.any_cons, Stage.inCS] using hlk,
        by simpa [List.countP_cons, Stage.inCS] using hcs, ?_, ?_⟩
      · intro v hv
        simp at hv
        exact hrd v (by simpa using hv)
      · simp [List.countP_cons, Stage.hasSent] at hq ⊢
        omega
    | done => simp [Stage.tree, threadNext] at hmem

theorem Inv.reach {n : Nat} {c c' : Config Sig Shared} (h : Reach exec c c') (hc : Inv n c) :
    Inv n c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hc.step hs)

/-- In every interleaving of `main worker n`, once the main thread has returned, the counter
is `n`. -/
theorem main_result (n : Nat) {c : Config Sig Shared} (h : Reach exec (init workerTree n) c)
    {rest : List (Thread Sig Unit)} (hdone : c.threads = .pure () :: rest) :
    c.shared.counter = n := by
  obtain ⟨stages, mstage, hw, -, hlen, hcnt, -, -, -, hq⟩ := (Inv.of_init n).reach h
  rw [hdone] at hw
  simp only [List.cons.injEq] at hw
  obtain ⟨hm, -⟩ := hw
  cases mstage with
  | spawning k => simp [MainStage.tree, spawnTree] at hm
  | receiving k => simp [MainStage.tree, recvTree] at hm
  | done =>
    simp only [MainStage.spawned, MainStage.received] at hlen hq
    -- Every message has been received, so every worker has sent, so every worker has written.
    have hsent : stages.countP Stage.hasSent ≤ stages.countP Stage.hasWritten :=
      List.countP_mono_left fun stg _ h => by
        cases stg <;> simp_all [Stage.hasSent, Stage.hasWritten]
    have hwritten := List.countP_le_length (p := Stage.hasWritten) (l := stages)
    omega

/-! ## Without the mutex, an update is lost -/

/-- Every thread has returned, and the counter is not `n`. -/
def wrong (n : Nat) (c : Config Sig Shared) : Bool := c.done && c.shared.counter != n

-- The search is exhaustive for two workers: no interleaving has more than 14 requests.
#guard searchSchedule exec (wrong 2) 20 (init workerTree 2) == none

/-- info: some [0, 0, 0, 1, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval searchSchedule exec (wrong 2) 20 (init unlockedTree 2)

/-- The schedule found above. Each entry is an index into `next`, which lists one request per
thread, the main thread first: spawn both workers; the first worker reads `0`, then the second
reads `0`; the first writes `1` and sends; the main thread receives; the second writes `1` and
sends; the main thread receives and returns. -/
def losingSchedule : List Nat := [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem losingSchedule_result :
    (run exec (init unlockedTree 2) losingSchedule).map (wrong 2) = some true := by
  decide

/-- Some interleaving of two workers without the mutex ends with the counter at `1`. -/
theorem unlocked_loses_update :
    ∃ c, Reach exec (init unlockedTree 2) c ∧ wrong 2 c = true := by
  obtain ⟨c, hc, hf⟩ := Option.map_eq_some_iff.mp losingSchedule_result
  exact ⟨c, run_sound hc, hf⟩

/-! ## The same program in IO -/

/-- The runtime objects behind the resources. -/
structure Env where
  mutex : Std.BaseMutex
  counter : IO.Ref Nat
  channel : Std.Channel.Sync Unit

/-- Fresh runtime objects: the mutex free, the counter `0`, and the channel empty. -/
def Env.new : BaseIO Env := do
  return { mutex := ← Std.BaseMutex.new, counter := ← IO.mkRef 0, channel := ← Std.Channel.Sync.new }

/-- The runtime handler of the signature. -/
def handler (env : Env) : (β : Type) → Sig β → IO β :=
  Sig.sum.elim (MutexOp.io env.mutex)
    (Sig.sum.elim (RefOp.io env.counter) (ChanOp.io env.channel))

/-- The runtime never throws: every resource operation is a `BaseIO` action. -/
theorem handler_noError (env : Env) (β : Type) (op : Sig β) : NoError (handler env β op) := by
  rcases op with op | op | op <;> cases op <;> exact NoError.toIO _

/-- The program at `IO`, with the runtime handler behind its `MonadLiftT` instances. -/
@[expose] def mainIO (env : Env) (n : Nat) : IO Unit :=
  letI : MonadLiftT MutexOp IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  letI : MonadLiftT (RefOp Nat) IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  letI : MonadLiftT ChanOp IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  main (m := IO) (worker (m := IO)) n

-- The only fact about `IO` used here is `LawfulMonad IO`.
/-- The IO program is the fold of the verified request tree with the runtime handler. -/
theorem mainIO_eq (env : Env) (n : Nat) :
    mainIO env n = Freer.fold (WithSpawn.io (handler env)) (main (m := Thread Sig) workerTree n) := by
  letI : MonadLiftT MutexOp IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  letI : MonadLiftT (RefOp Nat) IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  letI : MonadLiftT ChanOp IO := ⟨fun op => handler env _ (Inj.inj op)⟩
  have hw : graph (WithSpawn.io (handler env)) workerTree (worker (m := IO)) :=
    worker.parametric (graph _) (graph_monad _) (liftRel _) (liftRel _) (liftRel _)
  exact (main.parametric (graph _) (graph_monad _) (spawnRel _) (liftRel _) _ _ hw n).symm

/-- Run the program on fresh runtime objects, then read the counter. -/
def runMain (n : Nat) : IO Nat := do
  let env ← Env.new
  mainIO env n
  env.counter.get

/-- info: 4 -/
#guard_msgs in
#eval runMain 4

#guard_uses main_result ⊇ [Inv.of_init, Inv.reach]
#guard_uses Inv.reach ⊇ [Inv.step]
#guard_uses Inv.step ⊇ [mem_next]
#guard_uses unlocked_loses_update ⊇ [run_sound, losingSchedule_result]
#guard_uses mainIO_eq ⊇ [main.parametric, worker.parametric, spawnRel, liftRel]
#guard_axioms worker.parametric, unlockedWorker.parametric, spawnAll.parametric,
  recvAll.parametric, main.parametric ⊆ []
#guard_axioms tree_main, Inv.of_init, losingSchedule_result, unlocked_loses_update
  ⊆ [propext, Quot.sound]
-- `Classical.choice` enters `mainIO_eq` through the runtime operations that `handler` calls.
#guard_axioms mainIO_eq, handler_noError ⊆ [propext, Classical.choice, Quot.sound]
-- `Classical.choice` enters `Inv.step` through `List.countP_eq_zero`.
#guard_axioms Inv.step, Inv.reach, main_result ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Concurrency.Counter
