module

public import Tapas

public section

/-!
A Lean-only adapter for *ghost state*: a program performs ghost updates, and the ghost
state is then kept, re-represented, or dropped by choosing an interpretation of one
capability. The relations connect those choices.

The capability names an alphabet `I` of **ghost updates**, not a representation. Each
interpretation gives the alphabet a meaning in its own representation, and the
**representation stays out of the interface**, which is what lets two interpretations
disagree about it, one threading an opaque counter and the other an ordinary number.
-/

namespace TapasTest.Applications.Monad.Ghost.Basic

open Tapas.Parametricity Tapas.LogicalRelation

class MonadGhostOf (I : Type u) (m : Type u → Type v) where
  ghost : I → m PUnit.{u + 1}

class GhostUpdateStep (I σ : Type u) where
  step : I → σ → σ

derive_effect_rel MonadGhostOf

section Interpretations

variable {I σ τ : Type u} {m : Type u → Type v} [Monad m]

/-- Keep the ghost state in the state monad. -/
instance stateGhost [inst : GhostUpdateStep I σ] : MonadGhostOf I (StateT σ m) where
  ghost i := fun s => pure (⟨⟩, inst.step i s)

instance (priority := low) erasedGhost : MonadGhostOf I m where
  ghost _ := pure ⟨⟩

end Interpretations

/-! ## Erasure: the ghost state is invisible to the result -/

section Erase

/-- The instrumented run returns the same value, from every initial ghost state. -/
@[expose] def Erase (σ : Type u) (m : Type u → Type v) [Monad m] : ComputationRelation (StateT σ m) m := fun {_} withGhost noGhost =>
  ∀ s, Prod.fst <$> withGhost s = noGhost

variable {σ : Type u} {m : Type u → Type v} [Monad m]

variable [LawfulMonad m]

theorem Erase.pure_rel {α : Type u} (a : α) :
    Erase σ m (pure a) (pure a) := by
  intro s
  show Prod.fst <$> (pure (a, s) : m _) = pure a
  rw [map_pure]

theorem Erase.bind_rel {α β : Type u} {x : StateT σ m α} {y : m α}
    {f : α → StateT σ m β} {g : α → m β}
    (hxy : Erase σ m x y) (hfg : ∀ a, Erase σ m (f a) (g a)) : Erase σ m (x >>= f) (y >>= g) := by
  intro s
  show Prod.fst <$> (x s >>= fun p => f p.1 p.2) = y >>= g
  rw [map_bind, ← hxy s, bind_map_left]
  exact bind_congr (fun p => hfg p.1 p.2)

theorem Erase.monadRel :
    Monad.Rel (Erase σ m) :=
  Monad.Rel.ofPureBind _ Erase.pure_rel Erase.bind_rel

/-- Every state interpretation erases, whatever its updates do to the ghost state. -/
theorem Erase.ghostRel {I : Type u} [GhostUpdateStep I σ] :
    MonadGhostOf.Rel (I := I) (Erase σ m) :=
  MonadGhostOf.Rel.mk _
    (ghost := fun i => by
      intro s
      show Prod.fst <$> (pure (PUnit.unit, GhostUpdateStep.step i s) : m _) = pure PUnit.unit
      rw [map_pure])

omit [LawfulMonad m] in
/-- The semantic reading of a certificate: instrumentation does not change the result. -/
theorem Erase.run_eq {α : Type u} {withGhost : StateT σ m α} {noGhost : m α}
    (h : Erase σ m withGhost noGhost) (s : σ) : Prod.fst <$> withGhost s = noGhost :=
  h s

end Erase

/-! ## Reindexing: the ghost state may be represented differently

`Reindex shift` relates two instrumented runs whose ghost state is represented differently
and read off by `shift`.
-/

section Reindex

/-- Same value, and ghost states that agree under `shift`, from every initial state. -/
@[expose] def Reindex (shift : σ → τ) (m : Type u → Type v) [Monad m] : ComputationRelation (StateT σ m) (StateT τ m) :=
  fun {_} left right =>
    ∀ s, (fun p => (p.1, shift p.2)) <$> left s = right (shift s)

variable {σ τ : Type u} {m : Type u → Type v} [Monad m] (shift : σ → τ)

variable [LawfulMonad m]

theorem Reindex.pure_rel {α : Type u} (a : α) :
    Reindex shift m (pure a) (pure a) := by
  intro s
  show (fun p => (p.1, shift p.2)) <$> (pure (a, s) : m _) = pure (a, shift s)
  rw [map_pure]

theorem Reindex.bind_rel {α β : Type u} {x : StateT σ m α} {y : StateT τ m α}
    {f : α → StateT σ m β} {g : α → StateT τ m β}
    (hxy : Reindex shift m x y) (hfg : ∀ a, Reindex shift m (f a) (g a)) :
    Reindex shift m (x >>= f) (y >>= g) := by
  intro s
  show (fun p => (p.1, shift p.2)) <$> (x s >>= fun p => f p.1 p.2)
      = y (shift s) >>= fun q => g q.1 q.2
  rw [map_bind, ← hxy s, bind_map_left]
  exact bind_congr (fun p => hfg p.1 p.2)

theorem Reindex.monadRel :
    Monad.Rel (Reindex shift m) :=
  Monad.Rel.ofPureBind _ (Reindex.pure_rel shift) (Reindex.bind_rel shift)

theorem Reindex.ghostRel {I : Type u}
    [leftStep : GhostUpdateStep I σ] [rightStep : GhostUpdateStep I τ]
    (hstep : ∀ i s, shift (leftStep.step i s) = rightStep.step i (shift s)) :
    MonadGhostOf.Rel (I := I) (Reindex shift m) :=
  MonadGhostOf.Rel.mk _
    (ghost := fun i => by
      intro s
      show (fun p => (p.1, shift p.2)) <$> (pure (PUnit.unit, leftStep.step i s) : m _)
          = pure (PUnit.unit, rightStep.step i (shift s))
      rw [map_pure, hstep])

omit [LawfulMonad m] in
/-- The semantic reading of a certificate: the two runs agree on the result, and on the
ghost state once `shift` has read it. -/
theorem Reindex.run_eq {α : Type u} {left : StateT σ m α} {right : StateT τ m α}
    (h : Reindex shift m left right) (s : σ) :
    (fun p => (p.1, shift p.2)) <$> left s = right (shift s) :=
  h s

end Reindex

/-! ## Partial fixpoints

`derive_parametric` asks for `AdmissibleRel` when the program is defined by
`partial_fixpoint` (a `while` loop written with `infer_effects_partial%`, for instance). The
premise holds for `Erase` over a base monad with a flat order, which is where such programs
can be interpreted at all: `Id` has no uniform `CCPO`, so a looping program is erased into
`Option` rather than into `Id`.
-/

open Lean.Order in
theorem flat_erase {ι : Sort u} {α : Sort v} {β : Sort w} {b : α} {b' : β}
    (φ : α → β) (hbot : ∀ x : α, φ x = b' ↔ x = b) :
    AdmissibleRel (fun (f : ι → FlatOrder b) (y : FlatOrder b') => ∀ i, φ (f i) = y) :=
  AdmissibleRel.flat_sync (fun _ => (hbot b).mpr rfl) (fun _ _ h i => by rw [← h i]; exact hbot _)

theorem Erase.admissible {σ α : Type u} :
    AdmissibleRel ((Erase σ Option) (α := α)) :=
  flat_erase (fun x => Prod.fst <$> x) (fun x => by cases x <;> simp)

end TapasTest.Applications.Monad.Ghost.Basic
