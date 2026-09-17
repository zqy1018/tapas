import Tapas.Applications.Monad.CommonMonadRelations
import Tapas.Parametricity.Program

/-!
Translations for the standard library's loops and monadic traversals, so that a `for` loop
or a `mapM` in a derived program needs nothing of its own.

These are ordinary recursive definitions, so they are derived here exactly as a user would
derive them, helper first. They are registered under names of this module's own, never as
`List.forIn'.parametric`: the registry keys a rule by the constant its conclusion relates
and never by the theorem's name, so nothing is lost, and a user who wants
`derive_parametric List.forIn'` of their own still has that name free.

NOTE: Two do not fit that pattern, both because they recurse through a *private* helper that no
`derive_parametric` invocation can name.

* `Std.Legacy.Range.forIn'` is written out below and reduced to the list loop. It serves
  only the legacy `[0:k]` spelling; `[0...k]` and `[0...=k]` iterate through a list, so
  they are carried by `listForIn'Rel` already and need nothing of their own. This is the
  one hand-written rule left here, and its lifetime is that of `Std.Legacy.Range`.
* `Array.mapM` is not shipped. The same route is available in principle — it rewrites to
  `List.mapM` or to `Array.foldlM` — but both rewrites assume `LawfulMonad`, and of *both*
  interpretations, which a translation applied to an arbitrary pair of related monads
  cannot supply. A program that uses it must relate it under its own lawfulness premises.
-/

namespace Tapas.Parametricity.StdLoops

open Tapas.LogicalRelation

/-! ## `for` loops -/

derive_parametric List.forIn'.loop as listForIn'LoopRel (repr := m)
derive_parametric List.forIn' as listForIn'Rel (repr := m)

derive_parametric Array.forIn'.loop as arrayForIn'LoopRel (repr := m)
derive_parametric Array.forIn' as arrayForIn'Rel (repr := m)

/-- A legacy range loop is a list loop over `List.range'`, so it inherits the list
translation. The current range syntax reaches `List.forIn'` on its own. -/
@[parametric] theorem rangeForIn'Rel {β : Type u} {m : Type u → Type v} [instMonad : Monad m]
    (r : Std.Legacy.Range) (init : β) (f : (i : Nat) → i ∈ r → β → m (ForInStep β))
    {m' : Type u → Type w} (R : ComputationRelation m m') [inst' : Monad m']
    (hm : Monad.Rel R instMonad inst')
    (f' : (i : Nat) → i ∈ r → β → m' (ForInStep β))
    (hf : ∀ i h b, R (f i h b) (f' i h b)) :
    R (Std.Legacy.Range.forIn' r init f) (Std.Legacy.Range.forIn' r init f') := by
  show R (forIn' r init f) (forIn' r init f')
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range' r init f,
      Std.Legacy.Range.forIn'_eq_forIn'_range' r init f']
  exact listForIn'Rel _ _ _ R hm _ (fun a h b => hf a _ b)

/-! ## Monadic traversals -/

derive_parametric List.mapM.loop as listMapMLoopRel
derive_parametric List.mapM as listMapMRel

derive_parametric List.forM as listForMRel
derive_parametric List.foldlM as listFoldlMRel
derive_parametric List.foldrM as listFoldrMRel

derive_parametric List.filterAuxM as listFilterAuxMRel
derive_parametric List.filterM as listFilterMRel

derive_parametric List.filterMapM.loop as listFilterMapMLoopRel
derive_parametric List.filterMapM as listFilterMapMRel

derive_parametric Array.foldlM.loop as arrayFoldlMLoopRel (repr := m)
derive_parametric Array.foldlM as arrayFoldlMRel (repr := m)
derive_parametric Array.forM as arrayForMRel (repr := m)

end Tapas.Parametricity.StdLoops
