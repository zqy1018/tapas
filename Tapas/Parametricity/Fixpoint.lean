import Init.Internal.Order.Basic

/-!
Relational least-fixpoint induction. The orders are the actual CCPO instances
used by `Lean.Order.fix`; no monad structure or continuity of the functionals
is required.
-/

namespace Tapas.Parametricity

open Lean.Order Lean.Order.PartialOrder

/-- A relation closed under suprema of chains of related pairs. Lean includes
the empty chain in admissibility, so this also requires related bottom values. -/
def AdmissibleRel {α : Sort u} {β : Sort v} [CCPO α] [CCPO β]
    (R : α → β → Prop) : Prop :=
  admissible (fun p : α ×' β => R p.1 p.2)

namespace AdmissibleRel

/-- The empty-chain case of relational admissibility. -/
theorem bot {α : Sort u} {β : Sort v} [CCPO α] [CCPO β]
    {R : α → β → Prop} (h : AdmissibleRel R) : R ⊥ ⊥ := by
  have hp := h (empty_chain (α ×' β)) (chain_empty _) (fun _ h => False.elim h)
  change R (⊥ : α ×' β).1 (⊥ : α ×' β).2 at hp
  have hb : (⊥ : α ×' β) = ⟨⊥, ⊥⟩ :=
    rel_antisymm (bot_le _) ⟨bot_le _, bot_le _⟩
  simpa only [hb] using hp

/-- Equality is admissible for every CCPO. -/
theorem eq {α : Sort u} [CCPO α] : AdmissibleRel (@Eq α) := by
  intro c hc h
  rw [← prod_csup_eq]
  apply rel_antisymm
  · apply csup_le (PProd.chain.chain_fst hc)
    rintro a ⟨b, hab⟩
    have heq : a = b := h ⟨a, b⟩ hab
    rw [heq]
    exact le_csup (PProd.chain.chain_snd hc) ⟨a, hab⟩
  · apply csup_le (PProd.chain.chain_snd hc)
    rintro b ⟨a, hab⟩
    have heq : a = b := h ⟨a, b⟩ hab
    rw [← heq]
    exact le_csup (PProd.chain.chain_fst hc) ⟨b, hab⟩

private def evalChain {ι : Sort u} {κ : Sort v} {α : ι → Sort w} {β : κ → Sort z}
    (c : ((∀ i, α i) ×' (∀ j, β j)) → Prop) (i : ι) (j : κ) : α i ×' β j → Prop :=
  fun p => ∃ f, c f ∧ PProd.mk (f.1 i) (f.2 j) = p

private theorem chain_eval {ι : Sort u} {κ : Sort v} {α : ι → Sort w} {β : κ → Sort z}
    [∀ i, CCPO (α i)] [∀ j, CCPO (β j)]
    {c : ((∀ i, α i) ×' (∀ j, β j)) → Prop} (hc : chain c) (i : ι) (j : κ) :
    chain (evalChain c i j) := by
  rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  rcases hc f g hf hg with h | h
  · exact Or.inl ⟨h.1 i, h.2 j⟩
  · exact Or.inr ⟨h.1 i, h.2 j⟩

private theorem csup_eval {ι : Sort u} {κ : Sort v} {α : ι → Sort w} {β : κ → Sort z}
    [∀ i, CCPO (α i)] [∀ j, CCPO (β j)]
    {c : ((∀ i, α i) ×' (∀ j, β j)) → Prop} (hc : chain c) (i : ι) (j : κ) :
    PProd.mk ((CCPO.csup hc).1 i) ((CCPO.csup hc).2 j) = CCPO.csup (chain_eval hc i j) := by
  rw [← prod_csup_eq]
  dsimp only [prod_csup]
  rw [← fun_csup_eq, ← fun_csup_eq]
  apply is_sup_unique ?_ (CCPO.csup_spec _)
  intro p
  constructor
  · rintro ⟨hl, hr⟩ _ ⟨f, hf, rfl⟩
    exact ⟨rel_trans (le_csup (chain_apply (PProd.chain.chain_fst hc) i)
        ⟨f.1, ⟨f.2, hf⟩, rfl⟩) hl,
      rel_trans (le_csup (chain_apply (PProd.chain.chain_snd hc) j)
        ⟨f.2, ⟨f.1, hf⟩, rfl⟩) hr⟩
  · intro h
    constructor
    · apply csup_le (chain_apply (PProd.chain.chain_fst hc) i)
      rintro _ ⟨f, ⟨g, hfg⟩, rfl⟩
      exact (h ⟨f i, g j⟩ ⟨⟨f, g⟩, hfg, rfl⟩).1
    · apply csup_le (chain_apply (PProd.chain.chain_snd hc) j)
      rintro _ ⟨g, ⟨f, hfg⟩, rfl⟩
      exact (h ⟨f i, g j⟩ ⟨⟨f, g⟩, hfg, rfl⟩).2

/-- Lift admissibility to functions sending related arguments to related results.
The argument relation is fixed; the result families may be dependent and heterogeneous. -/
theorem pi {ι : Sort u} {κ : Sort v} {α : ι → Sort w} {β : κ → Sort z}
    [∀ i, CCPO (α i)] [∀ j, CCPO (β j)]
    {S : ι → κ → Prop} {R : ∀ i j, α i → β j → Prop}
    (h : ∀ i j, S i j → AdmissibleRel (R i j)) :
    AdmissibleRel (fun (f : ∀ i, α i) (g : ∀ j, β j) =>
      ∀ i j, S i j → R i j (f i) (g j)) := by
  intro c hc hfg i j hij
  have hp := h i j hij (evalChain c i j) (chain_eval hc i j) (by
    rintro _ ⟨f, hf, rfl⟩
    exact hfg f hf i j hij)
  simpa only [← csup_eval hc i j] using hp

/-- Pointwise lifting with shared arguments, as used by program translations. -/
theorem pointwise {ι : Sort u} {α : ι → Sort v} {β : ι → Sort w}
    [∀ i, CCPO (α i)] [∀ i, CCPO (β i)]
    {R : ∀ i, α i → β i → Prop} (h : ∀ i, AdmissibleRel (R i)) :
    AdmissibleRel (fun (f : ∀ i, α i) (g : ∀ i, β i) => ∀ i, R i (f i) (g i)) := by
  intro c hc hfg i
  have hp := h i (evalChain c i i) (chain_eval hc i i) (by
    rintro _ ⟨f, hf, rfl⟩
    exact hfg f hf i)
  simpa only [← csup_eval hc i i] using hp

end AdmissibleRel

private theorem fix_le_of_le {α : Sort u} [CCPO α] {f : α → α}
    (hf : monotone f) {x : α} (hx : f x ⊑ x) : fix f hf ⊑ x := by
  apply fix_induct hf (fun y => y ⊑ x)
  · intro c hc h
    exact csup_le hc h
  · intro y hy
    exact rel_trans (hf _ _ hy) hx

private theorem fix_pair {α : Sort u} {β : Sort v} [CCPO α] [CCPO β]
    {f : α → α} {g : β → β} (hf : monotone f) (hg : monotone g) :
    fix (fun p : α ×' β => PProd.mk (f p.1) (g p.2))
      (by intro x y h; exact ⟨hf _ _ h.1, hg _ _ h.2⟩) = ⟨fix f hf, fix g hg⟩ := by
  let F := fun p : α ×' β => PProd.mk (f p.1) (g p.2)
  have hF : monotone F := fun _ _ h => ⟨hf _ _ h.1, hg _ _ h.2⟩
  change fix F hF = _
  apply rel_antisymm
  · apply fix_le_of_le hF
    exact ⟨rel_of_eq (fix_eq hf).symm, rel_of_eq (fix_eq hg).symm⟩
  · have heq := fix_eq hF
    exact ⟨fix_le_of_le hf (rel_of_eq (congrArg PProd.fst heq).symm),
      fix_le_of_le hg (rel_of_eq (congrArg PProd.snd heq).symm)⟩

/-- Related monotone functionals have related least fixpoints when their
relation is admissible on the product order. -/
theorem fix_rel {α : Sort u} {β : Sort v} [CCPO α] [CCPO β]
    {R : α → β → Prop} {f : α → α} {g : β → β}
    (hf : monotone f) (hg : monotone g) (hadm : AdmissibleRel R)
    (hstep : ∀ x y, R x y → R (f x) (g y)) :
    R (fix f hf) (fix g hg) := by
  have h := fix_induct
    (f := fun p : α ×' β => PProd.mk (f p.1) (g p.2))
    (by intro x y h; exact ⟨hf _ _ h.1, hg _ _ h.2⟩)
    (fun p => R p.1 p.2) hadm (fun p hp => hstep p.1 p.2 hp)
  simpa only [fix_pair hf hg] using h

end Tapas.Parametricity
