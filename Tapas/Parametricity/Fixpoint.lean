import Init.Internal.Order.Basic

/-!
This module defines `AdmissibleRel` for relations closed under suprema of chains
of related pairs. It proves admissibility for equality, provides function
relation constructions via `AdmissibleRel.pi` and `AdmissibleRel.pointwise`, and covers the
one-sided case of a function into a flat order with `AdmissibleRel.flat_sync`.
The theorem `fix_rel` shows that two monotone functionals preserving an admissible
relation have least fixpoints related by that same relation.
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

private theorem flat_rel_cases {α : Sort u} {b : α} {x y : FlatOrder b}
    (h : x ⊑ y) : x = b ∨ x = y := by
  cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Admissibility when the left side is a function into a flat order and the right side is
a single flat-order value. Neither `pi` nor `pointwise` applies, since only one side is a
function.

`hsync` is what makes this work. A chain in a flat order has a maximum, so its supremum is
one of its own members, and a relation closed on the members is closed on the supremum. A
chain of *functions* need not have one, since different arguments may become defined at
different stages. Requiring the two sides to be defined together removes that: the function
side is defined everywhere or nowhere, so the chain of pairs has a maximum again. -/
theorem flat_sync {ι : Sort u} {α : Sort v} {β : Sort w} {b : α} {b' : β}
    {R : (ι → FlatOrder b) → FlatOrder b' → Prop}
    (hbot : R (fun _ => b) b')
    (hsync : ∀ f y, R f y → ∀ i, (y = b' ↔ f i = b)) :
    AdmissibleRel R := by
  intro c hc h
  rw [← prod_csup_eq]
  show R (CCPO.csup (PProd.chain.chain_fst hc)) (CCPO.csup (PProd.chain.chain_snd hc))
  by_cases hdef : ∃ p, c p ∧ p.2 ≠ b'
  · -- Some member is already defined; being defined makes it the maximum of the chain.
    obtain ⟨p, hp, hp2⟩ := hdef
    have hp1 : ∀ j, p.1 j ≠ b := fun j hj => hp2 ((hsync _ _ (h p hp) j).mpr hj)
    have hmax : ∀ q, c q → q.1 ⊑ p.1 ∧ q.2 ⊑ p.2 := by
      intro q hq
      rcases hc q p hq hp with hle | hle
      · exact hle
      · refine ⟨fun j => ?_, ?_⟩
        · rcases flat_rel_cases (hle.1 j) with he | he
          · exact absurd he (hp1 j)
          · rw [he]; exact rel_refl
        · rcases flat_rel_cases hle.2 with he | he
          · exact absurd he hp2
          · rw [he]; exact rel_refl
    rw [rel_antisymm (csup_le (PProd.chain.chain_fst hc) (fun a ⟨y, hay⟩ => (hmax ⟨a, y⟩ hay).1))
          (le_csup (PProd.chain.chain_fst hc) ⟨p.2, hp⟩),
        rel_antisymm (csup_le (PProd.chain.chain_snd hc) (fun y ⟨a, hay⟩ => (hmax ⟨a, y⟩ hay).2))
          (le_csup (PProd.chain.chain_snd hc) ⟨p.1, hp⟩)]
    exact h p hp
  · -- Nothing in the chain is defined yet, so both suprema are the bottom element.
    have hundef : ∀ p, c p → p.2 = b' :=
      fun p hp => Classical.byContradiction (fun hne => hdef ⟨p, hp, hne⟩)
    have hbot1 : ∀ q, c q → q.1 ⊑ (fun _ => b) := by
      intro q hq j
      have hj : q.1 j = b := (hsync _ _ (h q hq) j).mp (hundef q hq)
      show q.1 j ⊑ b
      rw [hj]
      exact rel_refl
    have hbot2 : ∀ q, c q → q.2 ⊑ b' := by
      intro q hq
      rw [hundef q hq]
      exact rel_refl
    rw [rel_antisymm (csup_le (PProd.chain.chain_fst hc) (fun a ⟨y, hay⟩ => hbot1 ⟨a, y⟩ hay))
          (fun _ => FlatOrder.rel.bot),
        rel_antisymm (csup_le (PProd.chain.chain_snd hc) (fun y ⟨a, hay⟩ => hbot2 ⟨a, y⟩ hay))
          FlatOrder.rel.bot]
    exact hbot

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
