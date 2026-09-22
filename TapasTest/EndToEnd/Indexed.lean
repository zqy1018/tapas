module

public import TapasTest.TestingUtils

public section

open TaglessFinal Tapas.LogicalRelation Tapas.Parametricity
universe u v w

namespace TapasTest.EndToEnd.Indexed

class IndexedAtom {I : Sort u} (repr : I → Type v) where
  atom (i : I) : repr i

derive_interface_rel IndexedAtom (repr := repr)

def indexedAtom {I : Sort u} (i : I) :=
  infer_final% (repr : I → Type v) => IndexedAtom.atom (repr := repr) i

derive_parametric indexedAtom (repr := repr)

example {I : Sort u} {repr : I → Type v} {repr' : I → Type w}
    (R : IndexedRelation repr repr') [IndexedAtom repr] [IndexedAtom repr']
    (h : IndexedAtom.Rel R) (i : I) :
    R (indexedAtom i (repr := repr)) (indexedAtom i (repr := repr')) :=
  indexedAtom.parametric i R h

inductive Ty where
  | nat
  | arrow : Ty → Ty → Ty

class Language (repr : Ty → Type u) where
  lit : Nat → repr .nat
  add : repr .nat → repr .nat → repr .nat
  lam {a b} : (repr a → repr b) → repr (.arrow a b)
  app {a b} : repr (.arrow a b) → repr a → repr b

derive_interface_rel Language (repr := repr)

example {repr : Ty → Type u} {repr' : Ty → Type v}
    (R : IndexedRelation repr repr') [left : Language repr] [right : Language repr']
    [Language.Rel R] {a b} (f : repr a → repr b) (g : repr' a → repr' b)
    (h : ∀ x y, R x y → R (f x) (g y)) :
    R (left.lam f) (right.lam g) := Language.Rel.lam f g h

@[expose] def double := infer_final% (repr : Ty → Type u) =>
  Language.lam (repr := repr) (fun x => Language.add x x)

example : {repr : Ty → Type u} → [Language repr] → repr (.arrow .nat .nat) := @double

derive_parametric double (repr := repr)

@[expose] def six := infer_final% (repr : Ty → Type u) =>
  Language.app (repr := repr) double (Language.lit 3)

derive_parametric six (repr := repr)

@[expose] def Eval : Ty → Type
  | .nat => Nat
  | .arrow a b => Eval a → Eval b

instance : Language Eval where
  lit := id
  add := Nat.add
  lam f := f
  app f x := f x

#guard Nat.beq (six (repr := Eval)) 6

-- A second interpretation wraps every semantic value, including function values.
@[expose] def Wrapped (t : Ty) := ULift.{0} (Eval t)

instance : Language Wrapped where
  lit n := ⟨n⟩
  add x y := ⟨Nat.add x.down y.down⟩
  lam f := ⟨fun x => (f ⟨x⟩).down⟩
  app f x := ⟨f.down x.down⟩

@[expose] def unwrapRelation : IndexedRelation Wrapped Eval := fun {_} x y => x.down = y

abbrev unwrapCompatible : Language.Rel unwrapRelation where
  lit _ := rfl
  add _ _ hx _ _ hy := by cases hx; cases hy; rfl
  lam f g h := by
    funext x
    exact h ⟨x⟩ x rfl
  app _ _ hf _ _ hx := by cases hf; cases hx; rfl

theorem six_correct : (six (repr := Wrapped)).down = six (repr := Eval) :=
  six.parametric unwrapRelation unwrapCompatible

#guard Nat.beq (six (repr := Wrapped)).down 6

example {repr : Ty → Type u} {repr' : Ty → Type v}
    (R : IndexedRelation repr repr') [left : Language repr] [right : Language repr']
    [Language.Rel R] {a b} (f : repr (.arrow a b)) (g : repr' (.arrow a b))
    (hf : R f g) (x : repr a) (y : repr' a) (hx : R x y) :
    R (left.app f x) (right.app g y) := Language.Rel.app f g hf x y hx

abbrev Final (t : Ty) := {repr : Ty → Type u} → [Language repr] → repr t

derive_type_rel Final (repr := repr)

example : Final.Rel.{u,v} (@six) (@six) := by
  intro repr repr' R left right h
  exact six.parametric R h

/-! ## Branching and recursion over an indexed representation

The same control flow `Carrier.lean` runs over a plain carrier, run over `repr : Ty → Type`.
The interesting difference is the index: as long as every branch lands at the *same* index,
the proof is the carrier proof; when the index is computed from the discriminant, it is not.
-/

def pick (b : Bool) := infer_final% (repr : Ty → Type u) =>
  if b then Language.lit (repr := repr) 1
  else Language.add (Language.lit (repr := repr) 1) (Language.lit 2)

derive_parametric pick (repr := repr)

def fromOption (x : Option Nat) := infer_final% (repr : Ty → Type u) =>
  match x with
  | some n => Language.lit (repr := repr) n
  | none => Language.add (Language.lit (repr := repr) 0) (Language.lit 0)

derive_parametric fromOption (repr := repr)

-- The declared result type supplies the expected type for a bare `casesOn` while
-- `infer_final` infers the interface. It is recognised as a branch just the same.
infer_final (repr : Ty → Type u)
def viaCasesOn (b : Bool) : repr .nat :=
  Bool.casesOn b (Language.lit 0) (Language.lit 1)

derive_parametric viaCasesOn (repr := repr)

-- Structural recursion building a term of unbounded size at one index.
infer_final (repr : Ty → Type u)
def iterate : Nat → repr .nat
  | 0 => Language.lit 0
  | n + 1 => Language.add (Language.lit 1) (iterate n)

derive_parametric iterate (repr := repr)

example {repr : Ty → Type u} {repr' : Ty → Type v} (R : IndexedRelation repr repr')
    [Language repr] [Language repr'] (h : Language.Rel R) (n : Nat) :
    R (iterate (repr := repr) n) (iterate (repr := repr') n) := iterate.parametric R h n

-- An index need not be a literal: it may be any expression that reduces to one.
def tyOf : Bool → Ty
  | true => .nat
  | false => .arrow .nat .nat

infer_final (repr : Ty → Type u)
def fixedByFun : repr (tyOf true) := Language.lit 3

derive_parametric fixedByFun (repr := repr)

/-! ### An index computed from the discriminant

When the result index varies with the branch, the relational premise for an operation is
stated at the index that operation returns (`lit` at `.nat`), while the branch's goal
carries the index as written (`tyOf true`). Closing the branch means reducing one to the
other, and the proof search does that at reducible transparency only. So an index function
has to be an `abbrev` or carry `@[reducible]`; a plain `def` stops the search at the first
operation. The same holds when the index recurses along with the program.
-/

abbrev tyAt : Bool → Ty
  | true => .nat
  | false => .arrow .nat .nat

infer_final (repr : Ty → Type u)
def atIndex (b : Bool) : repr (tyAt b) :=
  match b with
  | true => Language.lit 3
  | false => Language.lam (fun x => x)

derive_parametric atIndex (repr := repr)

example {repr : Ty → Type u} {repr' : Ty → Type v} (R : IndexedRelation repr repr')
    [Language repr] [Language repr'] (h : Language.Rel R) (b : Bool) :
    R (atIndex (repr := repr) b) (atIndex (repr := repr') b) := atIndex.parametric R h b

abbrev arrows : Nat → Ty
  | 0 => .nat
  | n + 1 => .arrow .nat (arrows n)

infer_final (repr : Ty → Type u)
def constFn : (n : Nat) → repr (arrows n)
  | 0 => Language.lit 0
  | n + 1 => Language.lam (fun _ => constFn n)

derive_parametric constFn (repr := repr)

-- The same program over the irreducible `tyOf` is rejected, naming the operation whose
-- premise could not be brought to the branch's index.
infer_final (repr : Ty → Type u)
def atIndexOpaque (b : Bool) : repr (tyOf b) :=
  match b with
  | true => Language.lit 3
  | false => Language.lam (fun x => x)

/--
error: parametricity: no applicable translation for TapasTest.EndToEnd.Indexed.Language.lit; use `derive_parametric TapasTest.EndToEnd.Indexed.Language.lit` or `attribute [parametric] theoremName`
-/
#guard_msgs in
derive_parametric atIndexOpaque (repr := repr)

-- It is provable by hand, so the limit is the transparency the search reduces at, not the
-- statement: `exact` closes each branch after an ordinary `cases`.
example {repr : Ty → Type u} {repr' : Ty → Type v} (R : IndexedRelation repr repr')
    [Language repr] [Language repr'] (h : Language.Rel R) (b : Bool) :
    R (atIndexOpaque (repr := repr) b) (atIndexOpaque (repr := repr') b) := by
  cases b
  · exact h.lam _ _ (fun x y hxy => hxy)
  · exact h.lit 3

#guard_no_parametric atIndexOpaque

#guard_axioms double.parametric, six.parametric, pick.parametric, fromOption.parametric,
  viaCasesOn.parametric, iterate.parametric, fixedByFun.parametric, atIndex.parametric,
  constFn.parametric ⊆ []

#guard_axioms six_correct ⊆ [propext, Quot.sound]

end TapasTest.EndToEnd.Indexed
