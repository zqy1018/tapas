module

public import TapasTest.TestingUtils

public section

open TaglessFinal Tapas.LogicalRelation Tapas.Parametricity
universe u v w

namespace TapasTest.EndToEnd.Carrier

class Arith (A : Type u) where
  lit : Nat → A
  add : A → A → A

derive_interface_rel Arith (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [left : Arith A] [right : Arith B] [Arith.Rel R] (n : Nat) :
    R (left.lit n) (right.lit n) := Arith.Rel.lit n

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [left : Arith A] [right : Arith B] [Arith.Rel R]
    {x y : A} {x' y' : B} (hx : R x x') (hy : R y y') :
    R (left.add x y) (right.add x' y') := Arith.Rel.add x x' hx y y' hy

@[expose] def expression := infer_final% (A : Type u) =>
  Arith.add (A := A) (Arith.lit 1) (Arith.lit 2)

-- Repeated uses of the same interface yield just one instance binder.
example : {A : Type u} → [Arith A] → A := @expression

derive_parametric expression (repr := A)

-- A handwritten definition uses exactly the same proof path.
@[expose] def twice {A : Type u} [Arith A] : A :=
  let x := expression
  Arith.add x x

derive_parametric twice (repr := A)

infer_final (A : Type u)
def sumTo : Nat → A
  | 0 => Arith.lit 0
  | n + 1 => Arith.add (Arith.lit (n + 1)) (sumTo n)

derive_parametric sumTo (repr := A)

-- Branching over a carrier, not just over a monad. A bare `casesOn` is recognised
-- as a branch but `split` declines to eliminate it, so the shared discriminant is
-- destructed instead and the selected branch reduces away.
infer_final (A : Type u)
def pick (b : Bool) : A :=
  if b then Arith.lit 1 else Arith.add (Arith.lit 1) (Arith.lit 2)

derive_parametric pick (repr := A)

infer_final (A : Type u)
def fromOption (x : Option Nat) : A :=
  match x with
  | some n => Arith.lit n
  | none => Arith.lit 0

derive_parametric fromOption (repr := A)

infer_final (A : Type u)
def viaCasesOn (b : Bool) : A :=
  Bool.casesOn b (Arith.lit 0) (Arith.lit 1)

derive_parametric viaCasesOn (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Arith A] [Arith B] (h : Arith.Rel R) (b : Bool) :
    R (viaCasesOn (A := A) b) (viaCasesOn (A := B) b) := viaCasesOn.parametric R h b

-- Proof generation uses the relation of a handwritten interface, which has to have
-- been generated already: it is never derived on the spot.
class Atom (A : Type u) where
  atom : A

derive_interface_rel Atom (repr := A)

infer_final (A : Type u)
def atomProgram : A := Atom.atom

derive_parametric atomProgram (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Atom A] [Atom B] (h : Atom.Rel R) :
    R (atomProgram (A := A)) (atomProgram (A := B)) := atomProgram.parametric R h

inductive Syntax where
  | lit : Nat → Syntax
  | add : Syntax → Syntax → Syntax
  deriving Repr, BEq

instance : Arith Syntax := ⟨Syntax.lit, Syntax.add⟩
instance : Arith Nat := ⟨id, Nat.add⟩
instance : Arith String := ⟨toString, fun x y => s!"({x} + {y})"⟩

@[expose] def evaluate : Syntax → Nat
  | .lit n => n
  | .add x y => evaluate x + evaluate y

abbrev evaluationRelation : Arith.Rel (fun (x : Syntax) (y : Nat) => evaluate x = y) where
  lit _ := rfl
  add _ _ hx _ _ hy := by cases hx; cases hy; rfl

-- Instantiate a generated theorem with a graph relation: reification preserves meaning.
theorem expression_correct : evaluate (expression (A := Syntax)) = expression (A := Nat) :=
  expression.parametric (fun x y => evaluate x = y) evaluationRelation

theorem twice_correct : evaluate (twice (A := Syntax)) = twice (A := Nat) :=
  twice.parametric (fun x y => evaluate x = y) evaluationRelation

#guard expression (A := Nat) == 3
#guard expression (A := String) == "(1 + 2)"
#guard expression (A := Syntax) == .add (.lit 1) (.lit 2)
#guard twice (A := Nat) == 6
#guard sumTo (A := Nat) 4 == 10

abbrev Final := {A : Type u} → [Arith A] → A

derive_type_rel Final (repr := A)

example : Final.Rel.{u, v} (@expression) (@expression) := by
  intro A B R left right h
  exact expression.parametric R h

-- Ordinary type parameters remain shared, even when they have the same kind as A.
abbrev WithInput (X : Type u) := {A : Type v} → [Arith A] → (X → A) → X → A

derive_type_rel WithInput (repr := A)

example {X : Type u} (p : WithInput.{u,v} X) (q : WithInput.{u,w} X) :
    WithInput.Rel p q ↔
      ∀ {A : Type v} {B : Type w} (R : A → B → Prop) [Arith A] [Arith B],
        Arith.Rel R → ∀ (f : X → A) (g : X → B),
      (∀ x, R (f x) (g x)) → ∀ x, R (p f x) (q g x) := Iff.rfl

-- A later type constructor is shared; explicit selection does not revert to
-- automatically relating all binders of monadic kind.
abbrev WithFunctor := {A : Type u} → [Arith A] → (F : Type → Type) → F Nat → A

derive_type_rel WithFunctor (repr := A)

example (p : WithFunctor.{u}) (q : WithFunctor.{v}) :
    WithFunctor.Rel p q ↔
      ∀ {A : Type u} {B : Type v} (R : A → B → Prop) [Arith A] [Arith B],
        Arith.Rel R → ∀ (F : Type → Type) (x : F Nat), R (p F x) (q F x) := Iff.rfl

-- Selection by name applies at every depth, so a same-named binder inside an
-- argument's type is a representation too: the argument is related rather than
-- shared. Rename that binder, or mark the intended one, to say otherwise.
abbrev Shadowed := ({A : Type} → A → A) → {A : Type u} → [Arith A] → A

derive_type_rel Shadowed (repr := A)

example (p : Shadowed.{u}) (q : Shadowed.{v}) :
    Shadowed.Rel p q ↔ ∀ (f g : {A : Type} → A → A),
      (∀ {A B : Type} (R : A → B → Prop) (x : A) (y : B), R x y → R (f x) (g y)) →
      ∀ {A : Type u} {B : Type v} (R : A → B → Prop) [Arith A] [Arith B],
        Arith.Rel R → R (p f) (q g) := Iff.rfl

-- Parameters of the type definition itself are shared, including universes
-- quantified inside the type of a higher-order parameter.
abbrev WithSharedHandler (_handler : {F : Type → Type v} → F Nat → Nat) :=
  {A : Type u} → [Arith A] → A

derive_type_rel WithSharedHandler (repr := A)

class Batch (A : Type u) where
  first? : List A → Option A
  select : List A → A

derive_interface_rel Batch (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [left : Batch A] [right : Batch B] [Batch.Rel R]
    (xs : List A) (ys : List B) (h : ListRel R xs ys) :
    Option.Rel R (left.first? xs) (right.first? ys) := Batch.Rel.first? xs ys h

infer_final (A : Type u)
def selectProgram (xs : List A) : A := Batch.select xs

derive_parametric selectProgram (repr := A)

-- Relator-lifted parameters are duplicated, so they do not pin the output universe.
example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Batch A] [Batch B] (h : Batch.Rel R)
    (xs : List A) (ys : List B) (hxy : ListRel R xs ys) :
    R (selectProgram xs) (selectProgram ys) := selectProgram.parametric R h xs ys hxy

-- `Batch` lifts a relator in an operation's argument; `Source` lifts one in a program's
-- result, and reuses a container-valued generated theorem as another program's premise.
class Source (A : Type u) where
  atom : A
  batch : List A
  first? : List A → Option A

derive_interface_rel Source (repr := A)

@[expose] def atoms := infer_final% (A : Type u) => [Source.atom (A := A), Source.atom]
def pair := infer_final% (A : Type u) => (Source.atom (A := A), Source.atom (A := A))
def optional := infer_final% (A : Type u) => Source.first? (Source.batch (A := A))
def handler := infer_final% (A : Type u) => (fun x : A => Source.first? [x])

example : {A : Type u} → [Source A] → List A := @atoms
example : {A : Type u} → [Source A] → A × A := @pair
example : {A : Type u} → [Source A] → Option A := @optional
example : {A : Type u} → [Source A] → A → Option A := @handler

derive_parametric atoms (repr := A)
derive_parametric pair (repr := A)
derive_parametric optional (repr := A)
derive_parametric handler (repr := A)

-- Registered container relations must work as theorem conclusions and premises,
-- including when a generated theorem is reused by another definition.
infer_final (A : Type u)
def useAtoms : Option A := Source.first? (atoms (A := A))
derive_parametric useAtoms (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Source A] [Source B] (h : Source.Rel R) :
    ListRel R (atoms (A := A)) (atoms (A := B)) := atoms.parametric R h

example {A : Type u} {B : Type v} (R : A → B → Prop)
    [Source A] [Source B] (h : Source.Rel R) :
    Option.Rel R (useAtoms (A := A)) (useAtoms (A := B)) := useAtoms.parametric R h

-- An independent result is interpreted by equality; no representation-headed
-- result is required at the proof boundary either.
def constant := infer_final% (A : Type u) => (7 : Nat)
derive_parametric constant (repr := A)

-- An interface need not be a typeclass. A record of operations lets two
-- interpreters be held at once, which instance search cannot do, and the
-- generated relation is still a class.
structure Packed (A : Type u) where
  lit : Nat → A
  add : A → A → A

derive_interface_rel Packed (repr := A)

-- Registered structure interfaces preserve independent representation universes
-- in both program theorems and relations between polymorphic programs.
def packedExpression {A : Type u} (ops : Packed A) : A :=
  ops.add (ops.lit 1) (ops.lit 2)

derive_parametric packedExpression (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    (left : Packed A) (right : Packed B) (h : Packed.Rel R left right) :
    R (packedExpression left) (packedExpression right) :=
  packedExpression.parametric R left right h

abbrev PackedFinal := {A : Type u} → Packed A → A

derive_type_rel PackedFinal (repr := A)

example (p : PackedFinal.{u}) (q : PackedFinal.{v}) :
    PackedFinal.Rel p q ↔ ∀ {A : Type u} {B : Type v} (R : A → B → Prop)
      (left : Packed A) (right : Packed B), Packed.Rel R left right → R (p left) (q right) :=
  Iff.rfl

-- Structures with relators still scan inside lifted arguments for shared universes.
abbrev WithProductHandler := {A : Type u} → ((ULift.{u} Unit → A) × Unit) → A

derive_type_rel WithProductHandler (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    (left : Packed A) (right : Packed B) [Packed.Rel R left right]
    {x y : A} {x' y' : B} (hx : R x x') (hy : R y y') :
    R (left.add x y) (right.add x' y') := Packed.Rel.add x x' hx y y' hy

def packedEvaluate : Packed Nat := ⟨id, Nat.add⟩
def packedReify : Packed Syntax := ⟨Syntax.lit, Syntax.add⟩

-- Both interpreters are in scope at the same time, and the adapter proof is the
-- same shape as the typeclass one above.
example : Packed.Rel (fun x y => evaluate x = y) packedReify packedEvaluate where
  lit _ := rfl
  add _ _ hx _ _ hy := by cases hx; cases hy; rfl

-- A field that is itself an interface reuses the relation just generated.
structure PackedOuter (A : Type u) where
  inner : Packed A
  wrap : A → A

derive_interface_rel PackedOuter (repr := A)

example {A : Type u} {B : Type v} (R : A → B → Prop)
    (left : PackedOuter A) (right : PackedOuter B) [h : PackedOuter.Rel R left right] :
    Packed.Rel R left.inner right.inner := h.inner

/-- error: logical relation: declaration already exists: TapasTest.EndToEnd.Carrier.Arith.Rel -/
#guard_msgs in
derive_interface_rel Arith (repr := A)

class Dependent (A : Type) where
  pick : (x : A) → {y : A // y = x}

/--
error: while deriving TapasTest.EndToEnd.Carrier.Dependent.Rel.pick:
logical relation: dependent representation arguments are unsupported
-/
#guard_msgs in
derive_interface_rel Dependent (repr := A)

#guard_no_interface_rel Dependent

-- A nonparametric observation is accepted as Lean code, but its proof is rejected.
noncomputable def observe {A : Type} [Arith A] : A := by
  classical
  exact if Arith.lit (A := A) 0 = Arith.lit 2 then Arith.lit 0 else Arith.lit 1

/-- error: parametricity: condition depends on the representation or differs between interpretations -/
#guard_msgs in
derive_parametric observe (repr := A)

#guard_no_parametric observe

#guard_axioms expression.parametric, twice.parametric, expression_correct,
  sumTo.parametric, atoms.parametric, pair.parametric, optional.parametric,
  handler.parametric, useAtoms.parametric, constant.parametric ⊆ []

end TapasTest.EndToEnd.Carrier
