module

import Tapas

namespace TapasTest.TaglessFinal.AbstractTC

class Lit (A : Type) where
  lit : Nat → A

class Wrap (A : Type) where
  wrap : A → A

/- Without a list every argument elaboration left behind is abstracted, ordered
by their type dependencies and named after `nameGen`. -/
def all {A : Type} := abstractTCargs% (Wrap.wrap (Lit.lit (A := A) 1))

/--
info: @all : {A : Type} → [arg0 : Wrap A] → [arg1 : Lit A] → A
-/
#guard_msgs in
#check @all

/- Naming the classes selects the same two. -/
def listed {A : Type} := abstractTCargs% [Lit, Wrap] (Wrap.wrap (Lit.lit (A := A) 1))

/--
info: @listed : {A : Type} → [arg0 : Wrap A] → [arg1 : Lit A] → A
-/
#guard_msgs in
#check @listed

/- A class left out of the list keeps its ordinary meaning, so its missing
instance is an ordinary error rather than a new argument. -/
/--
error: don't know how to synthesize implicit argument `self`
  @Wrap.wrap A ?m.9 (Lit.lit 1)
context:
A : Type
⊢ Wrap A
-/
#guard_msgs in
def omitted {A : Type} := abstractTCargs% [Lit] (Wrap.wrap (Lit.lit (A := A) 1))

/- A name that is neither a class nor a local declaration is rejected. -/
/--
error: unknown typeclass or local declaration: NoSuchClass
-/
#guard_msgs in
def unknownName {A : Type} := abstractTCargs% [NoSuchClass] (Lit.lit (A := A) 1)

class Pick (repr : Bool → Type) where
  pick {i} : repr i

/- Without a list the selection is not restricted to classes: the undetermined
index is abstracted as an instance-implicit argument as well. Callers that want
only class constraints pass a list, or use `inferInterfaceBody`, which checks the
head itself. -/
def unrestricted {repr : Bool → Type} := abstractTCargs% (Pick.pick (repr := repr))

/--
info: @unrestricted : {repr : Bool → Type} → [arg0 : Pick repr] → [arg1 : Bool] → repr arg1
-/
#guard_msgs in
#check @unrestricted

/- `simplifyType` drops the binders a constraint does not depend on. The
requirement here is raised under a `Nat` binder it never mentions. -/
def keptTelescope {A : Type} := abstractTCargs% (fun _ : Nat => Lit.lit (A := A) 1)

/--
info: @keptTelescope : {A : Type} → [arg0 : Nat → Lit A] → Nat → A
-/
#guard_msgs in
#check @keptTelescope

def prunedTelescope {A : Type} :=
  abstractTCargs% (simplifyType := true) (fun _ : Nat => Lit.lit (A := A) 1)

/--
info: @prunedTelescope : {A : Type} → [arg0 : Lit A] → Nat → A
-/
#guard_msgs in
#check @prunedTelescope

class Choose (σ : Type) (A : Type) where
  choose : A

/- `allowMVarDependency` decides whether a constraint may be abstracted while its
own type is still undetermined. Rejecting it reports that constraint. -/
/--
error: (type still has mvars after simplification):
Choose ?m.3 A
-/
#guard_msgs in
def undetermined {A : Type} :=
  abstractTCargs% (allowMVarDependency := false) [Choose] (Choose.choose (A := A) (σ := _))

/- The configuration is elaborated against `AbstractTCArgsConfig`, so an unknown
field is reported rather than ignored. -/
/--
error: Invalid configuration option `noSuchField` for `TaglessFinal.AbstractTCArgsConfig`
-/
#guard_msgs in
def unknownField {A : Type} := abstractTCargs% (noSuchField := true) (Lit.lit (A := A) 1)

end TapasTest.TaglessFinal.AbstractTC
