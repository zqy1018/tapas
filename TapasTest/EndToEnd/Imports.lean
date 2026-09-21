import TapasTest.EndToEnd.Carrier
import TapasTest.EndToEnd.Indexed

namespace TapasTest.EndToEnd.Imports

universe u

def carrier := infer_final% (A : Type u) => Carrier.twice (A := A)

derive_parametric carrier (repr := A)

def indexed := infer_final% (repr : Indexed.Ty → Type u) => Indexed.six (repr := repr)

derive_parametric indexed (repr := repr)

#guard carrier (A := Nat) == 6
#guard Nat.beq (indexed (repr := Indexed.Eval)) 6

-- A generated container-valued theorem survives module import as a reusable rule.
def container := infer_final% (A : Type u) => Carrier.atoms (A := A)
derive_parametric container (repr := A)

#guard_axioms carrier.parametric, indexed.parametric, container.parametric ⊆ []

end TapasTest.EndToEnd.Imports
