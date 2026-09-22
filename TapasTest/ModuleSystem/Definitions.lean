module

public import Tapas

namespace TapasTest.ModuleSystem.Definitions

def hidden (n : Nat) := n + 1

infer_effects public def sealed := pure (hidden 3)
derive_parametric sealed

public theorem sealed_eq : sealed (m := Id) = 4 := by rfl

infer_effects @[expose] public def unfolded := pure (9 : Nat)
derive_parametric unfolded

-- Declaration inference must respect both section defaults and an explicit override.
@[expose] public section

infer_final (A : Type) def sectionIdentity (x : A) : A := x
infer_effects @[no_expose] def sectionSealed := pure (11 : Nat)

end

-- A custom theorem name must keep the visibility of its private source.
infer_effects def hiddenProgram := pure (5 : Nat)
derive_parametric hiddenProgram as hiddenProof

example {m : Type → Type} [Monad m] : hiddenProgram (m := m) = pure 5 := rfl

end TapasTest.ModuleSystem.Definitions
