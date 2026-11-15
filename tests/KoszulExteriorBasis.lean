module
public import NSP14.Homological.KoszulExteriorBasis
public import NSP14.Homological.KoszulSlotArrow
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Tests.KoszulExteriorBasis
theorem actual_exterior_basis_exists (k σ : Type) [Field k] [Fintype σ] (j : ℕ) :
    Nonempty (Module.Basis (Homological.KoszulSlot (Homological.variableList k σ).length j)
      k (⋀[k]^j (σ → k))) :=
  ⟨Homological.koszulExteriorBasis k j⟩
end NSP14.Tests.KoszulExteriorBasis
