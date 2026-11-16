module
public import NSP14.Homological.ExteriorContraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
@[expose] public section
namespace NSP14.Tests.ExteriorContraction
theorem actual_contraction_naturality (R : Type) [CommRing R] {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (φ : Module.Dual R N) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft φ (ExteriorAlgebra.map f x)=
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (φ.comp f) x) :=
  Homological.exterior_contract_map R f φ x
end NSP14.Tests.ExteriorContraction
