module
public import NSP14.Homological.BasiswiseTensor
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
open scoped Classical TensorProduct
namespace NSP14.Tests.BasiswiseTensor
theorem actual_varying_tensor_equivalence {k M V J : Type} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup V] [Module k V]
    (b : Module.Basis J k M) (e : J → V ≃ₗ[k] V) :
    ∃ E : M ⊗[k] V ≃ₗ[k] M ⊗[k] V,
      ∀ j w, E (b j ⊗ₜ[k] w)=b j ⊗ₜ[k] e j w :=
  ⟨Homological.basiswiseTensorEquiv b e,Homological.basiswiseTensorEquiv_tmul b e⟩
end NSP14.Tests.BasiswiseTensor
