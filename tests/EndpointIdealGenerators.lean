module
public import NSP14.Endpoint.StandardArtinGenerators
@[expose] public section
open NSP14.Homological NSP14.Endpoint
attribute [local instance] MvPolynomial.gradedAlgebra
theorem EndpointIdealGenerators_acceptance_001 (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] (hp : I≠⊤)
    (hh : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    totalBetti k σ (artinModule k σ I) 1=idealGeneratorNumber k σ I := artin_first_generators k σ I hp hh
