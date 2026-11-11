module
public import NSP14.Endpoint.FirstHarmonic
public import NSP14.Homological.StandardMonomials
@[expose] public section
open NSP14.Homological NSP14.Endpoint
attribute [local instance] MvPolynomial.gradedAlgebra
example (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (f : MvPolynomial σ k) (hf : f.IsHomogeneous n)
    (r : normalSpace MonomialOrder.degLex I)
    (hr : f-r.val∈I) : r.val.IsHomogeneous n :=
  normal_homogeneous k σ I hI n f hf r hr
