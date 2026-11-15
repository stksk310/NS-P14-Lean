module
public import NSP14.Endpoint.ArtinGradedZero
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.ArtinGradedZero
theorem actual_graded_zero_row (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (t : ℤ) :
    Homological.gradedBetti k σ (Endpoint.artinModule k σ I) (Endpoint.artinGrading k σ I hI) 0 t=
      if (0:ℤ)=t then 1 else 0 :=
  Endpoint.artin_gradedBetti_zero k σ I hproper hI t
end NSP14.Tests.ArtinGradedZero
