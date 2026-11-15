module
public import NSP14.Endpoint.ArtinShift
public import Mathlib.RingTheory.Ideal.Colon
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.ArtinGradedMaps
theorem actual_homogeneous_image (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (f : MvPolynomial σ k) (hf : f.IsHomogeneous n) :
    (show Homological.coefficientModule k σ (Endpoint.artinModule k σ I) from Ideal.Quotient.mk I f) ∈
      (Endpoint.artinGrading k σ I hI).degreeSpace (n:ℤ) :=
  Endpoint.artin_mk_homogeneous k σ I hI n f hf

theorem actual_quotient_projection (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (hIJ : I ≤ J)
    (q : ℤ) (a : Homological.coefficientModule k σ (Endpoint.artinModule k σ I))
    (ha : a ∈ (Endpoint.artinGrading k σ I hI).degreeSpace q) :
    Endpoint.artinQuotientMap k σ I J hIJ a ∈ (Endpoint.artinGrading k σ J hJ).degreeSpace q :=
  Endpoint.artinQuotientMap_homogeneous k σ I J hI hJ hIJ q a ha

theorem actual_homogeneous_multiplication (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (g : MvPolynomial σ k) (hIJ : I ≤ J.colon {g}) (n : ℕ) (hg : g.IsHomogeneous n)
    (q : ℤ) (a : Homological.coefficientModule k σ (Endpoint.artinModule k σ I))
    (ha : a ∈ (Endpoint.artinGrading k σ I hI).degreeSpace q) :
    Endpoint.artinMultiplyMap k σ I J g hIJ a ∈
      (Endpoint.artinGrading k σ J hJ).degreeSpace (q+(n:ℤ)) :=
  Endpoint.artinMultiplyMap_homogeneous k σ I J hI hJ g hIJ n hg q a ha

theorem actual_shifted_betti (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (s : ℤ) (i : ℕ) (t : ℤ) :
    Homological.gradedBetti k σ (Endpoint.artinModule k σ I)
      (Endpoint.artinShiftedGrading k σ I hI s) i t=
      Homological.gradedBetti k σ (Endpoint.artinModule k σ I)
        (Endpoint.artinGrading k σ I hI) i (t-s) :=
  Endpoint.artinShifted_gradedBetti k σ I hI s i t
end NSP14.Tests.ArtinGradedMaps
