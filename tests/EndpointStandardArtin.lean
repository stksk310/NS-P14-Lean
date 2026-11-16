module
public import NSP14.Endpoint.StandardArtinGenerators
public import NSP14.Homological.StandardMonomials
@[expose] public section
open NSP14.Homological NSP14.Endpoint
attribute [local instance] MvPolynomial.gradedAlgebra
theorem EndpointStandardArtin_acceptance_001 (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (f : MvPolynomial σ k) (hf : f.IsHomogeneous n)
    (r : normalSpace MonomialOrder.degLex I)
    (hr : f-r.val∈I) : r.val.IsHomogeneous n :=
  normal_homogeneous k σ I hI n f hf r hr

namespace GeneralArtinAcceptance
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]
  (hp : I≠⊤) (hh : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
  (h1 : ∀ f∈I,f.IsHomogeneous 1 → f=0) (hq : 2≤Fintype.card σ)
include hp hh h1 hq in
theorem EndpointStandardArtin_acceptance_002 : (totalBetti k σ (artinModule k σ I) 1 : ℚ)≤
    weightedFirst (Fintype.card σ) (artinLimit k σ I) (artinHilbert k σ I hh) :=
  artin_first_harmonic k σ I hp hh h1 hq
include hp hh h1 in
theorem EndpointStandardArtin_acceptance_003 (i : ℕ) (hi : 1 ≤ i) : totalBetti k σ (artinModule k σ I) i≤
    Module.finrank k (MvPolynomial σ k ⧸ I)*(Fintype.card σ).choose i-
      (Fintype.card σ+1).choose (i+1) := artin_positive_rows k σ I hp hh h1 i hi
include hp hh h1 in
theorem EndpointStandardArtin_acceptance_004 (h5 : Fintype.card σ=5) : (totalBetti k σ (artinModule k σ I) 1 : ℚ)-
    (Module.finrank k (MvPolynomial σ k ⧸ I):ℚ)≤14 := artin_first_five k σ I hp hh h1 h5
end GeneralArtinAcceptance
