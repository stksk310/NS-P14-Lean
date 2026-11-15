module
public import NSP14.Endpoint.GradedIdealAdjoining
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.GradedIdealAdjoining
theorem actual_graded_adjoining (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (J : Ideal (MvPolynomial σ k)) (g h : MvPolynomial σ k) (x : σ)
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hK : (J ⊔ Ideal.span {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hC : (J.colon {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (hdeg : g.IsHomogeneous n) (he : g=MvPolynomial.X x*h)
    (hc : J.colon {g} ≤ J.colon {h}) (i : ℕ) (t : ℤ) :
    Homological.gradedBetti k σ (Endpoint.artinModule k σ (J ⊔ Ideal.span {g}))
        (Endpoint.artinGrading k σ (J ⊔ Ideal.span {g}) hK) (i+1) t=
      Homological.gradedBetti k σ (Endpoint.artinModule k σ J) (Endpoint.artinGrading k σ J hJ) (i+1) t+
      Homological.gradedBetti k σ (Endpoint.artinModule k σ (J.colon {g}))
        (Endpoint.artinGrading k σ (J.colon {g}) hC) i (t-(n:ℤ)) :=
  Endpoint.artin_adjoin_gradedBetti k σ J g h x hJ hK hC n hdeg he hc i t
end NSP14.Tests.GradedIdealAdjoining
