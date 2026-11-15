module
public import NSP14.Homological.NormalTriangular
@[expose] public section
namespace NSP14.Tests.NormalTriangular
theorem actual_normal_degree (k σ : Type) [Field k] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k)
    (r : Homological.normalSpace m I) (hfr : f-r.val ∈ I) :
    m.toSyn (m.degree r.val) ≤ m.toSyn (m.degree f) :=
  Homological.normal_representative_degree_le k m I f r hfr
end NSP14.Tests.NormalTriangular
