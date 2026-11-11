module
public import NSP14.Endpoint.TwoMonomial
@[expose] public section
namespace NSP14.Endpoint.Data
theorem EndpointTwoMonomial_acceptance_001 (D : Data) (k : Type) [Field k] (hq : D.q=2) (f : D.InternalRing k) :
    D.internalToQCore k f=0 ↔ ∀ β∈f.support,D.internalToQCore k (MvPolynomial.monomial β (1:k))=0 :=
  D.two_internal_monomial_kernel k hq f
end NSP14.Endpoint.Data
