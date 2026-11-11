module
public import NSP14.Endpoint.FirstHarmonic
public import NSP14.Endpoint.CoreHilbertSum
@[expose] public section
open NSP14.Homological
open scoped BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
theorem EndpointFirstBetti_acceptance_001 : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)≤(D.q : ℚ)+
    ∑ n∈Finset.range (D.u-1),((D.q-1 : ℕ) : ℚ)*(D.coreHilbert k (n+1):ℚ)/(n+2) := D.QCore_first_harmonic k
end NSP14.Endpoint.Data
