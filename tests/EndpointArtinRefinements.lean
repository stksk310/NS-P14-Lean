module
public import NSP14.Endpoint.FiveBound
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
theorem EndpointArtinRefinements_acceptance_001 (hq : D.q=5) : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)-(D.coreP k:ℚ)≤14 := D.QCore_first_five k hq
end NSP14.Endpoint.Data
