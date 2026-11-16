module
public import NSP14.Endpoint.QuadraticDimension
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
theorem EndpointQuadratic_acceptance_001 : D.coreHilbert k 2≤(D.q+1).choose 2 := D.coreHilbert_two_bound k
end NSP14.Endpoint.Data
