module
public import NSP14.Endpoint.InternalSocleBasis
@[expose] public section
namespace NSP14.Endpoint.Data
theorem EndpointInternalSocle_acceptance_001 (D : Data) (k : Type) [Field k] (hq : D.q=2) : D.internalSigma k hq=
    Nat.card (D.InternalSocleIndex hq) := D.internalSigma_point_count k hq
end NSP14.Endpoint.Data
