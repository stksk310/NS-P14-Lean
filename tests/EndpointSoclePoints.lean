module
public import NSP14.Endpoint.SocleCorners
@[expose] public section
namespace NSP14.Endpoint.Data
theorem EndpointSoclePoints_acceptance_001 (D : Data) (k : Type) [Field k] : D.actualR k=Nat.card D.EndpointSocleExponent :=
  D.actualR_exponent_count k
end NSP14.Endpoint.Data
