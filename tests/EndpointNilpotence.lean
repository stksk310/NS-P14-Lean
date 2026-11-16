module
public import NSP14.Endpoint.EndpointRank
public import NSP14.Endpoint.Competitors
@[expose] public section
open NSP14
namespace EndpointNilpotenceAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem actual_endpoint_nilpotent :
    D.endpointToG k (MvPolynomial.X (1 : Fin 2))^D.m=0 := D.endpoint_v_nilpotent k
end EndpointNilpotenceAcceptance

namespace EndpointNilpotenceAcceptance
open NSP14
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_E_rank_zero : Module.rank (D.EndpointRing k) (D.actualEndpointModule k)=0 :=
  D.actualEndpoint_rank_zero k
end EndpointNilpotenceAcceptance
