module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointModulesAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem actual_endpoint_surjection : Function.Surjective (D.coreToGEndpoint k).hom :=
  D.coreToGEndpoint_surjective k

theorem correct_endpoints :
    (D.coreToG k).comp (D.endpointToCore k)=D.endpointToG k := D.coreToG_endpointToCore k
end EndpointModulesAcceptance
