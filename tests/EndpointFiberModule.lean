module
public import NSP14.Endpoint.FiberModule
public import NSP14.Endpoint.IdealCoordinates
@[expose] public section
open scoped DirectSum
open NSP14
namespace EndpointFiberModuleAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem actual_E_module : Nonempty (D.coreEndpointModule k ≃ₗ[D.EndpointRing k]
    (⨁ r : Fin D.u,D.coreFiberIdeal k r)) := ⟨D.coreFiberModuleEquiv k⟩
end EndpointFiberModuleAcceptance
