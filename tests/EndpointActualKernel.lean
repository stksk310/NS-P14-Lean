module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointActualKernelAcceptance
variable (D : Endpoint.Data)

theorem all_competitor_intersection (s : Fin D.u) :
    D.actualDeadFiber s=D.coreFiber s∩D.competitorFiber s := D.actualDeadFiber_eq_inter s
end EndpointActualKernelAcceptance

namespace EndpointActualKernelAcceptance
open NSP14
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_kernel_ideal (s : Fin D.u) :
    D.actualKernelIdeal k s=D.coreFiberIdeal k s⊓D.competitorIdeal k s := D.actualKernelIdeal_eq_inf k s
end EndpointActualKernelAcceptance
