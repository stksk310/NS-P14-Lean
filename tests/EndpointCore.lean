module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointCoreAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem actual_surjection : Function.Surjective (D.coreToG k) := D.coreToG_surjective k

theorem actual_minimal_presentation :
    (D.coreToG k).comp (D.fullToCore k)=D.fullToG k := D.coreToG_fullToCore k
end EndpointCoreAcceptance

namespace EndpointCoreAcceptance
open NSP14
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_kernel : (D.coreToG k).toLinearMap.ker=
    Submodule.span k ((D.coreMonomial k) '' {p | D.coreDegree p<D.source.order (D.coreValue p).val}) :=
  D.coreToG_kernel_span k
end EndpointCoreAcceptance
