module
public import NSP14.Endpoint.Compensation
public import NSP14.Endpoint.NativeTransfer
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
theorem EndpointCompensation_acceptance_001 (i : ℕ) : totalBetti k D.a (D.QActualModule k) i≤
    totalBetti k D.a (D.QCoreModule k) i+(if i=0 then 0 else (D.coreP k-D.actualP k)*D.q.choose (i-1)) :=
  D.actual_kernel_compensation k i
end NSP14.Endpoint.Data
