module
public import NSP14.Endpoint.FullTransfer
public import NSP14.Endpoint.VariableOrder
public import NSP14.Endpoint.H0Internal
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QActualModule k) i+D.endpointRemainder k i := D.actual_native_endpoint_bound k i
end NSP14.Endpoint.Data

namespace NSP14.Endpoint.Data
open NSP14.Homological
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := D.actual_core_endpoint_bound k i
example : totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.actualR k := D.actual_endpoint_top k
example : totalBetti k D.Variables (D.fullG k) 0=1 := D.actual_endpoint_zero k
end NSP14.Endpoint.Data
