module
public import NSP14.Endpoint.TwoRows
public import NSP14.Endpoint.FullTransfer
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (hq : D.q=2) : totalBetti k D.a (D.QCoreModule k) 1=D.internalSigma k hq+1 := D.QCore_two_betti_one k hq
end NSP14.Endpoint.Data
