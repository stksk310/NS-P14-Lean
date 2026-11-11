module
public import NSP14.Endpoint.HomologyFinite
public import NSP14.Endpoint.FiberModule
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (i : ℕ) : Module.Finite k ((D.endpointComplex k).homology i) := D.endpointHomologyFinite k i
end NSP14.Endpoint.Data
