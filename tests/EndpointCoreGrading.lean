module
public import NSP14.Endpoint.CoreHilbert
@[expose] public section
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example : Module.finrank k ((D.QCoreGrading k).piece 0)=1 := D.QCoreGrading_zero_dim k
example : Module.finrank k ((D.QCoreGrading k).piece 1)=D.q := D.QCoreGrading_one_dim k
example : Function.Surjective (D.internalToQCore k) := D.internalToQCore_surjective k
end NSP14.Endpoint.Data
