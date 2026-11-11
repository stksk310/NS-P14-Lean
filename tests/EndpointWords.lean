module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointWordsAcceptance
variable (D : Endpoint.Data)
theorem every_actual_core_point (p : D.corePoints) : ∃ w : List D.Variables,D.coreWord w=p :=
  D.exists_coreWord p
end EndpointWordsAcceptance
