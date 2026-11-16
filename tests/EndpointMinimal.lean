module
public import NSP14.Endpoint.MinimalWords
public import NSP14.Endpoint.Minimal
public import Mathlib.Order.Minimal
@[expose] public section
open NSP14
namespace EndpointMinimalAcceptance
variable (D : Endpoint.Data)

theorem no_endpoint_factor (p q : D.corePoints) (c : ℕ×ℕ)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2)
    (h : p=q+D.coreEndpointPoint c) : c=0 := D.minimal_endpoint_factor p q c hmin h
end EndpointMinimalAcceptance

namespace EndpointMinimalAcceptance
open NSP14
variable (D : Endpoint.Data)
theorem bounded_internal_word (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : w.length<D.u := D.minimal_word_length_lt w hmin
end EndpointMinimalAcceptance
