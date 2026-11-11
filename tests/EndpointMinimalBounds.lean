module
public import NSP14.Endpoint.MinimalBounds
public import NSP14.Endpoint.MinimalWords
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
example (r : Fin D.u) (c : ℕ×ℕ) (h : Minimal (·∈D.coreFiber r) c) :
    c.1+c.2≤D.u-2 := D.minimalFiber_budget r c h
example (r : Fin D.u) : Set.Finite {c | Minimal (·∈D.coreFiber r) c} := D.minimalFiber_finite r
end NSP14.Endpoint.Data
