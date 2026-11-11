module
public import NSP14.Endpoint.Residues
public import NSP14.Endpoint.MinimalBounds
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
example (r : Fin D.u) : ∃ c : ℕ×ℕ,c∈D.coreFiber r := D.coreFiber_nonempty r
example (r : Fin D.u) : D.shortestDegree r<D.u := D.shortestDegree_lt r
end NSP14.Endpoint.Data
