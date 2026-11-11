module
public import NSP14.Endpoint.PositiveRows
public import NSP14.Endpoint.ArtinRank
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (i : ℕ) (hi : 2 ≤ i) : totalBetti k D.Variables (D.fullG k) i≤
    D.coreP k*(D.q+1).choose i+D.Rhat*(D.q+1).choose (i-1)-(D.q+1).choose (i+1) := D.actual_positive_rows k i hi
end NSP14.Endpoint.Data
