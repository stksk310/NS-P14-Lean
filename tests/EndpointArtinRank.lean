module
public import NSP14.Endpoint.ArtinRank
public import NSP14.Homological.KoszulIndependentImages
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (i : ℕ) (hi : 1 ≤ i) : totalBetti k D.a (D.QCoreModule k) i≤
    D.coreP k*D.q.choose i-(D.q+1).choose (i+1) := D.QCore_positive_betti_bound k i hi
end NSP14.Endpoint.Data
