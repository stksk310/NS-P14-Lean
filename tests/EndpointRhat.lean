module
public import NSP14.Endpoint.SocleBounds
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (k : Type) [Field k]
example (i : ℕ) : totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
    totalBetti k (S.endpointData he hw).a ((S.endpointData he hw).QCoreModule k) i+
      (S.endpointData he hw).coreRhatRemainder k i := S.narrow_endpoint_core_Rhat_bound he hw k i
end NSP14.NumericalSemigroup
