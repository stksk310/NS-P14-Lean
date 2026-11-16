module
public import NSP14.Width.EdgeAP
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.Tests.EdgeAP
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem actual_all_rows (he : 5 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2)
    (hu : (S.endpointData (by omega) hw).u=(S.endpointData (by omega) hw).q+1) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i :=
  S.narrow_fullAP_comparison k he hw hu i
end NSP14.Tests.EdgeAP
