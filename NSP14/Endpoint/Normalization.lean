module
public import NSP14.Semigroup.WidthNormalization
public import NSP14.Semigroup.CarrierTransport
public import NSP14.Endpoint.Presentation
@[expose] public section
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
  (k : Type) [Field k]

/-- The normalized presentation still describes the original actual
source, including its grading and its original coefficient field. -/
noncomputable def endpointData_gradedEquiv :
    (S.endpointData he hw).source.TangentAlgebra k ≃ₐ[k] S.TangentAlgebra k :=
  (S.endpointData he hw).source.carrierTangentEquiv S (S.endpointData_carrier he hw) k

noncomputable def endpointData_completedEquiv :
    (S.endpointData he hw).source.FormalTangentAlgebra k ≃ₐ[k] S.FormalTangentAlgebra k :=
  (S.endpointData he hw).source.carrierCompletedEquiv S (S.endpointData_carrier he hw) k

theorem endpointData_totalBetti (i : ℕ) :
    NSP14.Homological.totalBetti k (S.endpointData he hw).source.AtomExponent
      (ModuleCat.of ((S.endpointData he hw).source.FullPolynomialRing k)
        ((S.endpointData he hw).source.TangentAlgebra k)) i=
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i :=
  (S.endpointData he hw).source.carrier_totalBetti S (S.endpointData_carrier he hw) k i
end NSP14.NumericalSemigroup
