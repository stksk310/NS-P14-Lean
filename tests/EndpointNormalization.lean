module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointNormalizationAcceptance
variable (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension) (hw : S.width≤S.multiplicity-2)

theorem same_source : (S.endpointData he hw).source.carrier=S.carrier := S.endpointData_carrier he hw

theorem same_multiplicity : (S.endpointData he hw).m=S.multiplicity := S.endpointData_m he hw

theorem same_embedding : (S.endpointData he hw).q+2=S.embeddingDimension := S.endpointData_embedding he hw

theorem narrow_bound : (S.endpointData he hw).d*(S.endpointData he hw).u+2≤(S.endpointData he hw).m :=
  S.endpointData_narrow he hw
end EndpointNormalizationAcceptance
