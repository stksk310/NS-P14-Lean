import NSP14

open CategoryTheory NSP14.Homological

namespace Run18OrderAudit

theorem actualTransfer (D : NSP14.Endpoint.Data) (k : Type) [Field k] (i : ℕ) :
    totalBetti k D.Variables (D.fullG k) i ≤
      totalBetti k D.a (D.QCoreModule k) i + D.coreRemainder k i :=
  D.actual_core_endpoint_bound k i

theorem physicalNormalization (S : NSP14.NumericalSemigroup)
    (he : 4 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity - 2) :
    (S.endpointData he hw).d * (S.endpointData he hw).u + 2 ≤ (S.endpointData he hw).m :=
  S.endpointData_narrow he hw

theorem literalTarget (S : NSP14.NumericalSemigroup) (k : Type) [Field k]
    (he : 2 ≤ S.embeddingDimension) (i : ℕ) (hi : 1 ≤ i) :
    NSP14.Target.apLowerProfile (min S.width (S.multiplicity-1)) i ≤
      totalBetti k (S.intervalCompletion he).AtomExponent
        (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k)
          ((S.intervalCompletion he).FormalTangentAlgebra k)) i :=
  S.interval_completed_betti_lower k he i hi

#check NSP14.Endpoint.Data.QCore_internal_basis
#check NSP14.Endpoint.Data.coreP_le_wordVolume
#check NSP14.Endpoint.Data.actualR_le_volume
#check NSP14.Endpoint.Data.actualR_le_height
#check NSP14.Endpoint.Data.actual_positive_rows_add
#check NSP14.Endpoint.Data.QCore_first_harmonic
#check NSP14.Endpoint.Data.QCore_first_third
#check NSP14.Endpoint.Data.QCore_first_fourth
#check NSP14.Endpoint.Data.wordVolume_tail
#check NSP14.Endpoint.Data.wordVolume_growth_bound
#check NSP14.Additive.fourPoint_growth
#check NSP14.Homological.gradedBetti_total

#print axioms actualTransfer
#print axioms physicalNormalization
#print axioms literalTarget
#print axioms NSP14.Endpoint.Data.wordVolume_growth_bound
#print axioms NSP14.Additive.fourPoint_growth

set_option pp.explicit true in
#check @NSP14.Endpoint.Data.actual_core_endpoint_bound
set_option pp.explicit true in
#check @NSP14.NumericalSemigroup.interval_completed_betti_lower
set_option pp.explicit true in
#check @NSP14.Homological.gradedBetti_total

end Run18OrderAudit
