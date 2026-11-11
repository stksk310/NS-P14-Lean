module
public import NSP14.Endpoint.RowPackage
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace NSP14.Endpoint.Data
open NSP14.Homological
variable (D : Data) (k : Type) [Field k]
theorem EndpointRowPackage_acceptance_001 (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤D.endpointRowBound k i := D.actual_endpoint_rows k i
theorem EndpointRowPackage_acceptance_002 (i : ℕ) : totalBetti (ZMod 2) D.Variables (D.fullG (ZMod 2)) i≤D.endpointRowBound (ZMod 2) i :=
  D.actual_endpoint_rows (ZMod 2) i
theorem EndpointRowPackage_acceptance_003 (hq : D.q=2) (i : ℕ) : totalBetti (ZMod 2) D.Variables (D.fullG (ZMod 2)) i≤D.twoRowBound (ZMod 2) hq i :=
  D.actual_two_all_rows (ZMod 2) hq i
theorem EndpointRowPackage_acceptance_004 : totalBetti k D.Variables (D.fullG k) 0=1 := D.actual_endpoint_zero k
theorem EndpointRowPackage_acceptance_005 : totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.Rhat := D.actual_endpoint_top_Rhat k
theorem EndpointRowPackage_acceptance_006 : totalBetti k D.Variables (D.fullG k) (D.q+3)=0 := D.actual_endpoint_above k _ (by omega)
theorem EndpointRowPackage_acceptance_007 : D.coreRemainder k 0=0 := rfl
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
open NSP14.Homological
theorem EndpointRowPackage_acceptance_008 (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (k : Type) [Field k] (i : ℕ) : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
        (S.endpointData he hw).endpointRowBound k i := S.narrow_endpoint_rows he hw k i
end NSP14.NumericalSemigroup
