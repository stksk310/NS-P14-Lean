module
public import NSP14.Endpoint.FirstRow
public import NSP14.Endpoint.PositiveRows
public import NSP14.Endpoint.TwoRows
public import NSP14.Endpoint.FiveBound
public import NSP14.Endpoint.StandardArtinGenerators
public import NSP14.Endpoint.TwoMonomial
public import NSP14.Endpoint.InternalSocleBasis
public import NSP14.Endpoint.InternalCoordinates
public import NSP14.Endpoint.SocleCorners
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : Data) (k : Type) [Field k]

/-- Canonical all-row envelope in the fixed orientation. The zeroth
row and rows above the full embedding dimension are explicit. -/
noncomputable def endpointRowBound (i : ℕ) : ℕ :=
  if i=0 then 1 else if i=1 then D.coreP k+⌊D.coreFirstBound k⌋₊+D.Rhat else
    if i≤D.q+2 then D.coreP k*(D.q+1).choose i+D.Rhat*(D.q+1).choose (i-1)-
      (D.q+1).choose (i+1) else 0

theorem actual_endpoint_rows (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤D.endpointRowBound k i := by
  unfold endpointRowBound
  split_ifs with h0 h1 hi
  · subst i
    exact (D.actual_endpoint_zero k).le
  · subst i
    exact D.actual_first_row k
  · exact D.actual_positive_rows k i (by omega)
  · rw [D.actual_endpoint_above k i (by omega)]

theorem completed_endpoint_rows (i : ℕ) : totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤D.endpointRowBound k i := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_endpoint_rows k i
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
  (k : Type) [Field k]

/-- Original source, original coefficient field and all ordinary Tor
rows; normalization and the endpoint proof chain are discharged here. -/
theorem narrow_endpoint_rows (i : ℕ) : NSP14.Homological.totalBetti k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
      (S.endpointData he hw).endpointRowBound k i := by
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti he hw k,
    ←(S.endpointData he hw).fullG_totalBetti k]
  exact (S.endpointData he hw).actual_endpoint_rows k i

theorem narrow_endpoint_two_rows (hq : (S.endpointData he hw).q=2) (i : ℕ) :
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
        (S.endpointData he hw).twoRowBound k hq i := by
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti he hw k,
    ←(S.endpointData he hw).fullG_totalBetti k]
  exact (S.endpointData he hw).actual_two_all_rows k hq i
end NSP14.NumericalSemigroup
