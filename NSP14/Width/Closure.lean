module
public import NSP14.Width.DenseComparison
public import NSP14.Width.SparseComparison
public import NSP14.Width.FiveComparison
public import NSP14.Width.EdgeHoleComparison
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
set_option synthInstance.maxHeartbeats 200000
/-- All original narrow sources with at least five actual minimal generators. -/
theorem narrow_width_comparison (he : 5≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
      totalBetti k (S.intervalCompletion (le_trans (by decide : 2≤5) he)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (le_trans (by decide : 2≤5) he)).FullPolynomialRing k)
          ((S.intervalCompletion (le_trans (by decide : 2≤5) he)).FormalTangentAlgebra k)) i := by
  by_cases he5 : S.embeddingDimension=5
  · exact S.narrow_five_comparison k he5 hw i
  have he6 : 6≤S.embeddingDimension := by omega
  let D := S.endpointData (by omega) hw
  have hD : D.q+2=S.embeddingDimension := S.endpointData_embedding (by omega) hw
  have hq : 4≤D.q := by omega
  have hU := D.q_add_one_le_u
  by_cases hedge0 : D.u=D.q+1
  · exact S.narrow_fullAP_comparison k he hw hedge0 i
  by_cases hedge1 : D.u=D.q+2
  · exact S.narrow_oneHole_comparison k he hw hedge1 i
  by_cases hsparse : 2*S.embeddingDimension-2≤D.u
  · exact S.narrow_sparse_comparison k he6 hw hsparse i
  let t := D.u-(D.q+1)
  have ht2 : 2≤t := by dsimp [t]; omega
  have htq : t≤D.q := by dsimp [t]; omega
  have hu : D.u=D.q+1+t := by dsimp [t]; omega
  exact S.narrow_dense_comparison k he6 hw t hu ht2 htq i
end NSP14.NumericalSemigroup
