module
public import NSP14.Width.SparseFirstLarge
public import NSP14.Width.SparseFirstSmall
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- All embedding dimensions e>=6 on the infinite sparse-width range. -/
theorem actual_first_sparse (he : 6≤D.q+2) (hu : 2*(D.q+2)-2≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  by_cases h : 10≤D.q+2
  · exact D.actual_first_sparse_large k h hu
  · exact D.actual_first_sparse_small k he (by omega) hu
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
set_option synthInstance.maxHeartbeats 200000 in
/-- Sparse first-row comparison on the original completed cone and its literal completion. -/
theorem narrow_sparse_first_comparison (he : 6≤S.embeddingDimension)
    (hw : S.width≤S.multiplicity-2)
    (hu : 2*S.embeddingDimension-2≤S.normalizedWidth) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 1≤
    totalBetti k (S.intervalCompletion (le_trans (by decide : 2≤6) he)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FullPolynomialRing k)
        ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FormalTangentAlgebra k)) 1 := by
  let D := S.endpointData (by omega) hw
  have hD : D.q+2=S.embeddingDimension := S.endpointData_embedding (by omega) hw
  have heD : 6≤D.q+2 := by omega
  have huD : 2*(D.q+2)-2≤D.u := by
    change 2*(D.q+2)-2≤S.normalizedWidth
    omega
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 1≤D.u.choose 2+1 := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    exact D.actual_first_sparse k heD huD
  have hwidth : D.u≤S.width := by
    change S.normalizedWidth≤S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2≤S.embeddingDimension)
    nlinarith only [hf,hd]
  have hm : min S.width (S.multiplicity-1)=S.width := min_eq_left (by omega)
  have ht := S.interval_completed_betti_lower k (by omega) 1 (by omega)
  rw [hm] at ht
  have hp := S.width_pos (by omega : 2≤S.embeddingDimension)
  simp only [NSP14.Target.apLowerProfile,Nat.one_mul,Nat.reduceAdd,Nat.sub_self,
    Nat.choose_zero_right,Nat.choose_one_right,min_eq_left hp] at ht
  exact hb.trans ((Nat.add_le_add_right (Nat.choose_le_choose 2 hwidth) 1).trans ht)
end NSP14.NumericalSemigroup
