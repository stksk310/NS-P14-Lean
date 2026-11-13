module
public import NSP14.Width.SparseHigher
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
set_option synthInstance.maxHeartbeats 200000 in
/-- All sparse widths, all actual Betti rows, the original completed source and literal target. -/
theorem narrow_sparse_comparison (he : 6≤S.embeddingDimension)
    (hw : S.width≤S.multiplicity-2)
    (hu : 2*S.embeddingDimension-2≤S.normalizedWidth) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
    totalBetti k (S.intervalCompletion (le_trans (by decide : 2≤6) he)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FullPolynomialRing k)
        ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FormalTangentAlgebra k)) i := by
  by_cases hi0 : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  by_cases hi1 : i=1
  · subst i
    exact S.narrow_sparse_first_comparison k he hw hu
  have hi : 2 ≤ i := by omega
  let D := S.endpointData (by omega) hw
  have hD : D.q+2=S.embeddingDimension := S.endpointData_embedding (by omega) hw
  have heD : 6≤D.q+2 := by omega
  have huD : 2*(D.q+2)-2≤D.u := by
    change 2*(D.q+2)-2≤S.normalizedWidth
    omega
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤ i*D.u.choose (i+1) := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    by_cases hie : i≤D.q+2
    · exact D.actual_sparse_higher k heD huD i hi hie
    · rw [D.actual_endpoint_above k i (by omega)]
      exact Nat.zero_le _
  have hwidth : D.u≤S.width := by
    change S.normalizedWidth≤S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2≤S.embeddingDimension)
    nlinarith only [hf,hd]
  have hm : min S.width (S.multiplicity-1)=S.width := min_eq_left (by omega)
  have ht := S.interval_completed_betti_lower k (by omega) i (by omega)
  rw [hm] at ht
  have hmon := Nat.mul_le_mul_left i (Nat.choose_le_choose (i+1) hwidth)
  have hlead : i*S.width.choose (i+1)≤NSP14.Target.apLowerProfile S.width i := Nat.le_add_right _ _
  exact hb.trans (hmon.trans (hlead.trans ht))
end NSP14.NumericalSemigroup
