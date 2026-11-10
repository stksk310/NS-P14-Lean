module
public import NSP14.Ordinary.HarmonicWeights
public import NSP14.Semigroup.ActualLayers
public import Mathlib.Algebra.BigOperators.Intervals
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem towerResource_range (t : ℕ) :
    S.towerResource k t=∑ a ∈ Finset.range (S.qTopDegree-1),
      Module.finrank k (S.towerStageDegree k (2+a) (2+a+t)) := by
  have he : Finset.Icc 2 S.qTopDegree=Finset.Ico 2 (S.qTopDegree+1) := by
    ext a
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [towerResource,he,Finset.sum_Ico_eq_sum_range]
  rw [show S.qTopDegree+1-2=S.qTopDegree-1 by omega]

theorem actualLayers_row_sum (r j : ℕ) :
    (S.actualLayers k).row r j S.deficit=
      ∑ t ∈ Finset.range (S.headTopDegree+1),NSP14.Ordinary.LowRank.weight r j t*(S.towerResource k t : ℚ) := by
  have h := Finset.sum_range_add
    (fun t => NSP14.Ordinary.LowRank.weight r j t*(S.towerResource k t : ℚ)) 2 (S.headTopDegree+1)
  have hl : (∑ t ∈ Finset.range 2,NSP14.Ordinary.LowRank.weight r j t*(S.towerResource k t : ℚ))=
      NSP14.Ordinary.LowRank.weight r j 0*S.deficit+
        NSP14.Ordinary.LowRank.weight r j 1*(S.towerResource k 1 : ℚ) := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,S.towerResource_zero]
  rw [hl] at h
  have hrow : (S.actualLayers k).row r j S.deficit=
      ∑ t ∈ Finset.range (S.headTopDegree+3),NSP14.Ordinary.LowRank.weight r j t*(S.towerResource k t : ℚ) := by
    rw [show 2+(S.headTopDegree+1)=S.headTopDegree+3 by omega] at h
    simpa only [NSP14.Ordinary.LowRank.Layers.row,actualLayers,Nat.add_comm 2] using h.symm
  rw [hrow]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro t _ ht
  have hv : S.headTopDegree < t := by simp only [Finset.mem_range,not_lt] at ht;omega
  rw [S.towerResource_vanish k t hv]
  simp

theorem tower_harmonicWeights_row (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    (∑ t ∈ Finset.range (S.headTopDegree+1),NSP14.Ordinary.harmonicWeight r j t*(S.towerResource k t : ℚ))+
      (∑ t ∈ Finset.range (S.headTopDegree+1),NSP14.Ordinary.harmonicWeight r (j-1) t*(S.towerResource k (t+1) : ℚ))=
        (S.actualLayers k).row r j S.deficit := by
  rw [S.actualLayers_row_sum]
  apply NSP14.Ordinary.harmonicWeight_sum r j S.headTopDegree hr hj
  rw [S.towerResource_vanish k _ (by omega)]
  rfl
end NSP14.NumericalSemigroup
