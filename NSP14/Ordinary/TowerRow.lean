module
public import NSP14.Ordinary.TowerCombined
public import NSP14.Ordinary.TowerResourceWeights
@[expose] public section
open scoped BigOperators
namespace NSP14.NumericalSemigroup.LinearCutData
open NSP14.Ordinary
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem cutHighEuler_le_weights (s n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ S.actualCutRank) :
    (C.cutHighEuler s n j : ℚ) ≤
      ∑ t ∈ Finset.range (S.headTopDegree+1),harmonicWeight S.actualCutRank j t*
        Module.finrank k (S.towerStageDegree k s (n+t)) := by
  by_cases hj0 : j=0
  · subst j
    rw [C.cutHighEuler_zero s n hn]
    simp [harmonicWeight]
  · by_cases htop : j=S.actualCutRank
    · subst j
      rw [C.cutHighEuler_top]
      have hr0 : S.actualCutRank ≠ 0 := by have := S.actualCutRank_two_le;omega
      simp [harmonicWeight,hr0,Nat.choose_eq_zero_of_lt (show S.actualCutRank-1 < S.actualCutRank by omega)]
    · have h := C.cutHighEuler_harmonic s n hn j ⟨by omega,by omega⟩
      simpa only [harmonicWeight,ite_eq_right hj0,Finset.mul_sum,mul_assoc] using h

/-- The complete same-cut tower contribution is the existing single H row,
including H0, the first Betti row and the finite-P top row. The separate
first x-Koszul comparison is still needed to turn this into a bound for G. -/
theorem cutTower_resource_row (j : ℕ) (hj : 1 ≤ j ∧ j ≤ S.actualCutRank) :
    ((C.cutHighEuler 2 2 j+C.cutTEuler (j-1) : ℤ) : ℚ) ≤
      (S.actualLayers k).row S.actualCutRank j S.deficit := by
  have hb := C.cutTower_combined (j-1)
  rw [Nat.sub_add_cancel hj.1] at hb
  have hq : ((C.cutHighEuler 2 2 j+C.cutTEuler (j-1) : ℤ) : ℚ) ≤
      ∑ a ∈ Finset.range (S.qTopDegree-1),
        ((C.cutHighEuler (2+a) (2+a) j : ℚ)+(C.cutHighEuler (2+a) (3+a) (j-1) : ℚ)) := by
    exact_mod_cast hb
  have hsum := Finset.sum_le_sum (s:=Finset.range (S.qTopDegree-1)) (fun a _ =>
    add_le_add (C.cutHighEuler_le_weights (2+a) (2+a) (by omega) j hj.2)
      (C.cutHighEuler_le_weights (2+a) (3+a) (by omega) (j-1) (by omega)))
  have hx : (∑ a ∈ Finset.range (S.qTopDegree-1),
      ∑ t ∈ Finset.range (S.headTopDegree+1),harmonicWeight S.actualCutRank j t*
        Module.finrank k (S.towerStageDegree k (2+a) (2+a+t)))=
      ∑ t ∈ Finset.range (S.headTopDegree+1),harmonicWeight S.actualCutRank j t*(S.towerResource k t : ℚ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum,S.towerResource_range k t,Nat.cast_sum]
  have hm : (∑ a ∈ Finset.range (S.qTopDegree-1),
      ∑ t ∈ Finset.range (S.headTopDegree+1),harmonicWeight S.actualCutRank (j-1) t*
        Module.finrank k (S.towerStageDegree k (2+a) (3+a+t)))=
      ∑ t ∈ Finset.range (S.headTopDegree+1),harmonicWeight S.actualCutRank (j-1) t*(S.towerResource k (t+1) : ℚ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum,S.towerResource_range k (t+1),Nat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [show 3+a+t=2+a+(t+1) by omega]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hx,hm,S.tower_harmonicWeights_row k S.actualCutRank j
    (by have := S.actualCutRank_two_le;omega) hj.1] at hsum
  rw [Finset.sum_add_distrib] at hq
  exact hq.trans hsum
end NSP14.NumericalSemigroup.LinearCutData
