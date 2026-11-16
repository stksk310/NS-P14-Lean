module

public import NSP14.Semigroup.TowerResources
public import NSP14.Ordinary.LowRank

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [Field k]

/-- The layers passed towards numerical closure use exactly one actual H.
The budget and head/tail inequalities are separate unclosed obligations. -/
noncomputable def actualLayers : NSP14.Ordinary.LowRank.Layers where
  head := (S.towerResource k 1 : ℚ)
  tail j := (S.towerResource k (j + 2) : ℚ)
  support := Finset.range (S.headTopDegree + 1)
  tail_vanish j hj := by
    have ht : S.headTopDegree < j + 2 := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    rw [S.towerResource_vanish k _ ht]
    rfl
  head_nonneg := Nat.cast_nonneg _
  tail_nonneg _ := Nat.cast_nonneg _

@[simp] theorem actualLayers_head : (S.actualLayers k).head = (S.towerResource k 1 : ℚ) := rfl
@[simp] theorem actualLayers_tail (j : ℕ) :
    (S.actualLayers k).tail j = (S.towerResource k (j + 2) : ℚ) := rfl

/-- A finite sum over every actual degree. The additional last two entries
are proved zero, rather than truncating an unknown tail. -/
theorem actualLayers_mass :
    (S.actualLayers k).mass S.deficit =
      ∑ t ∈ Finset.range (S.headTopDegree + 3), (S.towerResource k t : ℚ) := by
  have h := Finset.sum_range_add (fun t => (S.towerResource k t : ℚ)) 2 (S.headTopDegree + 1)
  have he : 2 + (S.headTopDegree + 1) = S.headTopDegree + 3 := by omega
  rw [he] at h
  have hsmall : (∑ t ∈ Finset.range 2, (S.towerResource k t : ℚ)) =
      (S.towerResource k 0 : ℚ) + (S.towerResource k 1 : ℚ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsmall] at h
  have hshift : (∑ j ∈ Finset.range (S.headTopDegree + 1),
      (S.towerResource k (2 + j) : ℚ)) =
      ∑ j ∈ Finset.range (S.headTopDegree + 1), (S.towerResource k (j + 2) : ℚ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm 2 j]
  rw [hshift, S.towerResource_zero] at h
  exact h.symm

end NSP14.NumericalSemigroup
