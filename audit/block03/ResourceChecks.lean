module

import NSP14

open scoped BigOperators
open NSP14 NSP14.Ordinary.SmallScalar

namespace NSP14.Block03Audit

-- Padding finite supports with zero layers does not change the scalar.
-- This checks the role of tail_vanish independently of the SO3 estimate.
theorem scalar_support_invariant {r : ℕ} {e d : ℚ}
    (R T : Resources r e d) (hhead : R.head = T.head) (htail : R.tail = T.tail) :
    R.scalar = T.scalar := by
  let w := fun j : ℕ => ((r : ℚ) - 1) / ((j : ℚ) + 3)
  have hR : (∑ j ∈ R.support, w j * R.tail j) =
      ∑ j ∈ R.support ∪ T.support, w j * R.tail j := by
    apply Finset.sum_subset Finset.subset_union_left
    intro j _ hj
    rw [R.tail_vanish j hj, mul_zero]
  have hT : (∑ j ∈ T.support, w j * T.tail j) =
      ∑ j ∈ R.support ∪ T.support, w j * T.tail j := by
    apply Finset.sum_subset Finset.subset_union_right
    intro j _ hj
    rw [T.tail_vanish j hj, mul_zero]
  dsimp [w] at hR hT
  unfold Resources.scalar
  rw [hhead, hR, hT, htail]

-- A profile simultaneously saturating the budget, head cap, all positive
-- residual tail caps, and SO3. The layer with zero residual carries one unit.
def sharpResources : Resources 4 5 10 where
  head := 4
  tail j := if j < 5 then 14 else if j = 5 then 1 else 0
  support := Finset.range 6
  tail_vanish j hj := by
    have h6 : 6 ≤ j := by simpa using hj
    simp [show ¬j < 5 by omega, show j ≠ 5 by omega]
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num
  budget := by norm_num [volume, Finset.sum_range_succ]
  head_cap := by norm_num [triangular]
  tail_cap j := by split_ifs <;> norm_num

example : sharpResources.scalar = upper 4 7 5 10 := by
  norm_num [Resources.scalar, sharpResources, upper, volume, triangular,
    alpha, tailWeight, Finset.sum_range_succ]

example : sharpResources.scalar = (3451 : ℚ) / 40 := by
  norm_num [Resources.scalar, sharpResources, Finset.sum_range_succ]

example : (95 : ℚ) - sharpResources.scalar = seed 4 7 := by
  norm_num [Resources.scalar, sharpResources, row4.1, Finset.sum_range_succ]

#print axioms scalar_support_invariant
