module

import NSP14

open NSP14.Ordinary.SmallScalar

-- A negative integer shift invalidates an unqualified "all integer shifts" claim.
-- rank 4, base e = 5, shift s = -4, d = triangular 4 = 10.
example : gap 4 7 1 10 = -(121 : ℚ) / 56 := by
  norm_num [gap, upper, volume, triangular, alpha, tailWeight, Finset.sum_range_succ]

example : ¬ (∀ s t : ℤ,
    0 < gap 4 7 ((4 : ℚ) + 1 + s) (triangular 4 + t)) := by
  intro h
  have hh := h (-4) 0
  norm_num [gap, upper, volume, triangular, alpha, tailWeight,
    Finset.sum_range_succ] at hh
