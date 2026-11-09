module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LargeSeed
open NSP14.Ordinary.LargeScalar

namespace NSP14.Block06Audit

-- The coefficient after absorbing the negative linear term is uniformly positive.
theorem continuous_linear_margin (r : ℕ) (hr : 9 ≤ r) :
    3 / 4 < baseStep r (largeCutoff r) - (1 - alpha r (largeCutoff r)) / 2 := by
  have hb := baseStep_gt r hr
  obtain ⟨ha0, ha1⟩ := alpha_bounds r hr
  linarith

-- Odd triangular number: the actual cutoff attains the rational minimum.
example : stepLower 9 (largeCutoff 9) = floorStep 9 := by
  norm_num [stepLower, floorStep, correction, alpha, triangular, largeCutoff, triangularNat]

-- Even triangular number: the actual cutoff is strictly above that minimum.
example : floorStep 11 < stepLower 11 (largeCutoff 11) := by
  norm_num [stepLower, floorStep, correction, alpha, triangular, largeCutoff, triangularNat]

example : floorStep 9 = (124 : ℚ) / 9 := by norm_num [floorStep, triangular]

-- This original quadratic summand is negative for fractional shifts.
example : (1 / 2 : ℚ) * ((1 / 2 : ℚ) - 1) / 2 = -(1 / 8 : ℚ) := by norm_num

-- A tiny positive rational deficit shift is admitted at every rank, including s=0.
example (r : ℕ) (hr : 9 ≤ r) :
    0 < gap r (largeCutoff r) 10 (triangular r + 1 / 100) := by
  simpa using gap_pos_shift r (0 : ℚ) (1 / 100 : ℚ) hr (by norm_num) (by norm_num)

#print axioms continuous_linear_margin

end NSP14.Block06Audit
