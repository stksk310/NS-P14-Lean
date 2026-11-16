module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LargeSeed
open NSP14.Ordinary.LargeScalar

example (r : ℕ) (e d : ℚ) (hr : 9 ≤ r) (he : 10 ≤ e) (hd : triangular r ≤ d) :
    0 < gap r (largeCutoff r) e d := large_gap_pos r e d hr he hd

example (r : ℕ) (e d : ℚ) (R : Resources r e d)
    (hr : 9 ≤ r) (he : 10 ≤ e) (hd : triangular r ≤ d) :
    R.scalar < d * (volume e d + 1) := R.scalar_lt_large hr he hd

-- The exact minimum point and the first two ranks of each cutoff parity.
example : 0 < gap 9 (largeCutoff 9) 10 45 := by
  exact large_gap_pos 9 10 45 (by decide) (by norm_num) (by norm_num [triangular])
example : 0 < gap 10 (largeCutoff 10) 10 55 := by
  exact large_gap_pos 10 10 55 (by decide) (by norm_num) (by norm_num [triangular])
example : 0 < gap 11 (largeCutoff 11) 10 66 := by
  exact large_gap_pos 11 10 66 (by decide) (by norm_num) (by norm_num [triangular])

-- Rational extension: 0<t<1 would make t(t−1)/2 negative.
example : 0 < gap 9 (largeCutoff 9) (21 / 2) (91 / 2) := by
  exact large_gap_pos 9 (21 / 2) (91 / 2) (by decide)
    (by norm_num) (by norm_num [triangular])

-- Uniformly arbitrarily far into both directions, without finite rank sampling.
example (r : ℕ) (s t : ℚ) (hr : 9 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < gap r (largeCutoff r) (10 + s) (triangular r + t) :=
  gap_pos_shift r s t hr hs ht

-- The stronger forward difference and the continuous cutoff comparison.
example (r : ℕ) (hr : 9 ≤ r) : 5 / 4 < baseStep r (largeCutoff r) := baseStep_gt r hr
example (r : ℕ) (hr : 9 ≤ r) : floorStep r ≤ stepLower r (largeCutoff r) :=
  floorStep_le_stepLower r hr

-- One genuine finite resource profile, with a nonzero layer at any tail index.
def largeResources (k : ℕ) : Resources 9 (21 / 2) (91 / 2) where
  head := 0
  tail j := if j = k then 1 else 0
  support := {k}
  tail_vanish j hj := by simpa using hj
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num
  budget := by norm_num [volume]
  head_cap := by norm_num [triangular]
  tail_cap j := by split_ifs <;> norm_num

example (k : ℕ) : (largeResources k).scalar < 11921 / 8 := by
  have h := (largeResources k).scalar_lt_large (by decide) (by norm_num)
    (by norm_num [triangular])
  norm_num [volume] at h
  exact h

#print axioms triangular_large
#print axioms alpha_bounds
#print axioms seed_slope_identity
#print axioms step_identity
#print axioms correction_neg
#print axioms baseSlope_lower
#print axioms baseSlope_pos
#print axioms floor_comparison_identity
#print axioms floorStep_le_stepLower
#print axioms floorStep_gt
#print axioms baseStep_gt
#print axioms quadrant_identity
#print axioms gap_pos_shift
#print axioms large_gap_pos
#print axioms Resources.scalar_lt_large
