module

import NSP14

open NSP14.Ordinary.SmallScalar

-- Entire quadrants, not numerical samples.
example (s t : ℕ) :
    0 < gap 4 7 ((4 : ℚ) + 1 + s) (triangular 4 + t) := by
  simpa [cutoff] using small_gap_pos 4 s t (by decide) (Or.inl (by decide))

example (s t : ℕ) (h : s + t ≠ 0) :
    0 < gap 8 21 ((8 : ℚ) + 1 + s) (triangular 8 + t) := by
  simpa [cutoff] using small_gap_pos 8 s t (by decide) (Or.inr h)

-- The exceptional corner must not accidentally be proved positive.
example : seed 6 13 < 0 := by rw [row6.1]; norm_num
example : seed 7 17 < 0 := by rw [row7.1]; norm_num
example : seed 8 21 < 0 := by rw [row8.1]; norm_num

-- First adjacent points of the three exceptional rows.
example : 0 < gap 6 13 ((6 : ℚ) + 1 + 1) (triangular 6 + 0) := by
  simpa [cutoff] using small_gap_pos 6 1 0 (by decide) (Or.inr (by decide))
example : 0 < gap 7 17 ((7 : ℚ) + 1 + 0) (triangular 7 + 1) := by
  simpa [cutoff] using small_gap_pos 7 0 1 (by decide) (Or.inr (by decide))
example : 0 < gap 8 21 ((8 : ℚ) + 1 + 1) (triangular 8 + 0) := by
  simpa [cutoff] using small_gap_pos 8 1 0 (by decide) (Or.inr (by decide))

#print axioms gap_shift
#print axioms dStep_eq
#print axioms row4
#print axioms row5
#print axioms row6
#print axioms row7
#print axioms row8
#print axioms cutoff_admissible
#print axioms small_gap_pos
#print axioms scalar_lt_of_upper
