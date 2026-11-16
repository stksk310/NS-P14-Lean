module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LargeSeed

example (r : ℕ) (hr : 10 ≤ r) : harmonic (largeCutoff r) < barrier r :=
  harmonic_lt_barrier r hr

example (r : ℕ) (hr : 9 ≤ r) :
    0 < gap r (largeCutoff r) 10 (triangular r) :=
  large_seed_pos r hr

-- Odd/even triangular numbers: every floor is taken in N before casting.
example : triangularNat 9 = 45 ∧ largeCutoff 9 = 23 ∧
    triangularNat 10 = 55 ∧ largeCutoff 10 = 28 ∧
    triangularNat 11 = 66 ∧ largeCutoff 11 = 34 ∧
    triangularNat 12 = 78 ∧ largeCutoff 12 = 40 := by
  norm_num [triangularNat, largeCutoff]

example (r : ℕ) : (triangularNat r : ℚ) = triangular r := triangularNat_cast r
example (r : ℕ) (hr : 9 ≤ r) : r ≤ largeCutoff r :=
  NSP14.Ordinary.LargeSeed.cutoff_admissible r (by omega)

-- Harmonic indexing includes exactly 1,...,n.
example : harmonic 0 = 0 ∧ harmonic 1 = 1 ∧ harmonic 2 = 3 / 2 := by
  norm_num [harmonic, Finset.sum_range_succ]
example : harmonic 23 = 444316699 / 118982864 := by
  norm_num [harmonic, Finset.sum_range_succ]
example : threshold 9 23 = 269 / 72 := by norm_num [threshold, triangular]
example : barrier 10 - harmonic 28 = 1833472237 / 80313433200 := by
  norm_num [barrier, harmonic, Finset.sum_range_succ]
example : gap 9 (largeCutoff 9) 10 (triangular 9) = 5845533 / 7436429 := by
  norm_num [gap, upper, volume, alpha, triangular, largeCutoff, triangularNat,
    tailWeight, Finset.sum_range_succ]

-- At r=10 the new increment comparison is already strict: gap = 7/3190.
example : barrier 11 - barrier 10 - (10 + 2) / (triangular 10 + 3) = 7 / 3190 := by
  norm_num [barrier, triangular]

-- Generic identities, with no finite upper bound on rank or cutoff.
example (r : ℕ) (hr : 10 ≤ r) :
    ((r : ℚ) + 2) / (triangular r + 3) < barrier (r + 1) - barrier r :=
  barrier_step_gt r hr
example (r n : ℕ) (hr : 9 ≤ r) (hn : 2 ≤ n) :
    gap r n 10 (triangular r) =
      ((r : ℚ) - 1) * (triangular r + 9) * (threshold r n - harmonic n) :=
  seed_eq_threshold r n hr hn

#print axioms triangularNat_cast
#print axioms triangularNat_succ
#print axioms triangular_nonneg
#print axioms cutoff_bounds
#print axioms NSP14.Ordinary.LargeSeed.cutoff_admissible
#print axioms cutoff_step
#print axioms harmonic_add
#print axioms harmonic_add_le
#print axioms harmonic_cutoff_step
#print axioms barrier_step_identity
#print axioms barrier_step_gt
#print axioms harmonic_base
#print axioms harmonic_lt_barrier
#print axioms threshold_gap_identity
#print axioms barrier_lt_thresholdLower
#print axioms thresholdLower_le_threshold
#print axioms harmonic_lt_threshold
#print axioms harmonic_tail
#print axioms tailWeight_eq
#print axioms seed_eq_threshold
#print axioms rank_nine_seed
#print axioms large_seed_pos
