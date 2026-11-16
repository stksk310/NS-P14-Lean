module

public import NSP14.Ordinary.SmallScalar
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators

namespace NSP14.Ordinary

theorem rational_sum_range (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℚ)) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The whole staircase, including zero residue and its duplicate initial zero. -/
theorem min_staircase_sum (d n : ℕ) :
    (∑ k ∈ Finset.range (d + 1 + n), ((min d (k - 1) : ℕ) : ℚ)) =
      (d : ℚ) * ((d : ℚ) - 1) / 2 + (n : ℚ) * d := by
  rw [Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range (d + 1), ((min d (k - 1) : ℕ) : ℚ)) =
      (d : ℚ) * ((d : ℚ) - 1) / 2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.zero_sub, min_zero, Nat.cast_zero, add_zero]
    rw [← rational_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [min_eq_right (by have := Finset.mem_range.mp hk; omega)]
  rw [hfirst]
  congr 1
  have hlast : ∀ k ∈ Finset.range n, min d (d + 1 + k - 1) = d := by
    intro k _
    omega
  calc
    _ = ∑ _k ∈ Finset.range n, (d : ℚ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hlast k hk]
    _ = _ := by simp

end NSP14.Ordinary
