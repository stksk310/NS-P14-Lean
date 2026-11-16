module

public import NSP14.Ordinary.Resources
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open scoped BigOperators

namespace NSP14.Ordinary.LargeSeed

open SmallScalar

/-!
# Large-rank harmonic barrier and base-gap positivity

This proves the base G_r(10,a_r)>0 for every r≥9. Extending the base to
arbitrary embedding dimension and deficit is a separate subsequent step.
-/

def triangularNat (r : ℕ) : ℕ := r * (r + 1) / 2
def largeCutoff (r : ℕ) : ℕ := triangularNat r / 2 + 1
def harmonic (n : ℕ) : ℚ := ∑ j ∈ Finset.range n, 1 / ((j : ℚ) + 1)
def barrier (r : ℕ) : ℚ := (r : ℚ) / 4 + 1 + 9 / (2 * (r : ℚ))

theorem triangularNat_cast (r : ℕ) : (triangularNat r : ℚ) = triangular r := by
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)
  have hq : (2 : ℚ) * (triangularNat r : ℚ) = (r : ℚ) * ((r : ℚ) + 1) := by
    exact_mod_cast h
  unfold triangular
  linarith

theorem triangularNat_succ (r : ℕ) :
    triangularNat (r + 1) = triangularNat r + r + 1 := by
  have hq : (triangularNat (r + 1) : ℚ) = (triangularNat r : ℚ) + r + 1 := by
    rw [triangularNat_cast, triangularNat_cast]
    simp only [triangular, Nat.cast_add, Nat.cast_one]
    ring
  exact_mod_cast hq

theorem triangular_nonneg (r : ℕ) : 0 ≤ triangular r := by unfold triangular; positivity

/-- Both floor bounds, including the odd triangular-number case. -/
theorem cutoff_bounds (r : ℕ) :
    triangular r + 1 ≤ 2 * (largeCutoff r : ℚ) ∧
    2 * (largeCutoff r : ℚ) ≤ triangular r + 2 := by
  have hm := Nat.mod_lt (triangularNat r) (by decide : 0 < 2)
  have he := Nat.mod_add_div (triangularNat r) 2
  have hl : triangularNat r + 1 ≤ 2 * largeCutoff r := by unfold largeCutoff; omega
  have hu : 2 * largeCutoff r ≤ triangularNat r + 2 := by unfold largeCutoff; omega
  rw [← triangularNat_cast]
  constructor <;> exact_mod_cast (by assumption)

theorem cutoff_admissible (r : ℕ) (hr : 4 ≤ r) : r ≤ largeCutoff r := by
  have hrq : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hl := (cutoff_bounds r).1
  have hp : 0 ≤ (r : ℚ) * ((r : ℚ) - 3) :=
    mul_nonneg (by positivity) (by linarith)
  have hq : (r : ℚ) ≤ largeCutoff r := by unfold triangular at hl; nlinarith
  exact_mod_cast hq

theorem cutoff_step (r : ℕ) :
    largeCutoff r ≤ largeCutoff (r + 1) ∧
    2 * (largeCutoff (r + 1) - largeCutoff r) ≤ r + 2 := by
  have ha := triangularNat_succ r
  have hm := Nat.mod_lt (triangularNat r) (by decide : 0 < 2)
  have hm' := Nat.mod_lt (triangularNat (r + 1)) (by decide : 0 < 2)
  have he := Nat.mod_add_div (triangularNat r) 2
  have he' := Nat.mod_add_div (triangularNat (r + 1)) 2
  unfold largeCutoff
  omega

theorem harmonic_add (n b : ℕ) : harmonic (n + b) = harmonic n +
    ∑ j ∈ Finset.range b, 1 / ((n : ℚ) + j + 1) := by
  simp only [harmonic, Finset.sum_range_add, Nat.cast_add]

/-- Every term of a harmonic block is bounded by its first term. -/
theorem harmonic_add_le (n b : ℕ) :
    harmonic (n + b) ≤ harmonic n + (b : ℚ) / ((n : ℚ) + 1) := by
  rw [harmonic_add]
  have hs : (∑ j ∈ Finset.range b, 1 / ((n : ℚ) + j + 1)) ≤
      ∑ _j ∈ Finset.range b, 1 / ((n : ℚ) + 1) := by
    apply Finset.sum_le_sum
    intro j _
    have hj : (0 : ℚ) ≤ j := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using
    add_le_add_left hs (harmonic n)

/-- A coarser increment bound suffices for the same barrier as the paper. -/
theorem harmonic_cutoff_step (r : ℕ) :
    harmonic (largeCutoff (r + 1)) ≤ harmonic (largeCutoff r) +
      ((r : ℚ) + 2) / (triangular r + 3) := by
  obtain ⟨hmono, hstep⟩ := cutoff_step r
  let b := largeCutoff (r + 1) - largeCutoff r
  have hsum := harmonic_add_le (largeCutoff r) b
  have heq : largeCutoff r + b = largeCutoff (r + 1) := by dsimp [b]; omega
  rw [heq] at hsum
  have hb : (2 : ℚ) * b ≤ (r : ℚ) + 2 := by exact_mod_cast hstep
  have hp := (cutoff_bounds r).1
  have ha := triangular_nonneg r
  have hle : (b : ℚ) / ((largeCutoff r : ℚ) + 1) ≤
      ((r : ℚ) + 2) / (triangular r + 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h1 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ triangular r + 3)
    have h2 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (r : ℚ) + 2)
    nlinarith
  linarith

/-- The increment comparison is a positive quartic in r−10. -/
theorem barrier_step_identity (r : ℕ) (hr : 10 ≤ r) :
    barrier (r + 1) - barrier r - ((r : ℚ) + 2) / (triangular r + 3) =
      (((r : ℚ) - 10) ^ 4 + 34 * ((r : ℚ) - 10) ^ 3 +
        385 * ((r : ℚ) - 10) ^ 2 + 1472 * ((r : ℚ) - 10) + 112) /
        (4 * (r : ℚ) * ((r : ℚ) + 1) * ((r : ℚ) ^ 2 + r + 6)) := by
  have hrq : (10 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℚ) ≠ 0 := by linarith
  unfold barrier triangular
  push_cast
  field_simp
  ring

theorem barrier_step_gt (r : ℕ) (hr : 10 ≤ r) :
    ((r : ℚ) + 2) / (triangular r + 3) < barrier (r + 1) - barrier r := by
  have hrq : (10 : ℚ) ≤ r := by exact_mod_cast hr
  have hx : 0 ≤ (r : ℚ) - 10 := by linarith
  have hp : 0 <
      (((r : ℚ) - 10) ^ 4 + 34 * ((r : ℚ) - 10) ^ 3 +
        385 * ((r : ℚ) - 10) ^ 2 + 1472 * ((r : ℚ) - 10) + 112) /
        (4 * (r : ℚ) * ((r : ℚ) + 1) * ((r : ℚ) ^ 2 + r + 6)) := by positivity
  rw [← barrier_step_identity r hr] at hp
  linarith

theorem harmonic_base : harmonic (largeCutoff 10) < barrier 10 := by
  norm_num [largeCutoff, triangularNat, harmonic, barrier, Finset.sum_range_succ]

/-- A genuine induction, not a finite range of tested ranks. -/
theorem harmonic_lt_barrier (r : ℕ) (hr : 10 ≤ r) :
    harmonic (largeCutoff r) < barrier r := by
  induction r, hr using Nat.le_induction with
  | base => exact harmonic_base
  | succ r hr ih =>
    have hH := harmonic_cutoff_step r
    have hB := barrier_step_gt r hr
    linarith

/-- The paper's rational threshold T_r, with a freely specified cutoff. -/
def threshold (r n : ℕ) : ℚ :=
  let a := triangular r
  a * (a + 22 - r) / (2 * ((r : ℚ) - 1) * (a + 9)) +
    (2 * (r : ℚ) - 3) / ((r : ℚ) - 1) -
    (a * (a + 21) + 36) / (2 * ((n : ℚ) + 1) * (a + 9))

/-- T_1 from the paper, below T_r for either parity of a_r. -/
def thresholdLower (r : ℕ) : ℚ :=
  let a := triangular r
  a * (a + 22 - r) / (2 * ((r : ℚ) - 1) * (a + 9)) +
    (2 * (r : ℚ) - 3) / ((r : ℚ) - 1) -
    (a * (a + 21) + 36) / ((a + 3) * (a + 9))

theorem threshold_gap_identity (r : ℕ) (hr : 10 ≤ r) :
    thresholdLower r - barrier r =
      ((r : ℚ) ^ 3 * (((r : ℚ) - 10) * (2 * r + 15) + 2) +
        r * (111 * ((r : ℚ) - 10) + 210) + 972) /
      (2 * (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) ^ 2 + r + 6) *
        ((r : ℚ) ^ 2 + r + 18)) := by
  have hrq : (10 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℚ) ≠ 0 := by linarith
  have hr1 : (r : ℚ) - 1 ≠ 0 := by linarith
  unfold thresholdLower barrier triangular
  field_simp
  ring

theorem barrier_lt_thresholdLower (r : ℕ) (hr : 10 ≤ r) :
    barrier r < thresholdLower r := by
  have hrq : (10 : ℚ) ≤ r := by exact_mod_cast hr
  have hx : 0 ≤ (r : ℚ) - 10 := by linarith
  have hm : 0 < (r : ℚ) - 1 := by linarith
  have hp : 0 <
      ((r : ℚ) ^ 3 * (((r : ℚ) - 10) * (2 * r + 15) + 2) +
        r * (111 * ((r : ℚ) - 10) + 210) + 972) /
      (2 * (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) ^ 2 + r + 6) *
        ((r : ℚ) ^ 2 + r + 18)) := by positivity
  rw [← threshold_gap_identity r hr] at hp
  linarith

theorem thresholdLower_le_threshold (r : ℕ) :
    thresholdLower r ≤ threshold r (largeCutoff r) := by
  have ha := triangular_nonneg r
  have hn := (cutoff_bounds r).1
  have hden : (triangular r + 3) * (triangular r + 9) ≤
      2 * ((largeCutoff r : ℚ) + 1) * (triangular r + 9) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ triangular r * (triangular r + 21) + 36)
    (by positivity : 0 < (triangular r + 3) * (triangular r + 9)) hden
  unfold thresholdLower threshold
  linarith

theorem harmonic_lt_threshold (r : ℕ) (hr : 10 ≤ r) :
    harmonic (largeCutoff r) < threshold r (largeCutoff r) :=
  lt_of_lt_of_le (lt_trans (harmonic_lt_barrier r hr) (barrier_lt_thresholdLower r hr))
    (thresholdLower_le_threshold r)

/-- Separate the first two terms without assuming the remaining sum is empty. -/
theorem harmonic_tail (n : ℕ) (hn : 2 ≤ n) :
    harmonic n = 3 / 2 + ∑ j ∈ Finset.range (n - 2), 1 / ((j : ℚ) + 3) := by
  have h := harmonic_add 2 (n - 2)
  rw [show 2 + (n - 2) = n by omega] at h
  have h2 : harmonic 2 = 3 / 2 := by norm_num [harmonic, Finset.sum_range_succ]
  rw [h2] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem tailWeight_eq (r n : ℕ) (hn : 2 ≤ n) :
    tailWeight r n = ((r : ℚ) - 1) * (harmonic n - 3 / 2) -
      ((n : ℚ) - 2) * alpha r n := by
  have hs : (∑ j ∈ Finset.range (n - 2), ((r : ℚ) - 1) / ((j : ℚ) + 3)) =
      ((r : ℚ) - 1) * ∑ j ∈ Finset.range (n - 2), 1 / ((j : ℚ) + 3) := by
    simp [div_eq_mul_inv, Finset.mul_sum]
  have hH : (∑ j ∈ Finset.range (n - 2), 1 / ((j : ℚ) + 3)) = harmonic n - 3 / 2 := by
    linarith [harmonic_tail n hn]
  unfold tailWeight
  rw [Finset.sum_sub_distrib, hs, hH]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_sub hn]

/-- The existing gap and the paper's harmonic threshold are exactly the same base. -/
theorem seed_eq_threshold (r n : ℕ) (hr : 9 ≤ r) (hn : 2 ≤ n) :
    gap r n 10 (triangular r) =
      ((r : ℚ) - 1) * (triangular r + 9) * (threshold r n - harmonic n) := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have hr1 : (r : ℚ) - 1 ≠ 0 := by linarith
  have ha := triangular_nonneg r
  unfold gap upper
  rw [tailWeight_eq r n hn]
  unfold threshold volume alpha
  field_simp
  ring

/-- The only finite large-rank anchor retained by V03. -/
theorem rank_nine_seed : 0 < gap 9 (largeCutoff 9) 10 (triangular 9) := by
  norm_num [gap, upper, volume, alpha, triangular, largeCutoff, triangularNat,
    tailWeight, Finset.sum_range_succ]

/-- Every large-rank base is proved; no sampled rank cutoff remains. -/
theorem large_seed_pos (r : ℕ) (hr : 9 ≤ r) :
    0 < gap r (largeCutoff r) 10 (triangular r) := by
  by_cases h9 : r = 9
  · subst r; exact rank_nine_seed
  have h10 : 10 ≤ r := by omega
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have hm : 0 < (r : ℚ) - 1 := by linarith
  have ha := triangular_nonneg r
  rw [seed_eq_threshold r (largeCutoff r) hr (by have := cutoff_admissible r (by omega); omega)]
  exact mul_pos (mul_pos hm (by positivity)) (sub_pos.mpr (harmonic_lt_threshold r h10))

end NSP14.Ordinary.LargeSeed
