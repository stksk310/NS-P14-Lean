module

public import NSP14.Ordinary.LowRank
public import NSP14.Ordinary.LargeScalar

@[expose] public section

open scoped BigOperators

namespace NSP14.Ordinary.Scalarization

open LowRank SmallScalar

def factor (r k : ℕ) : ℚ := Nat.choose (r - 1) (k - 1)

/-- Adjacent binomial coefficients, expressed without truncated subtraction. -/
theorem choose_balance (n k : ℕ) (hk : 1 ≤ k) :
    (k : ℚ) * (Nat.choose n k : ℚ) =
      ((n : ℚ) + 1 - k) * (Nat.choose n (k - 1) : ℚ) := by
  have heq : k - 1 + 1 = k := by omega
  have h := Nat.add_one_mul_choose_eq n (k - 1)
  have hp := Nat.choose_succ_succ' n (k - 1)
  rw [heq] at h hp
  rw [hp] at h
  have hq : ((n : ℚ) + 1) * (Nat.choose n (k - 1) : ℚ) =
      ((Nat.choose n (k - 1) : ℚ) + Nat.choose n k) * k := by exact_mod_cast h
  nlinarith

theorem binomial_balance (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (k : ℚ) * (Nat.choose (r - 1) k : ℚ) = ((r : ℚ) - k) * factor r k := by
  have h := choose_balance (r - 1) k hk
  rw [Nat.cast_sub hr] at h
  simpa [factor] using h

theorem factor_nonneg (r k : ℕ) : 0 ≤ factor r k := by unfold factor; positivity

theorem factor_pos (r k : ℕ) (hk : 1 ≤ k ∧ k ≤ r) : 0 < factor r k := by
  unfold factor
  exact_mod_cast (Nat.choose_pos (show k - 1 ≤ r - 1 by omega))

/-- The exceptional head weight simplifies to C(r−1,k−1)(r+1)/(k+1). -/
theorem head_weight_eq (r k : ℕ) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    weight r k 1 = factor r k * (((r : ℚ) + 1) / ((k : ℚ) + 1)) := by
  have hne : k ≠ 1 := by omega
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℚ) - 1 ≠ 0 := by linarith
  have hb := binomial_balance r k hr (by omega)
  simp only [weight, ite_eq_right hne]
  rw [hb]
  unfold factor
  field_simp [hk0]
  ring

theorem tail_weight_eq (r k j : ℕ) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    weight r k (j + 2) = factor r k *
      (((r : ℚ) - k) / ((j : ℚ) + 2 + k) + ((k : ℚ) - 1) / ((j : ℚ) + k)) := by
  have hne : k ≠ 1 := by omega
  have hb := binomial_balance r k hr (by omega)
  simp only [weight, ite_eq_right hne]
  rw [hb]
  unfold factor
  ring

/-- The k=2 tail comparison is sharp at r=4,j=0. -/
theorem second_tail_identity (r j : ℕ) :
    ((r : ℚ) - 1) / ((j : ℚ) + 3) -
      (((r : ℚ) - 2) / ((j : ℚ) + 4) + 1 / ((j : ℚ) + 2)) =
      (((r : ℚ) - 3) * ((j : ℚ) + 2) - 2) /
        (((j : ℚ) + 2) * ((j : ℚ) + 3) * ((j : ℚ) + 4)) := by
  field_simp
  ring

theorem normalized_tail_le (r k j : ℕ) (hr : 4 ≤ r) (hk : 2 ≤ k ∧ k ≤ r) :
    ((r : ℚ) - k) / ((j : ℚ) + 2 + k) + ((k : ℚ) - 1) / ((j : ℚ) + k) ≤
      ((r : ℚ) - 1) / ((j : ℚ) + 3) := by
  have hrq : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk.1
  have hkr : (k : ℚ) ≤ r := by exact_mod_cast hk.2
  have hj : (0 : ℚ) ≤ j := by positivity
  by_cases h2 : k = 2
  · subst k
    have hp := mul_nonneg (by linarith : 0 ≤ (r : ℚ) - 4)
      (by positivity : 0 ≤ (j : ℚ) + 2)
    have hnum : 0 ≤ ((r : ℚ) - 3) * ((j : ℚ) + 2) - 2 := by nlinarith
    have hfrac := div_nonneg hnum
      (by positivity : 0 ≤ ((j : ℚ) + 2) * ((j : ℚ) + 3) * ((j : ℚ) + 4))
    rw [← second_tail_identity] at hfrac
    norm_num at hfrac ⊢
    rw [show (j : ℚ) + 2 + 2 = (j : ℚ) + 4 by ring]
    exact hfrac
  · have hk3 : (3 : ℚ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    calc
      _ ≤ ((r : ℚ) - k) / ((j : ℚ) + 3) + ((k : ℚ) - 1) / ((j : ℚ) + 3) :=
        add_le_add
          (div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith))
          (div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith))
      _ = _ := by ring

theorem weight_zero_le (r k : ℕ) (hr : 4 ≤ r) (hk : 1 ≤ k ∧ k ≤ r) :
    weight r k 0 ≤ factor r k * weight r 1 0 := by
  by_cases h1 : k = 1
  · subst k; simp [weight, factor]
  have hk2 : 2 ≤ k := by omega
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk2
  have hb := binomial_balance r k (by omega) hk.1
  have hc := factor_nonneg r k
  have hB : (0 : ℚ) ≤ Nat.choose (r - 1) k := by positivity
  have hp := mul_nonneg (by linarith : 0 ≤ (k : ℚ) - 1) hB
  have hq := mul_nonneg (by linarith : 0 ≤ (k : ℚ) - 1) hc
  simp [weight, h1]
  nlinarith

theorem weight_head_le (r k : ℕ) (hr : 4 ≤ r) (hk : 1 ≤ k ∧ k ≤ r) :
    weight r k 1 ≤ factor r k * weight r 1 1 := by
  by_cases h1 : k = 1
  · subst k; simp [weight, factor]
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  rw [head_weight_eq r k (by omega) (by omega)]
  simp only [weight, ite_true]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) (factor_nonneg r k)

theorem weight_tail_le (r k j : ℕ) (hr : 4 ≤ r) (hk : 1 ≤ k ∧ k ≤ r) :
    weight r k (j + 2) ≤ factor r k * weight r 1 (j + 2) := by
  by_cases h1 : k = 1
  · subst k; simp [weight, factor]
  rw [tail_weight_eq r k j (by omega) (by omega)]
  simp only [weight, ite_true]
  exact mul_le_mul_of_nonneg_left (normalized_tail_le r k j hr ⟨by omega, hk.2⟩)
    (factor_nonneg r k)

/-- O_SCALAR for the actual finite weighted rows, including the top row. -/
theorem row_le_scalar (P : Layers) (r k : ℕ) (d : ℚ) (hr : 4 ≤ r)
    (hk : 1 ≤ k ∧ k ≤ r) (hd : 0 ≤ d) :
    P.row r k d ≤ (Nat.choose (r - 1) (k - 1) : ℚ) * P.row r 1 d := by
  have h0 := mul_le_mul_of_nonneg_right (weight_zero_le r k hr hk) hd
  have h1 := mul_le_mul_of_nonneg_right (weight_head_le r k hr hk) P.head_nonneg
  have ht : (∑ j ∈ P.support, weight r k (j + 2) * P.tail j) ≤
      factor r k * ∑ j ∈ P.support, weight r 1 (j + 2) * P.tail j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right (weight_tail_le r k j hr hk) (P.tail_nonneg j)
    simpa [mul_assoc] using h
  unfold Layers.row
  change _ ≤ factor r k * _
  nlinarith

end NSP14.Ordinary.Scalarization
