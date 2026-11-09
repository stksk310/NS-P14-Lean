module

public import NSP14.Ordinary.Resources

@[expose] public section

open scoped BigOperators

namespace NSP14.Ordinary.LowRank

open SmallScalar

/-!
# The numerical part of O_LOW

The weights are V02 (7.3). This module proves inequalities for those finite
weighted sums. Actual Koszul/Tor ranks and target margins are not constructed here.
Rank two uses no triangular lower bound on the deficit.
-/

/-- The nonnegative layers H₁ and H_{j+2}, with an arbitrary finite tail support. -/
structure Layers where
  head : ℚ
  tail : ℕ → ℚ
  support : Finset ℕ
  tail_vanish : ∀ j, j ∉ support → tail j = 0
  head_nonneg : 0 ≤ head
  tail_nonneg : ∀ j, 0 ≤ tail j

/-- V02 (7.3), with explicit values at layers zero, one, and j+2.
The non-first-row formula is used only for 2 ≤ k ≤ r. -/
def weight (r k : ℕ) : ℕ → ℚ
  | 0 => if k = 1 then (r : ℚ) - 1 else (Nat.choose (r - 1) k : ℚ)
  | 1 => if k = 1 then ((r : ℚ) + 1) / 2 else
      (k : ℚ) * (Nat.choose (r - 1) k : ℚ) / ((k : ℚ) + 1) +
      ((k : ℚ) - 1) * (Nat.choose (r - 1) (k - 1) : ℚ) / ((k : ℚ) - 1)
  | j + 2 => if k = 1 then ((r : ℚ) - 1) / ((j : ℚ) + 3) else
      (k : ℚ) * (Nat.choose (r - 1) k : ℚ) / ((j : ℚ) + 2 + k) +
      ((k : ℚ) - 1) * (Nat.choose (r - 1) (k - 1) : ℚ) / ((j : ℚ) + k)

namespace Layers

variable (P : Layers)

/-- Total resource S, with H₀=d. -/
def mass (d : ℚ) : ℚ := d + P.head + ∑ j ∈ P.support, P.tail j

/-- The full weighted row ∑ W_k(t) H_t; the parameter d is H₀. -/
def row (r k : ℕ) (d : ℚ) : ℚ :=
  weight r k 0 * d + weight r k 1 * P.head +
    ∑ j ∈ P.support, weight r k (j + 2) * P.tail j

theorem tail_sum_nonneg : 0 ≤ ∑ j ∈ P.support, P.tail j :=
  Finset.sum_nonneg (fun j _ => P.tail_nonneg j)

/-- A uniform cap on tail weights bounds the entire finite row. -/
theorem row_le (r k : ℕ) (d C : ℚ) (hw : ∀ j, weight r k (j + 2) ≤ C) :
    P.row r k d ≤ weight r k 0 * d + weight r k 1 * P.head +
      C * ∑ j ∈ P.support, P.tail j := by
  unfold row
  have h := Finset.sum_le_sum (s := P.support)
    (fun j _ => mul_le_mul_of_nonneg_right (hw j) (P.tail_nonneg j))
  rw [← Finset.mul_sum] at h
  linarith

/-- First of the two rank-two estimates in V02 §9. -/
theorem rank_two_first_le_mass (d : ℚ) :
    P.row 2 1 d ≤ 3 / 2 * P.mass d - d / 2 := by
  have hb := P.row_le 2 1 d (1 / 2) (by
    intro j
    norm_num [weight]
    rw [← one_div]
    apply (div_le_iff₀ (by positivity)).2
    have hj : (0 : ℚ) ≤ j := by positivity
    linarith)
  norm_num [weight] at hb
  have hs := P.tail_sum_nonneg
  unfold mass
  linarith

/-- Second rank-two estimate; H₁≤2d is an explicit additional resource fact. -/
theorem rank_two_first_le_linear (d : ℚ) (hh : P.head ≤ 2 * d) :
    P.row 2 1 d ≤ 5 / 2 * d + P.mass d / 2 := by
  have hb := P.row_le 2 1 d (1 / 2) (by
    intro j
    norm_num [weight]
    rw [← one_div]
    apply (div_le_iff₀ (by positivity)).2
    have hj : (0 : ℚ) ≤ j := by positivity
    linarith)
  norm_num [weight] at hb
  unfold mass
  linarith

theorem rank_two_top_le (d : ℚ) : P.row 2 2 d ≤ P.mass d - d := by
  have hb := P.row_le 2 2 d 1 (by
    intro j
    norm_num [weight]
    rw [← one_div]
    apply (div_le_iff₀ (by positivity)).2
    have hj : (0 : ℚ) ≤ j := by positivity
    linarith)
  norm_num [weight] at hb
  unfold mass
  linarith

/-- All rank-two numerical rows, including d=0 and the V=3 boundary. -/
theorem rank_two_bounds (e d : ℚ) (hd : 0 ≤ d)
    (hb : P.mass d ≤ d * volume e d) (hh : P.head ≤ 2 * d) :
    P.row 2 1 d ≤ d * (volume e d + 1) ∧
    P.row 2 2 d ≤ d * (volume e d - 1) := by
  constructor
  · by_cases hV : volume e d ≤ 3
    · have h := P.rank_two_first_le_mass d
      have hp := mul_nonneg hd (sub_nonneg.mpr hV)
      nlinarith
    · have h := P.rank_two_first_le_linear d hh
      have hp := mul_nonneg hd (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hV)))
      nlinarith
  · have h := P.rank_two_top_le d
    nlinarith

/-- Rank-three first-row estimate before paying it with the target margin. -/
theorem rank_three_first_le (d : ℚ) :
    P.row 3 1 d ≤ 4 / 3 * d + 4 / 3 * P.head + 2 / 3 * P.mass d := by
  have hb := P.row_le 3 1 d (2 / 3) (by
    intro j
    norm_num [weight]
    apply (div_le_iff₀ (by positivity)).2
    have hj : (0 : ℚ) ≤ j := by positivity
    linarith)
  norm_num [weight] at hb
  unfold mass
  linarith

/-- Rank-three second-row estimate, using H₁≤3d from the same profile. -/
theorem rank_three_second_le (d : ℚ) (hh : P.head ≤ 3 * d) :
    P.row 3 2 d ≤ 3 * d + 3 / 2 * P.mass d := by
  have hb := P.row_le 3 2 d (3 / 2) (by
    intro j
    norm_num [weight]
    have hj : (0 : ℚ) ≤ j := by positivity
    have h1 : (2 : ℚ) / ((j : ℚ) + 2 + 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    have h2 : (2 : ℚ) / ((j : ℚ) + 2) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    linarith)
  norm_num [weight] at hb
  unfold mass
  linarith

theorem rank_three_top_le (d : ℚ) : P.row 3 3 d ≤ P.mass d - d := by
  have hb := P.row_le 3 3 d 1 (by
    intro j
    norm_num [weight]
    apply (div_le_iff₀ (by positivity)).2
    have hj : (0 : ℚ) ≤ j := by positivity
    linarith)
  norm_num [weight] at hb
  unfold mass
  linarith

end Layers

/-- The positive first-row margin, valid even for rational e≥4 and d≥6. -/
theorem rank_three_margin_pos (e d : ℚ) (he : 4 ≤ e) (hd : 6 ≤ d) :
    0 < d * (volume e d - 1) - 4 * (e + d - 7) := by
  have hp := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr he)
  unfold volume
  nlinarith [sq_nonneg (d - 6)]

namespace Layers

variable (P : Layers)

/-- All three rank-three rows under the §9 resource conditions. -/
theorem rank_three_bounds (e d : ℚ) (he : 4 ≤ e) (hd : 6 ≤ d)
    (hb : P.mass d ≤ d * volume e d) (hh : P.head ≤ 3 * d)
    (hc : P.head ≤ e + d - 7) :
    P.row 3 1 d ≤ d * (volume e d + 1) ∧
    P.row 3 2 d ≤ 2 * d * (volume e d + 1) ∧
    P.row 3 3 d ≤ d * (volume e d - 1) := by
  have hfirst := P.rank_three_first_le d
  have hsecond := P.rank_three_second_le d hh
  have htop := P.rank_three_top_le d
  have hmargin := rank_three_margin_pos e d he hd
  have hV : 2 ≤ volume e d := by unfold volume; linarith
  have hp := mul_nonneg (by linarith : 0 ≤ d) (sub_nonneg.mpr hV)
  constructor
  · nlinarith
  constructor <;> nlinarith

end Layers
end NSP14.Ordinary.LowRank

namespace NSP14.Ordinary.SmallScalar.Resources

open LowRank

variable {r : ℕ} {e d : ℚ} (R : Resources r e d)

/-- Forget only the extra resource constraints, preserving the very same layers. -/
def toLayers : Layers where
  head := R.head
  tail := R.tail
  support := R.support
  tail_vanish := R.tail_vanish
  head_nonneg := R.head_nonneg
  tail_nonneg := R.tail_nonneg

/-- The first weighted row is exactly the existing Block03 scalar. -/
theorem row_one_eq_scalar : R.toLayers.row r 1 d = R.scalar := by
  simp [Layers.row, weight, toLayers, scalar]

/-- Rank three composes with Block03 data and the additional linear head cap. -/
theorem rank_three_bounds (R : Resources 3 e d) (he : 4 ≤ e) (hd : 6 ≤ d)
    (hh : R.head ≤ 3 * d) :
    R.toLayers.row 3 1 d ≤ d * (volume e d + 1) ∧
    R.toLayers.row 3 2 d ≤ 2 * d * (volume e d + 1) ∧
    R.toLayers.row 3 3 d ≤ d * (volume e d - 1) := by
  apply R.toLayers.rank_three_bounds e d he hd
  · exact R.budget
  · exact hh
  · have hc := R.head_cap
    norm_num [triangular] at hc
    change R.head ≤ e + d - 7
    linarith

end NSP14.Ordinary.SmallScalar.Resources
