module

public import NSP14.Combinatorics.Sidon
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

namespace NSP14.Ordinary.SmallScalar

/-!
# Finite resources imply the SO3 scalar bound

`head` is H₁ and `tail j` is H_{j+2}; H₀ is the parameter `d`.
The support is arbitrary and need not lie below the cutoff.
Constructing these resources from the actual tangent cone is a later task.
-/

/-- One finite resource profile, with all caps and the budget imposed on that same profile. -/
structure Resources (r : ℕ) (e d : ℚ) where
  head : ℚ
  tail : ℕ → ℚ
  support : Finset ℕ
  tail_vanish : ∀ j, j ∉ support → tail j = 0
  head_nonneg : 0 ≤ head
  tail_nonneg : ∀ j, 0 ≤ tail j
  budget : d + head + ∑ j ∈ support, tail j ≤ d * volume e d
  head_cap : head ≤ e + d - 1 - triangular r
  tail_cap : ∀ j, tail j ≤ e + d - 1

/-- Residual tail weights below the cutoff are nonnegative. -/
theorem residual_weight_nonneg (r n j : ℕ) (hr : 4 ≤ r) (hj : j < n - 2) :
    0 ≤ ((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n := by
  have hrq : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hjn : j + 3 ≤ n + 1 := by omega
  have hjq : (j : ℚ) + 3 ≤ (n : ℚ) + 1 := by exact_mod_cast hjn
  exact sub_nonneg.mpr (div_le_div_of_nonneg_left (by linarith) (by positivity) hjq)

/-- At and beyond the cutoff the residual weights are nonpositive. -/
theorem residual_weight_nonpos (r n j : ℕ) (hr : 4 ≤ r)
    (hn : 2 ≤ n) (hj : n - 2 ≤ j) :
    ((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n ≤ 0 := by
  have hrq : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hjn : n + 1 ≤ j + 3 := by omega
  have hjq : (n : ℚ) + 1 ≤ (j : ℚ) + 3 := by exact_mod_cast hjn
  exact sub_nonpos.mpr (div_le_div_of_nonneg_left (by linarith) (by positivity) hjq)

/-- Drop the nonpositive residual tail, cap the remaining terms, and fill missing indices.
The arbitrary finite support `S` can contain indices above `n`. -/
theorem residual_tail_le (r n : ℕ) (S : Finset ℕ) (H : ℕ → ℚ) (M : ℚ)
    (hr : 4 ≤ r) (hn : r ≤ n)
    (hH : ∀ j, 0 ≤ H j) (hcap : ∀ j, H j ≤ M) :
    ∑ j ∈ S, (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n) * H j
      ≤ M * tailWeight r n := by
  have hM : 0 ≤ M := le_trans (hH 0) (hcap 0)
  let I := S ∩ Finset.range (n - 2)
  calc
    _ ≤ ∑ j ∈ I, (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n) * H j := by
      apply Finset.sum_le_sum_of_subset_of_nonpos Finset.inter_subset_left
      intro j hj hjI
      have hjn : n - 2 ≤ j := by
        by_contra h
        exact hjI (Finset.mem_inter.mpr ⟨hj, Finset.mem_range.mpr (by omega)⟩)
      exact mul_nonpos_of_nonpos_of_nonneg
        (residual_weight_nonpos r n j hr (by omega) hjn) (hH j)
    _ ≤ ∑ j ∈ I, M * (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn := Finset.mem_range.mp (Finset.mem_inter.mp hj).2
      have h := mul_le_mul_of_nonneg_left (hcap j) (residual_weight_nonneg r n j hr hjn)
      simpa only [mul_comm] using h
    _ ≤ ∑ j ∈ Finset.range (n - 2),
        M * (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro j hj _
      exact mul_nonneg hM (residual_weight_nonneg r n j hr (Finset.mem_range.mp hj))
    _ = M * tailWeight r n := by rw [tailWeight, Finset.mul_sum]

namespace Resources

variable {r : ℕ} {e d : ℚ} (R : Resources r e d)

/-- The paper's F_r, including every nonzero layer. -/
def scalar : ℚ :=
  ((r : ℚ) - 1) * d + ((r : ℚ) + 1) / 2 * R.head +
    ∑ j ∈ R.support, ((r : ℚ) - 1) / ((j : ℚ) + 3) * R.tail j

/-- SO3 follows from the resource fields; no upper-bound hypothesis is assumed. -/
theorem scalar_le_upper (n : ℕ) (hr : 4 ≤ r) (hn : r ≤ n) :
    R.scalar ≤ upper r n e d := by
  have hrq : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hnq : (r : ℚ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ alpha r n := by
    unfold alpha
    exact div_nonneg (by linarith) (by positivity)
  have ha1 : alpha r n < 1 := by
    unfold alpha
    rw [div_lt_one (by positivity)]
    linarith
  have hc : 0 ≤ ((r : ℚ) + 1) / 2 - alpha r n := by linarith
  have hbudget := mul_le_mul_of_nonneg_left R.budget ha
  have hhead := mul_le_mul_of_nonneg_left R.head_cap hc
  have htail := residual_tail_le r n R.support R.tail (e + d - 1) hr hn
    R.tail_nonneg R.tail_cap
  have hsplit :
      ∑ j ∈ R.support, (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n) * R.tail j =
      (∑ j ∈ R.support, ((r : ℚ) - 1) / ((j : ℚ) + 3) * R.tail j) -
        alpha r n * ∑ j ∈ R.support, R.tail j := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit] at htail
  unfold scalar upper
  nlinarith

/-- SO5 for natural shifts with the explicit corner condition. -/
theorem scalar_lt (r s t : ℕ)
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hr : 4 ≤ r ∧ r ≤ 8) (hcorner : r ≤ 5 ∨ s + t ≠ 0) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) := by
  exact scalar_lt_of_upper r s t R.scalar hr hcorner
    (R.scalar_le_upper (cutoff r) hr.1 (cutoff_admissible r hr).1)

/-- Resource-derived SO3 composed with the proved boundary Sidon counting. -/
theorem scalar_lt_of_boundary_sidon (m r s t : ℕ) [NeZero m]
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → ∃ B : Finset (ZMod m), IsSidon B ∧ B.card = r + 1) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) := by
  exact R.scalar_lt r s t hr (corner_condition_of_boundary_sidon m r s t hm hr hboundary)

/-- End-to-end numerical interface: resources plus numerical Apéry-pair data imply SO5. -/
theorem scalar_lt_of_apery_pairs (S : AddSubmonoid ℕ) (m r s t : ℕ) [NeZero m]
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → Nonempty (AperyPairData S m (r + 1))) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) := by
  apply R.scalar_lt_of_boundary_sidon m r s t hm hr
  intro h6 hs
  obtain ⟨D⟩ := hboundary h6 hs
  exact ⟨D.residues, D.residues_sidon, D.residues_card⟩

end Resources
end NSP14.Ordinary.SmallScalar
