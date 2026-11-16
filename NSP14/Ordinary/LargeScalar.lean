module

public import NSP14.Ordinary.LargeSeed

@[expose] public section

namespace NSP14.Ordinary.LargeScalar

open SmallScalar LargeSeed

/-!
# Large-rank scalar closure

The unchanged Block05 seed implies positivity for all rational e≥10, d≥a_r,
r≥9. No actual tangent-cone or Tor construction is claimed here.
-/

def baseSlope (r n : ℕ) : ℚ := gap r n 11 (triangular r) - gap r n 10 (triangular r)
def baseStep (r n : ℕ) : ℚ := gap r n 10 (triangular r + 1) - gap r n 10 (triangular r)

def correction (r n : ℕ) : ℚ :=
  let a := triangular r
  a * (-a * ((n : ℚ) - r + 2) - n * ((r : ℚ) - 4) + 3) / (2 * ((n : ℚ) + 1))

def stepLower (r n : ℕ) : ℚ :=
  -correction r n / (triangular r + 9) + 11 - r - 8 * alpha r n

/-- The paper's F₁, at the smallest permitted rational cutoff (a+1)/2. -/
def floorStep (r : ℕ) : ℚ :=
  let a := triangular r
  a / 2 - 3 * (r : ℚ) / 2 + 11 / 2 +
    3 * (5 * r + 31) / (2 * (a + 9)) - 17 * ((r : ℚ) - 1) / (a + 3)

theorem triangular_large (r : ℕ) (hr : 9 ≤ r) : 4 * (r : ℚ) ≤ triangular r := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have hp := mul_nonneg (by positivity : (0 : ℚ) ≤ r) (by linarith : 0 ≤ (r : ℚ) - 7)
  unfold triangular
  nlinarith

theorem alpha_bounds (r : ℕ) (hr : 9 ≤ r) :
    0 < alpha r (largeCutoff r) ∧ alpha r (largeCutoff r) < 1 := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have hn : (r : ℚ) ≤ largeCutoff r := by
    exact_mod_cast LargeSeed.cutoff_admissible r (by omega)
  unfold alpha
  constructor
  · exact div_pos (by linarith) (by positivity)
  · apply (div_lt_one (by positivity)).2
    linarith

/-- S21, directly from the existing definitions. -/
theorem seed_slope_identity (r n : ℕ) :
    gap r n 10 (triangular r) = (triangular r + 9) * baseSlope r n + correction r n := by
  unfold baseSlope gap upper volume correction alpha
  field_simp
  ring

theorem step_identity (r n : ℕ) :
    baseStep r n = baseSlope r n + 11 - r - 8 * alpha r n := by
  unfold baseStep baseSlope gap upper volume
  ring

theorem correction_neg (r : ℕ) (hr : 9 ≤ r) : correction r (largeCutoff r) < 0 := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have ha := triangular_large r hr
  have hn : (r : ℚ) ≤ largeCutoff r := by
    exact_mod_cast LargeSeed.cutoff_admissible r (by omega)
  have hp := mul_nonneg (by linarith : 0 ≤ triangular r) (sub_nonneg.mpr hn)
  have hq := mul_nonneg (by positivity : (0 : ℚ) ≤ largeCutoff r)
    (by linarith : 0 ≤ (r : ℚ) - 4)
  have hbr : -triangular r * ((largeCutoff r : ℚ) - r + 2) -
      largeCutoff r * ((r : ℚ) - 4) + 3 < 0 := by nlinarith
  unfold correction
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hbr) (by positivity)

theorem baseSlope_lower (r : ℕ) (hr : 9 ≤ r) :
    -correction r (largeCutoff r) / (triangular r + 9) < baseSlope r (largeCutoff r) := by
  have ha := LargeSeed.triangular_nonneg r
  have hg := large_seed_pos r hr
  have hid := seed_slope_identity r (largeCutoff r)
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith

theorem baseSlope_pos (r : ℕ) (hr : 9 ≤ r) : 0 < baseSlope r (largeCutoff r) := by
  have h := baseSlope_lower r hr
  have hc := correction_neg r hr
  have ha := LargeSeed.triangular_nonneg r
  have hp : 0 < -correction r (largeCutoff r) / (triangular r + 9) :=
    div_pos (neg_pos.mpr hc) (by positivity)
  linarith

/-- A continuous cutoff comparison replaces the two parity cases F₀,F₁. -/
theorem floor_comparison_identity (r n : ℕ) :
    stepLower r n - floorStep r =
      (2 * (n : ℚ) - triangular r - 1) * ((r : ℚ) - 1) *
        ((triangular r) ^ 2 + 17 * triangular r + 144) /
      (2 * (triangular r + 9) * ((n : ℚ) + 1) * (triangular r + 3)) := by
  have ha := LargeSeed.triangular_nonneg r
  unfold stepLower floorStep correction alpha triangular
  field_simp
  ring

theorem floorStep_le_stepLower (r : ℕ) (hr : 9 ≤ r) :
    floorStep r ≤ stepLower r (largeCutoff r) := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have hfloor := (cutoff_bounds r).1
  have hf : 0 ≤ 2 * (largeCutoff r : ℚ) - triangular r - 1 := by linarith
  have hm : 0 ≤ (r : ℚ) - 1 := by linarith
  have ha := LargeSeed.triangular_nonneg r
  have hp : 0 ≤
      (2 * (largeCutoff r : ℚ) - triangular r - 1) * ((r : ℚ) - 1) *
        ((triangular r) ^ 2 + 17 * triangular r + 144) /
      (2 * (triangular r + 9) * ((largeCutoff r : ℚ) + 1) * (triangular r + 3)) := by positivity
  rw [← floor_comparison_identity r (largeCutoff r)] at hp
  linarith

/-- For r≥9 the bound is stronger than the paper's uniform r≥4 estimate. -/
theorem floorStep_gt (r : ℕ) (hr : 9 ≤ r) : 5 / 4 < floorStep r := by
  have hrq : (9 : ℚ) ≤ r := by exact_mod_cast hr
  have ha := triangular_large r hr
  have ha0 : 0 ≤ triangular r := by linarith
  have hmain : 11 / 2 ≤ triangular r / 2 - 3 * (r : ℚ) / 2 + 11 / 2 := by linarith
  have hratio : ((r : ℚ) - 1) / (triangular r + 3) < 1 / 4 := by
    apply (div_lt_iff₀ (by linarith)).2
    linarith
  have hratio17 : 17 * ((r : ℚ) - 1) / (triangular r + 3) < 17 / 4 := by
    calc
      _ = 17 * (((r : ℚ) - 1) / (triangular r + 3)) := by ring
      _ < 17 / 4 := by linarith
  have hpos : 0 < 3 * (5 * (r : ℚ) + 31) / (2 * (triangular r + 9)) := by positivity
  dsimp only [floorStep]
  linarith

theorem baseStep_gt (r : ℕ) (hr : 9 ≤ r) : 5 / 4 < baseStep r (largeCutoff r) := by
  have hA := baseSlope_lower r hr
  have hF := floorStep_le_stepLower r hr
  have hpos := floorStep_gt r hr
  rw [step_identity]
  unfold stepLower at hF
  linarith

/-- Recenter SO4 at e=10, and combine its linear t term with −(1−α)t/2. -/
theorem quadrant_identity (r n : ℕ) (s t : ℚ) :
    gap r n (10 + s) (triangular r + t) = gap r n 10 (triangular r) +
      s * baseSlope r n + t * (baseStep r n - (1 - alpha r n) / 2) +
      (1 - alpha r n) * (t ^ 2 / 2 + s * t) := by
  unfold baseSlope baseStep gap upper volume
  ring

/-- Nonnegative rational shifts, including the interval 0<t<1. -/
theorem gap_pos_shift (r : ℕ) (s t : ℚ) (hr : 9 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < gap r (largeCutoff r) (10 + s) (triangular r + t) := by
  have hg := large_seed_pos r hr
  have hA := baseSlope_pos r hr
  have hb := baseStep_gt r hr
  obtain ⟨ha0, ha1⟩ := alpha_bounds r hr
  have hbeta : 0 ≤ 1 - alpha r (largeCutoff r) := by linarith
  have hlin : 0 ≤ baseStep r (largeCutoff r) - (1 - alpha r (largeCutoff r)) / 2 := by linarith
  have hsA := mul_nonneg hs (le_of_lt hA)
  have htb := mul_nonneg ht hlin
  have hquad : 0 ≤ (1 - alpha r (largeCutoff r)) * (t ^ 2 / 2 + s * t) :=
    mul_nonneg hbeta (add_nonneg
    (div_nonneg (sq_nonneg t) (by norm_num)) (mul_nonneg hs ht))
  rw [quadrant_identity]
  linarith

/-- The full large-rank numerical gap, with rational e and d. -/
theorem large_gap_pos (r : ℕ) (e d : ℚ) (hr : 9 ≤ r) (he : 10 ≤ e)
    (hd : triangular r ≤ d) : 0 < gap r (largeCutoff r) e d := by
  have h := gap_pos_shift r (e - 10) (d - triangular r) hr
    (sub_nonneg.mpr he) (sub_nonneg.mpr hd)
  have heq : 10 + (e - 10) = e := by ring
  have hdq : triangular r + (d - triangular r) = d := by ring
  rw [heq, hdq] at h
  exact h

end NSP14.Ordinary.LargeScalar

namespace NSP14.Ordinary.SmallScalar.Resources

open LargeSeed LargeScalar

/-- Block03's resource-derived upper bound composed with the full large-rank gap. -/
theorem scalar_lt_large {r : ℕ} {e d : ℚ} (R : Resources r e d)
    (hr : 9 ≤ r) (he : 10 ≤ e) (hd : triangular r ≤ d) :
    R.scalar < d * (volume e d + 1) := by
  have hupper := R.scalar_le_upper (largeCutoff r) (by omega)
    (LargeSeed.cutoff_admissible r (by omega))
  have hgap := large_gap_pos r e d hr he hd
  unfold gap at hgap
  linarith

end NSP14.Ordinary.SmallScalar.Resources
