module

public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open scoped BigOperators

/-!
# First P14 block: five small-rank scalar gaps

Pure rational arithmetic, independent of tangent-cone semantics.
The bad corner for ranks 6–8 is an explicit hypothesis, to be discharged
by the future actual Apéry–Sidon module. No claim of P14 is made here.
-/
namespace NSP14.Ordinary.SmallScalar

/-- The triangular lower bound on the actual quadratic layer. -/
def triangular (r : ℕ) : ℚ := (r : ℚ) * ((r : ℚ) + 1) / 2

def volume (e d : ℚ) : ℚ := e + d / 2 - 3 / 2

def alpha (r n : ℕ) : ℚ := ((r : ℚ) - 1) / ((n : ℚ) + 1)

/-- The positive residual weights, with paper indices j=2,...,n-1. -/
def tailWeight (r n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n - 2), (((r : ℚ) - 1) / ((j : ℚ) + 3) - alpha r n)

/-- SO3, without assuming that any actual source has yet been constructed. -/
def upper (r n : ℕ) (e d : ℚ) : ℚ :=
  alpha r n * d * volume e d + ((r : ℚ) - 1 - alpha r n) * d +
  (((r : ℚ) + 1) / 2 - alpha r n) * (e + d - 1 - triangular r) +
  (e + d - 1) * tailWeight r n

def gap (r n : ℕ) (e d : ℚ) : ℚ := d * (volume e d + 1) - upper r n e d

def seed (r n : ℕ) : ℚ := gap r n ((r : ℚ) + 1) (triangular r)
def eSlope (r n : ℕ) : ℚ := gap r n ((r : ℚ) + 2) (triangular r) - seed r n
def dStep (r n : ℕ) : ℚ := gap r n ((r : ℚ) + 1) (triangular r + 1) - seed r n

/-- SO4 as an identity in independent rational shifts, not sampled parameters. -/
theorem gap_shift (r n : ℕ) (s t : ℚ) :
    gap r n ((r : ℚ) + 1 + s) (triangular r + t) =
      seed r n + s * eSlope r n + t * dStep r n +
        (1 - alpha r n) * (t * (t - 1) / 2 + s * t) := by
  simp only [seed, eSlope, dStep, gap, upper, volume]
  ring

/-- The two first differences satisfy the paper's formula for b. -/
theorem dStep_eq (r n : ℕ) :
    dStep r n = eSlope r n + 2 - alpha r n * ((r : ℚ) - 1) := by
  simp only [dStep, eSlope, seed, gap, upper, volume, triangular]
  ring

/-- Exact seed, e slope, and forward d difference for each of the five rows. -/
theorem row4 : seed 4 7 = 2443 / 280 ∧ eSlope 4 7 = 762 / 280 ∧
    dStep 4 7 = 1007 / 280 := by
  norm_num [seed, eSlope, dStep, gap, upper, volume, triangular, alpha,
    tailWeight, Finset.sum_range_succ]

theorem row5 : seed 5 10 = 39380 / 6930 ∧ eSlope 5 10 = 28429 / 6930 ∧
    dStep 5 10 = 32209 / 6930 := by
  norm_num [seed, eSlope, dStep, gap, upper, volume, triangular, alpha,
    tailWeight, Finset.sum_range_succ]

theorem row6 : seed 6 13 = -7479 / 72072 ∧ eSlope 6 13 = 424147 / 72072 ∧
    dStep 6 13 = 439591 / 72072 := by
  norm_num [seed, eSlope, dStep, gap, upper, volume, triangular, alpha,
    tailWeight, Finset.sum_range_succ]

theorem row7 : seed 7 17 = -12196485 / 2042040 ∧
    eSlope 7 17 = 17076937 / 2042040 ∧ dStep 7 17 = 17076937 / 2042040 := by
  norm_num [seed, eSlope, dStep, gap, upper, volume, triangular, alpha,
    tailWeight, Finset.sum_range_succ]

theorem row8 : seed 8 21 = -5070732 / 739024 ∧ eSlope 8 21 = 8418651 / 739024 ∧
    dStep 8 21 = 8250691 / 739024 := by
  norm_num [seed, eSlope, dStep, gap, upper, volume, triangular, alpha,
    tailWeight, Finset.sum_range_succ]

/-- Signs needed by the whole infinite quadrant, including adjacent gaps. -/
def Paid (r n : ℕ) : Prop :=
  0 < eSlope r n ∧ 0 < dStep r n ∧ 0 ≤ 1 - alpha r n ∧
    (0 < seed r n ∨ (0 < seed r n + eSlope r n ∧ 0 < seed r n + dStep r n))

theorem paid4 : Paid 4 7 := by
  unfold Paid
  simp only [row4.1, row4.2.1, row4.2.2]
  norm_num [alpha]
theorem paid5 : Paid 5 10 := by
  unfold Paid
  simp only [row5.1, row5.2.1, row5.2.2]
  norm_num [alpha]
theorem paid6 : Paid 6 13 := by
  unfold Paid
  simp only [row6.1, row6.2.1, row6.2.2]
  norm_num [alpha]
theorem paid7 : Paid 7 17 := by
  unfold Paid
  simp only [row7.1, row7.2.1, row7.2.2]
  norm_num [alpha]
theorem paid8 : Paid 8 21 := by
  unfold Paid
  simp only [row8.1, row8.2.1, row8.2.2]
  norm_num [alpha]

lemma nat_quadratic_nonneg (t : ℕ) : 0 ≤ (t : ℚ) * ((t : ℚ) - 1) / 2 := by
  by_cases h : t = 0
  · subst t; norm_num
  · have ht : (1 : ℚ) ≤ t := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)

/-- Universal positivity. The corner condition is explicit and not a new axiom. -/
theorem gap_pos_of_paid (r n s t : ℕ) (hp : Paid r n)
    (hadmissible : 0 < seed r n ∨ s + t ≠ 0) :
    0 < gap r n ((r : ℚ) + 1 + s) (triangular r + t) := by
  rw [gap_shift]
  obtain ⟨hA, hb, hbeta, hg⟩ := hp
  have hs : (0 : ℚ) ≤ s := by positivity
  have ht : (0 : ℚ) ≤ t := by positivity
  have hsa : 0 ≤ (s : ℚ) * eSlope r n := mul_nonneg hs (le_of_lt hA)
  have htb : 0 ≤ (t : ℚ) * dStep r n := mul_nonneg ht (le_of_lt hb)
  have htail : 0 ≤ (1 - alpha r n) *
      ((t : ℚ) * ((t : ℚ) - 1) / 2 + (s : ℚ) * t) :=
    mul_nonneg hbeta (add_nonneg (nat_quadratic_nonneg t) (mul_nonneg hs ht))
  rcases hadmissible with hpos | hcorner
  · linarith
  · rcases hg with hpos | ⟨hga, hgb⟩
    · linarith
    · by_cases hsz : s = 0
      · have htn : 1 ≤ t := by omega
        have htq : (1 : ℚ) ≤ t := by exact_mod_cast htn
        have : dStep r n ≤ (t : ℚ) * dStep r n := by nlinarith
        linarith
      · have hsn : 1 ≤ s := by omega
        have hsq : (1 : ℚ) ≤ s := by exact_mod_cast hsn
        have : eSlope r n ≤ (s : ℚ) * eSlope r n := by nlinarith
        linarith

def cutoff (r : ℕ) : ℕ :=
  if r = 4 then 7 else if r = 5 then 10 else if r = 6 then 13 else
    if r = 7 then 17 else 21

/-- Each selected cutoff has the range needed by the future resource bound. -/
theorem cutoff_admissible (r : ℕ) (hr : 4 ≤ r ∧ r ≤ 8) :
    r ≤ cutoff r ∧ 0 < alpha r (cutoff r) ∧ alpha r (cutoff r) < 1 := by
  obtain ⟨hlo, hhi⟩ := hr
  interval_cases r <;> norm_num [cutoff, alpha]

/-- The complete five-row numerical block for all integer shifts.
Actual source feasibility at the three exceptional corners is a later module. -/
theorem small_gap_pos (r s t : ℕ) (hr : 4 ≤ r ∧ r ≤ 8)
    (hcorner : r ≤ 5 ∨ s + t ≠ 0) :
    0 < gap r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t) := by
  have hadm : 0 < seed r (cutoff r) ∨ s + t ≠ 0 := by
    rcases hcorner with hlow | hn
    · have : r = 4 ∨ r = 5 := by omega
      rcases this with h | h <;> subst r
      · left; norm_num [cutoff, row4.1]
      · left; norm_num [cutoff, row5.1]
    · exact Or.inr hn
  apply gap_pos_of_paid r (cutoff r) s t _ hadm
  obtain ⟨hlo, hhi⟩ := hr
  interval_cases r
  · simpa [cutoff] using paid4
  · simpa [cutoff] using paid5
  · simpa [cutoff] using paid6
  · simpa [cutoff] using paid7
  · simpa [cutoff] using paid8

/-- Usable interface: once SO3 is supplied by the resource module, the scalar is paid. -/
theorem scalar_lt_of_upper (r s t : ℕ) (F : ℚ) (hr : 4 ≤ r ∧ r ≤ 8)
    (hcorner : r ≤ 5 ∨ s + t ≠ 0)
    (hupper : F ≤ upper r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t)) :
    F < (triangular r + t) * (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) := by
  have h := small_gap_pos r s t hr hcorner
  unfold gap at h
  linarith

end NSP14.Ordinary.SmallScalar
