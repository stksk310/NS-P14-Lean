module

public import NSP14.Ordinary.TargetMargin

@[expose] public section

namespace NSP14.Ordinary.NumericalClosure

open SmallScalar LowRank Scalarization

/-!
# One ordinary numerical comparison for every cut rank and every row

The inputs are one finite layer profile with simultaneous resource bounds.
Actual construction of those resources, the Tor bound, and the target Betti
formula remain semantic work. None is silently inferred from these numbers.
-/

structure Data (r e d : ℕ) where
  layers : Layers
  rank_lo : 2 ≤ r
  embed : r + 1 ≤ e
  budget : layers.mass d ≤ (d : ℚ) * volume e d
  head_linear : layers.head ≤ (r : ℚ) * d
  triangular_bound : 3 ≤ r → triangular r ≤ (d : ℚ)
  head_cap : 3 ≤ r → layers.head ≤ (e : ℚ) + d - 1 - triangular r
  tail_cap : ∀ j, layers.tail j ≤ (e : ℚ) + d - 1

/-- Sidon evidence is requested only at the small maximal-cut boundary. -/
def Boundary (r e d : ℕ) : Prop :=
  6 ≤ r → r ≤ 8 → e = r + 1 →
    ∃ B : Finset (ZMod (e + d)), IsSidon B ∧ B.card = e

namespace Data

variable {r e d : ℕ} (D : Data r e d)

/-- The same profile supplies Block03's resource record whenever r≥3. -/
def toResources (hr : 3 ≤ r) : Resources r e d where
  head := D.layers.head
  tail := D.layers.tail
  support := D.layers.support
  tail_vanish := D.layers.tail_vanish
  head_nonneg := D.layers.head_nonneg
  tail_nonneg := D.layers.tail_nonneg
  budget := D.budget
  head_cap := D.head_cap hr
  tail_cap := D.tail_cap

include D in
theorem deficit_nat_lower (hr : 3 ≤ r) : LargeSeed.triangularNat r ≤ d := by
  have h := D.triangular_bound hr
  rw [← LargeSeed.triangularNat_cast] at h
  exact_mod_cast h

include D in
theorem parameterization (hr : 3 ≤ r) :
    (r : ℚ) + 1 + ((e - (r + 1) : ℕ) : ℚ) = e ∧
    triangular r + ((d - LargeSeed.triangularNat r : ℕ) : ℚ) = d := by
  have he : r + 1 + (e - (r + 1)) = e := by have := D.embed; omega
  have hd : LargeSeed.triangularNat r + (d - LargeSeed.triangularNat r) = d := by
    have := D.deficit_nat_lower hr
    omega
  constructor
  · exact_mod_cast he
  · rw [← LargeSeed.triangularNat_cast]
    exact_mod_cast hd

include D in
theorem small_corner (hr : 4 ≤ r ∧ r ≤ 8) (hb : Boundary r e d) :
    r ≤ 5 ∨ (e - (r + 1)) + (d - LargeSeed.triangularNat r) ≠ 0 := by
  let s := e - (r + 1)
  let t := d - LargeSeed.triangularNat r
  have hs : r + 1 + s = e := by dsimp [s]; have := D.embed; omega
  have ht : LargeSeed.triangularNat r + t = d := by
    dsimp [t]; have := D.deficit_nat_lower (by omega); omega
  have : NeZero (e + d) := ⟨by have := D.embed; omega⟩
  have hm : e + d = (r + 1 + s) + r * (r + 1) / 2 + t := by
    unfold LargeSeed.triangularNat at ht
    omega
  apply corner_condition_of_boundary_sidon (e + d) r s t hm hr
  intro h6 hsz
  have he : e = r + 1 := by omega
  obtain ⟨B, hB, hc⟩ := hb h6 hr.2 he
  exact ⟨B, hB, by omega⟩

/-- All r≥4 use the existing small/large scalar theorems on the same resources. -/
theorem scalar_lt (hr : 4 ≤ r) (hb : Boundary r e d) :
    D.layers.row r 1 d < (d : ℚ) * (volume e d + 1) := by
  let R := D.toResources (by omega)
  have hrow : D.layers.row r 1 d = R.scalar := by
    simpa [R, toResources, Resources.toLayers] using R.row_one_eq_scalar
  rw [hrow]
  by_cases hlarge : 9 ≤ r
  · apply R.scalar_lt_large hlarge
    · have he : 10 ≤ e := by have := D.embed; omega
      exact_mod_cast he
    · exact D.triangular_bound (by omega)
  · have hsmall : 4 ≤ r ∧ r ≤ 8 := ⟨hr, by omega⟩
    have hgap := small_gap_pos r (e - (r + 1)) (d - LargeSeed.triangularNat r)
      hsmall (D.small_corner hsmall hb)
    obtain ⟨heq, hdq⟩ := D.parameterization (by omega)
    rw [heq, hdq] at hgap
    have hu := R.scalar_le_upper (cutoff r) hr (SmallScalar.cutoff_admissible r hsmall).1
    unfold gap at hgap
    linarith

/-- Numeric capacity for every row, treating rank two without triangular assumptions. -/
theorem row_capacity (k : ℕ) (hk : 1 ≤ k ∧ k ≤ r) (hb : Boundary r e d) :
    D.layers.row r k d ≤ (d : ℚ) * (volume e d + 1) * factor r k := by
  by_cases h2 : r = 2
  · subst r
    have hh : D.layers.head ≤ 2 * (d : ℚ) := by simpa using D.head_linear
    have h := D.layers.rank_two_bounds e d (by positivity) D.budget hh
    have hc : k = 1 ∨ k = 2 := by omega
    rcases hc with h1 | h2 <;> subst k <;> norm_num [factor]
    · exact h.1
    · have hd : (0 : ℚ) ≤ d := by positivity
      nlinarith [h.2]
  by_cases h3 : r = 3
  · subst r
    have he : (4 : ℚ) ≤ e := by exact_mod_cast D.embed
    have hd : (6 : ℚ) ≤ d := by
      have h := D.triangular_bound (by decide)
      norm_num [triangular] at h
      exact_mod_cast h
    have hh : D.layers.head ≤ 3 * (d : ℚ) := by simpa using D.head_linear
    have hc : D.layers.head ≤ (e : ℚ) + d - 7 := by
      have h := D.head_cap (by decide)
      norm_num [triangular] at h
      linarith
    have h := D.layers.rank_three_bounds e d he hd D.budget hh hc
    have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk3 with h1 | h2 | h3 <;> subst k <;> norm_num [factor]
    · exact h.1
    · nlinarith [h.2.1]
    · nlinarith [h.2.2]
  have hr4 : 4 ≤ r := by have := D.rank_lo; omega
  have hrow := row_le_scalar D.layers r k d hr4 hk (by positivity)
  have hscalar := D.scalar_lt hr4 hb
  have hmul := mul_le_mul_of_nonneg_left (le_of_lt hscalar) (factor_nonneg r k)
  change _ ≤ _ * factor r k
  change _ ≤ factor r k * _ at hrow
  nlinarith

/-- One theorem covers every ordinary numerical row and the concrete target R_k. -/
theorem all_rows (hb : Boundary r e d) :
    ∀ k, 1 ≤ k ∧ k ≤ r →
      TargetMargin.lower e r k + D.layers.row r k d ≤ TargetMargin.target e d r k := by
  intro k hk
  have hrow := D.row_capacity k hk hb
  have hmargin := TargetMargin.target_margin e d r k (by have := D.rank_lo; omega) hk.1
  linarith

/-- Numerical Apéry-pair data supply the same boundary evidence as Block02. -/
theorem all_rows_of_apery_pairs (S : AddSubmonoid ℕ)
    (hb : 6 ≤ r → r ≤ 8 → e = r + 1 → Nonempty (AperyPairData S (e + d) e)) :
    ∀ k, 1 ≤ k ∧ k ≤ r →
      TargetMargin.lower e r k + D.layers.row r k d ≤ TargetMargin.target e d r k := by
  apply D.all_rows
  intro h6 h8 he
  obtain ⟨A⟩ := hb h6 h8 he
  exact ⟨A.residues, A.residues_sidon, A.residues_card⟩

/-- Handoff for future actual Tor bounds; no actual rank is constructed here. -/
theorem relative_rows (c : ℕ → ℚ) (hb : Boundary r e d)
    (hc : ∀ k, 1 ≤ k ∧ k ≤ r → c k ≤ TargetMargin.lower e r k + D.layers.row r k d) :
    ∀ k, 1 ≤ k ∧ k ≤ r → c k ≤ TargetMargin.target e d r k := by
  intro k hk
  exact le_trans (hc k hk) (D.all_rows hb k hk)

end Data
end NSP14.Ordinary.NumericalClosure
