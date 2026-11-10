module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LowRank
open NSP14.Ordinary.Scalarization NSP14.Ordinary.NumericalClosure
open NSP14.Ordinary

namespace NSP14.Block07Audit

-- The first-row target margin is exact, not a strict or rounded capacity.
theorem first_margin_exact (e d r : ℕ) (hr : 1 ≤ r) :
    TargetMargin.target e d r 1 - TargetMargin.lower e r 1 =
      (d : ℚ) * (volume e d + 1) := by
  induction d with
  | zero => rw [TargetMargin.target_zero e r 1 hr]; simp
  | succ d ih =>
    have h := TargetMargin.target_step e d r 1 hr (by decide)
    norm_num at h
    rw [TargetMargin.capacity_step]
    linarith

-- Coefficients are rational subtraction, even in the formal domain e<r.
example : TargetMargin.target 0 0 4 1 = -(6 : ℚ) ∧
    TargetMargin.lower 0 4 1 = -(6 : ℚ) := by
  norm_num [TargetMargin.target, TargetMargin.lower]

-- A valid rank-three Data profile for which general scalarization fails.
-- The unified theorem must retain the separate low-rank branch.
private def largeTail : Layers where
  head := 0
  tail j := if j = 0 then 205 else 0
  support := {0}
  tail_vanish j hj := by simpa using hj
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num

private def rankThreeData : Data 3 200 6 where
  layers := largeTail
  rank_lo := by decide
  embed := by decide
  budget := by norm_num [Layers.mass, largeTail, volume]
  head_linear := by norm_num [largeTail]
  triangular_bound _ := by norm_num [triangular]
  head_cap _ := by norm_num [largeTail, triangular]
  tail_cap j := by dsimp [largeTail]; split_ifs <;> norm_num

example : factor 3 2 * rankThreeData.layers.row 3 1 6 <
    rankThreeData.layers.row 3 2 6 := by
  norm_num [factor, Layers.row, weight, rankThreeData, largeTail]

example : ∀ k, 1 ≤ k ∧ k ≤ 3 →
    TargetMargin.lower 200 3 k + rankThreeData.layers.row 3 k 6 ≤
      TargetMargin.target 200 6 3 k :=
  rankThreeData.all_rows (by intro h; omega)

-- All_rows itself can have equality at positive deficit in rank two.
private def boundaryHead : Layers where
  head := 6
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := by norm_num
  tail_nonneg _ := by norm_num

private def rankTwoData : Data 2 3 3 where
  layers := boundaryHead
  rank_lo := by decide
  embed := by decide
  budget := by norm_num [Layers.mass, boundaryHead, volume]
  head_linear := by norm_num [boundaryHead]
  triangular_bound h := by omega
  head_cap h := by omega
  tail_cap _ := by norm_num [boundaryHead]

example : TargetMargin.lower 3 2 1 + rankTwoData.layers.row 2 1 3 =
    TargetMargin.target 3 3 2 1 := by
  norm_num [TargetMargin.lower, TargetMargin.target, Layers.row, weight,
    rankTwoData, boundaryHead, Nat.choose]

example : ∀ k, 1 ≤ k ∧ k ≤ 2 →
    TargetMargin.lower 3 2 k + rankTwoData.layers.row 2 k 3 ≤
      TargetMargin.target 3 3 2 k := rankTwoData.all_rows (by intro h; omega)

-- All resource fields can hold at the excluded rank-six corner. Without Boundary,
-- the first target comparison actually fails for this numerical relaxation.
private def cornerLayers : Layers where
  head := 6
  tail j := if j < 11 then 27 else if j = 11 then 12 else 0
  support := Finset.range 12
  tail_vanish j hj := by
    have h12 : 12 ≤ j := by simpa using hj
    simp [show ¬j < 11 by omega, show j ≠ 11 by omega]
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num

private def cornerData : Data 6 7 21 where
  layers := cornerLayers
  rank_lo := by decide
  embed := by decide
  budget := by norm_num [Layers.mass, cornerLayers, volume, Finset.sum_range_succ]
  head_linear := by norm_num [cornerLayers]
  triangular_bound _ := by norm_num [triangular]
  head_cap _ := by norm_num [cornerLayers, triangular]
  tail_cap j := by dsimp [cornerLayers]; split_ifs <;> norm_num

example : TargetMargin.target 7 21 6 1 <
    TargetMargin.lower 7 6 1 + cornerData.layers.row 6 1 21 ∧
    TargetMargin.lower 7 6 1 + cornerData.layers.row 6 1 21 -
      TargetMargin.target 7 21 6 1 = (831 : ℚ) / 8008 := by
  norm_num [TargetMargin.target, TargetMargin.lower, Layers.row, weight,
    cornerData, cornerLayers, Finset.sum_range_succ, Nat.choose]

example : ¬ Boundary 6 7 21 := by
  intro hb
  obtain ⟨B, hB, hcard⟩ := hb (by decide) (by decide) rfl
  have h := NSP14.sidon_card_bound 28 B hB
  rw [hcard] at h
  norm_num at h

#print axioms first_margin_exact

end NSP14.Block07Audit
