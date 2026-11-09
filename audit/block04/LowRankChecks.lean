module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LowRank

namespace NSP14.Block04Audit

-- An independent expansion gives a quantitative lower bound on the margin,
-- including rational points between integer deficits.
theorem margin_expansion (e d : ℚ) :
    d * (volume e d - 1) - 4 * (e + d - 7) =
      15 + 2 * (e - 4) + 7 / 2 * (d - 6) +
        (d - 6) * (e - 4) + (d - 6)^2 / 2 := by
  unfold volume
  ring

theorem margin_ge_fifteen (e d : ℚ) (he : 4 ≤ e) (hd : 6 ≤ d) :
    15 ≤ d * (volume e d - 1) - 4 * (e + d - 7) := by
  have hprod := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr he)
  unfold volume
  nlinarith [sq_nonneg (d - 6)]

private def headOnly (h : ℚ) (hh : 0 ≤ h) : Layers where
  head := h
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := hh
  tail_nonneg _ := by norm_num

-- A valid rank-two numerical profile saturates both final rows at V=3.
-- This profile must not be excluded by importing Resources 2's triangular cap.
example :
    (headOnly 6 (by norm_num)).mass 3 = 3 * volume 3 3 ∧
    (headOnly 6 (by norm_num)).head = 2 * 3 ∧
    (headOnly 6 (by norm_num)).row 2 1 3 = 3 * (volume 3 3 + 1) ∧
    (headOnly 6 (by norm_num)).row 2 2 3 = 3 * (volume 3 3 - 1) := by
  norm_num [headOnly, Layers.mass, Layers.row, weight, volume]

example : ¬∃ R : Resources 2 3 3, R.head = 6 := by
  rintro ⟨R, h⟩
  have hc := R.head_cap
  norm_num [triangular, h] at hc

-- Dropping H1<=2d breaks the first rank-two row even with a valid mass budget.
example :
    (headOnly 3 (by norm_num)).mass 1 ≤ 1 * volume 5 1 ∧
    ¬ (headOnly 3 (by norm_num)).head ≤ 2 * 1 ∧
    1 * (volume 5 1 + 1) < (headOnly 3 (by norm_num)).row 2 1 1 := by
  norm_num [headOnly, Layers.mass, Layers.row, weight, volume]

-- Dropping the triangular head cap breaks rank three while H1<=3d and the
-- mass budget both hold; the cap must remain part of the future actual bridge.
example :
    (headOnly 18 (by norm_num)).mass 6 ≤ 6 * volume 4 6 ∧
    (headOnly 18 (by norm_num)).head ≤ 3 * 6 ∧
    ¬ (headOnly 18 (by norm_num)).head ≤ 4 + 6 - 7 ∧
    6 * (volume 4 6 + 1) < (headOnly 18 (by norm_num)).row 3 1 6 := by
  norm_num [headOnly, Layers.mass, Layers.row, weight, volume]

#print axioms margin_expansion
#print axioms margin_ge_fifteen

end NSP14.Block04Audit
