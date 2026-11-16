module

import NSP14

open scoped BigOperators
open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LowRank

-- No triangular lower bound on d or triangular head cap in rank two.
example (P : Layers) (e d : ℚ) (hd : 0 ≤ d)
    (hb : P.mass d ≤ d * volume e d) (hh : P.head ≤ 2 * d) :
    P.row 2 1 d ≤ d * (volume e d + 1) ∧
    P.row 2 2 d ≤ d * (volume e d - 1) :=
  P.rank_two_bounds e d hd hb hh

example (P : Layers) (e d : ℚ) (he : 4 ≤ e) (hd : 6 ≤ d)
    (hb : P.mass d ≤ d * volume e d) (hh : P.head ≤ 3 * d)
    (hc : P.head ≤ e + d - 7) :
    P.row 3 1 d ≤ d * (volume e d + 1) ∧
    P.row 3 2 d ≤ 2 * d * (volume e d + 1) ∧
    P.row 3 3 d ≤ d * (volume e d - 1) :=
  P.rank_three_bounds e d he hd hb hh hc

def emptyLayers : Layers where
  head := 0
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := by norm_num
  tail_nonneg _ := by norm_num

-- Empty tower: all e, including d=0, with no triangular or head-cap premise.
example (e : ℚ) : emptyLayers.row 2 1 0 ≤ 0 ∧ emptyLayers.row 2 2 0 ≤ 0 := by
  simpa using emptyLayers.rank_two_bounds e 0 (by norm_num)
    (by norm_num [Layers.mass, emptyLayers]) (by norm_num [emptyLayers])

-- The numerical relaxation is sharp at V=3; this is not an actual semigroup claim.
def boundaryTwo : Layers where
  head := 6
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := by norm_num
  tail_nonneg _ := by norm_num

example : volume 3 3 = 3 := by norm_num [volume]
example : boundaryTwo.row 2 1 3 = 3 * (volume 3 3 + 1) := by
  norm_num [Layers.row, weight, boundaryTwo, volume]
example : boundaryTwo.row 2 1 3 ≤ 12 := by
  have h := boundaryTwo.rank_two_bounds 3 3 (by norm_num)
    (by norm_num [Layers.mass, boundaryTwo, volume]) (by norm_num [boundaryTwo])
  norm_num [volume] at h
  exact h.1

-- A nonzero layer at an arbitrary tail index, including far beyond every small cutoff.
def distantTail (k : ℕ) : Layers where
  head := 0
  tail j := if j = k then 1 else 0
  support := {k}
  tail_vanish j hj := by simpa using hj
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num

example (k : ℕ) :
    (distantTail k).row 2 1 1 ≤ 3 ∧ (distantTail k).row 2 2 1 ≤ 1 := by
  have h := (distantTail k).rank_two_bounds 3 1 (by norm_num)
    (by norm_num [Layers.mass, distantTail, volume]) (by norm_num [distantTail])
  norm_num [volume] at h
  exact h

example (k : ℕ) :
    (distantTail k).row 3 1 6 ≤ 39 ∧ (distantTail k).row 3 2 6 ≤ 78 ∧
    (distantTail k).row 3 3 6 ≤ 27 := by
  have h := (distantTail k).rank_three_bounds 4 6 (by norm_num) (by norm_num)
    (by norm_num [Layers.mass, distantTail, volume])
    (by norm_num [distantTail]) (by norm_num [distantTail])
  norm_num [volume] at h
  exact h

example : weight 3 2 0 = 1 ∧ weight 3 2 1 = 8 / 3 ∧ weight 3 2 2 = 3 / 2 := by
  norm_num [weight]
example : weight 3 3 0 = 0 ∧ weight 3 3 1 = 1 ∧ weight 3 3 2 = 2 / 3 := by
  norm_num [weight]
example : 6 * (volume 4 6 - 1) - 4 * (4 + 6 - 7) = 15 := by norm_num [volume]

-- The adapter keeps exactly the same first row and the same resource profile.
example (r : ℕ) (e d : ℚ) (R : Resources r e d) :
    R.toLayers.row r 1 d = R.scalar := R.row_one_eq_scalar

example (e d : ℚ) (R : Resources 3 e d) (he : 4 ≤ e) (hd : 6 ≤ d)
    (hh : R.head ≤ 3 * d) :
    R.toLayers.row 3 1 d ≤ d * (volume e d + 1) ∧
    R.toLayers.row 3 2 d ≤ 2 * d * (volume e d + 1) ∧
    R.toLayers.row 3 3 d ≤ d * (volume e d - 1) := R.rank_three_bounds he hd hh

#print axioms Layers.tail_sum_nonneg
#print axioms Layers.row_le
#print axioms Layers.rank_two_first_le_mass
#print axioms Layers.rank_two_first_le_linear
#print axioms Layers.rank_two_top_le
#print axioms Layers.rank_two_bounds
#print axioms Layers.rank_three_first_le
#print axioms Layers.rank_three_second_le
#print axioms Layers.rank_three_top_le
#print axioms rank_three_margin_pos
#print axioms Layers.rank_three_bounds
#print axioms Resources.row_one_eq_scalar
#print axioms Resources.rank_three_bounds
