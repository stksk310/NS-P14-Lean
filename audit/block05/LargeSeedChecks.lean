module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LargeSeed

namespace NSP14.Block05Audit

-- Exact rounding, not just two inequalities; valid for every natural rank.
theorem cutoff_exact (r : ℕ) :
    2 * largeCutoff r = triangularNat r + 2 - triangularNat r % 2 := by
  have hm := Nat.mod_lt (triangularNat r) (by decide : 0 < 2)
  have he := Nat.mod_add_div (triangularNat r) 2
  unfold largeCutoff
  omega

-- The replacement barrier step cannot simply be started at r=9.
example : barrier 10 - barrier 9 - (9 + 2) / (triangular 9 + 3) =
    -(7 : ℚ) / 240 := by norm_num [barrier, triangular]

-- The threshold/barrier chain also fails at r=9, despite the positive actual seed.
example : thresholdLower 9 - barrier 9 = -(1 : ℚ) / 72 := by
  norm_num [thresholdLower, barrier, triangular]

-- The coarse increment estimate does not supply the original intermediate 2/r
-- bound; it must be compared directly with the barrier as recorded in A05.
example : (10 + 2) / (triangular 10 + 3) - (2 : ℚ) / 10 = 1 / 145 := by
  norm_num [triangular]

#print axioms cutoff_exact

end NSP14.Block05Audit
