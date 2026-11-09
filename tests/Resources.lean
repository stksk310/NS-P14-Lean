module

import NSP14

open scoped BigOperators
open NSP14 NSP14.Ordinary.SmallScalar

-- These interfaces must derive the upper bound from one resource profile.
example (r n : ℕ) (e d : ℚ) (R : Resources r e d)
    (hr : 4 ≤ r) (hn : r ≤ n) : R.scalar ≤ upper r n e d :=
  R.scalar_le_upper n hr hn

example (r s t : ℕ)
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hr : 4 ≤ r ∧ r ≤ 8) (hcorner : r ≤ 5 ∨ s + t ≠ 0) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) :=
  R.scalar_lt r s t hr hcorner

-- A nonzero resource arbitrarily far beyond the cutoff is allowed.
example (k : ℕ) :
    ∑ j ∈ ({k} : Finset ℕ),
      (((4 : ℚ) - 1) / ((j : ℚ) + 3) - alpha 4 7) * 1
      ≤ 1 * tailWeight 4 7 := by
  exact residual_tail_le 4 7 {k} (fun _ => 1) 1
    (by decide) (by decide) (fun _ => by norm_num) (fun _ => by norm_num)

-- H₁=0 and one tail layer of size 1, with no restriction on its location.
def singleTail (k : ℕ) : Resources 4 ((4 : ℚ) + 1 + 0) (triangular 4 + 0) where
  head := 0
  tail j := if j = k then 1 else 0
  support := {k}
  tail_vanish j hj := by simpa using hj
  head_nonneg := by norm_num
  tail_nonneg j := by split_ifs <;> norm_num
  budget := by norm_num [volume, triangular]
  head_cap := by norm_num [triangular]
  tail_cap j := by split_ifs <;> norm_num [triangular]

example (k : ℕ) : (singleTail k).scalar ≤ upper 4 7 5 10 := by
  have h := (singleTail k).scalar_le_upper 7 (by decide) (by decide)
  norm_num [triangular] at h
  exact h

example (k : ℕ) : (singleTail k).scalar < 95 := by
  have h := (singleTail k).scalar_lt 4 0 0 (by decide) (Or.inl (by decide))
  norm_num [triangular, volume] at h
  exact h

-- Empty tail and head: no accidental positivity or nonemptiness premise.
def emptyResources : Resources 4 5 10 where
  head := 0
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := by norm_num
  tail_nonneg _ := by norm_num
  budget := by norm_num [volume]
  head_cap := by norm_num [triangular]
  tail_cap _ := by norm_num

example : emptyResources.scalar = 30 := by norm_num [Resources.scalar, emptyResources]

-- Shifted index j denotes the paper layer j+2. At layer n the residual is zero.
example : ((4 : ℚ) - 1) / (5 + 3) - alpha 4 7 = 0 := by norm_num [alpha]
example : 0 < ((4 : ℚ) - 1) / (4 + 3) - alpha 4 7 := by norm_num [alpha]
example : ((4 : ℚ) - 1) / (6 + 3) - alpha 4 7 < 0 := by norm_num [alpha]

-- Both bridges require resources, not an assumed SO3 inequality.
example (m r s t : ℕ) [NeZero m]
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hb : 6 ≤ r → s = 0 → ∃ B : Finset (ZMod m), IsSidon B ∧ B.card = r + 1) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) :=
  R.scalar_lt_of_boundary_sidon m r s t hm hr hb

example (S : AddSubmonoid ℕ) (m r s t : ℕ) [NeZero m]
    (R : Resources r ((r : ℚ) + 1 + s) (triangular r + t))
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hb : 6 ≤ r → s = 0 → Nonempty (AperyPairData S m (r + 1))) :
    R.scalar < (triangular r + t) *
      (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) :=
  R.scalar_lt_of_apery_pairs S m r s t hm hr hb

-- Interior points still require no boundary witness.
example (R : Resources 6 ((6 : ℚ) + 1 + 1) (triangular 6 + 0)) : R.scalar < 378 := by
  have h := R.scalar_lt_of_boundary_sidon 29 6 1 0 (by decide) (by decide)
    (by intro _ hs; omega)
  norm_num [triangular, volume] at h
  exact h

#print axioms residual_weight_nonneg
#print axioms residual_weight_nonpos
#print axioms residual_tail_le
#print axioms Resources.scalar_le_upper
#print axioms Resources.scalar_lt
#print axioms Resources.scalar_lt_of_boundary_sidon
#print axioms Resources.scalar_lt_of_apery_pairs
