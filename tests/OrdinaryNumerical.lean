module

import NSP14

open NSP14.Ordinary.SmallScalar NSP14.Ordinary.LowRank
open NSP14.Ordinary.Scalarization
open NSP14 NSP14.Ordinary NSP14.Ordinary.NumericalClosure

example (P : Layers) (r k : ℕ) (d : ℚ) (hr : 4 ≤ r)
    (hk : 1 ≤ k ∧ k ≤ r) (hd : 0 ≤ d) :
    P.row r k d ≤ (Nat.choose (r - 1) (k - 1) : ℚ) * P.row r 1 d :=
  row_le_scalar P r k d hr hk hd

example (e d r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (d : ℚ) * (volume e d + 1) * factor r k ≤
      NSP14.Ordinary.TargetMargin.target e d r k -
        NSP14.Ordinary.TargetMargin.lower e r k :=
  NSP14.Ordinary.TargetMargin.target_margin e d r k hr hk

example (r e d : ℕ) (D : Data r e d) (hb : Boundary r e d) :
    ∀ k, 1 ≤ k ∧ k ≤ r →
      TargetMargin.lower e r k + D.layers.row r k d ≤ TargetMargin.target e d r k :=
  D.all_rows hb

example (S : AddSubmonoid ℕ) (r e d : ℕ) (D : Data r e d)
    (hb : 6 ≤ r → r ≤ 8 → e = r + 1 → Nonempty (AperyPairData S (e + d) e)) :
    ∀ k, 1 ≤ k ∧ k ≤ r →
      TargetMargin.lower e r k + D.layers.row r k d ≤ TargetMargin.target e d r k :=
  D.all_rows_of_apery_pairs S hb

-- Sharp k=2 tail at r=4; all top rows remain in the public theorem.
example : weight 4 2 2 = factor 4 2 * weight 4 1 2 := by norm_num [weight, factor]
example : weight 4 4 0 = 0 ∧ weight 4 4 1 = 1 ∧ weight 4 4 2 = 3 / 4 := by
  norm_num [weight]
example (r : ℕ) (hr : 4 ≤ r) (P : Layers) (d : ℚ) (hd : 0 ≤ d) :
    P.row r r d ≤ P.row r 1 d := by
  simpa [factor] using row_le_scalar P r r d hr ⟨by omega, le_rfl⟩ hd

def zeroLayers : Layers where
  head := 0
  tail _ := 0
  support := ∅
  tail_vanish _ _ := rfl
  head_nonneg := by norm_num
  tail_nonneg _ := by norm_num

def zeroTwo : Data 2 3 0 where
  layers := zeroLayers
  rank_lo := by decide
  embed := by decide
  budget := by norm_num [Layers.mass, zeroLayers]
  head_linear := by norm_num [zeroLayers]
  triangular_bound := by intro h; omega
  head_cap := by intro h; omega
  tail_cap _ := by norm_num [zeroLayers]

example : ∀ k, 1 ≤ k ∧ k ≤ 2 →
    TargetMargin.lower 3 2 k + zeroTwo.layers.row 2 k 0 ≤ TargetMargin.target 3 0 2 k :=
  zeroTwo.all_rows (by intro h; omega)

def singleLayer (j : ℕ) : Layers where
  head := 0
  tail t := if t = j then 1 else 0
  support := {j}
  tail_vanish t ht := by simpa using ht
  head_nonneg := by norm_num
  tail_nonneg t := by split_ifs <;> norm_num

private theorem tri_ge_six (r : ℕ) (hr : 3 ≤ r) : (6 : ℚ) ≤ triangular r := by
  have hrq : (3 : ℚ) ≤ r := by exact_mod_cast hr
  have h := mul_nonneg (by linarith : 0 ≤ (r : ℚ) - 3) (by positivity : 0 ≤ (r : ℚ) + 4)
  unfold triangular
  nlinarith

-- A nonempty family for every rank >=3, using an arbitrary distant layer.
def interiorData (r : ℕ) (hr : 3 ≤ r) (j : ℕ) :
    Data r (r + 2) (LargeSeed.triangularNat r) where
  layers := singleLayer j
  rank_lo := by omega
  embed := by omega
  budget := by
    have ha := tri_ge_six r hr
    have hrq : (3 : ℚ) ≤ r := by exact_mod_cast hr
    norm_num [Layers.mass, singleLayer]
    rw [LargeSeed.triangularNat_cast]
    have hV : 2 ≤ volume ((r : ℚ) + 2) (triangular r) := by
      unfold volume
      linarith
    have hp := mul_nonneg (by linarith : 0 ≤ triangular r) (sub_nonneg.mpr hV)
    nlinarith
  head_linear := by change 0 ≤ (r : ℚ) * (LargeSeed.triangularNat r : ℚ); positivity
  triangular_bound _ := by rw [LargeSeed.triangularNat_cast]
  head_cap _ := by
    change 0 ≤ ((r + 2 : ℕ) : ℚ) + (LargeSeed.triangularNat r : ℚ) - 1 - triangular r
    rw [LargeSeed.triangularNat_cast]
    push_cast
    have hrq : (3 : ℚ) ≤ r := by exact_mod_cast hr
    linarith
  tail_cap t := by
    have ha := tri_ge_six r hr
    change (if t = j then 1 else 0) ≤ ((r + 2 : ℕ) : ℚ) + (LargeSeed.triangularNat r : ℚ) - 1
    rw [LargeSeed.triangularNat_cast]
    push_cast
    split_ifs <;> linarith

example (r : ℕ) (hr : 3 ≤ r) (j : ℕ) :
    ∀ k, 1 ≤ k ∧ k ≤ r →
      TargetMargin.lower (r + 2) r k +
        (interiorData r hr j).layers.row r k (LargeSeed.triangularNat r) ≤
        TargetMargin.target (r + 2) (LargeSeed.triangularNat r) r k :=
  (interiorData r hr j).all_rows (by intro _ _ he; omega)

-- The small first corner and large r=9 are both admissible numerical families.
example : ∀ k, 1 ≤ k ∧ k ≤ 4 →
    TargetMargin.lower 6 4 k + (interiorData 4 (by decide) 100).layers.row 4 k 10 ≤
      TargetMargin.target 6 10 4 k := by
  simpa [LargeSeed.triangularNat] using
    (interiorData 4 (by decide) 100).all_rows (by intro _ _ h; omega)

example (r : ℕ) (hr : 4 ≤ r) (e d : ℕ) (D : Data r e d)
    (hb : Boundary r e d) : D.layers.row r 1 d < (d : ℚ) * (volume e d + 1) :=
  D.scalar_lt hr hb

private def powerValue (i : Fin 7) : ℕ := if i.val = 0 then 0 else 3 ^ (i.val - 1)

private theorem top_min (m x : ℕ) (hx : x < m) : IsAperyMin (⊤ : AddSubmonoid ℕ) m x := by
  constructor
  · simp
  · intro y _ h
    rw [Nat.mod_eq_of_lt hx] at h
    have hy := Nat.mod_le y m
    omega

-- A nonvacuous boundary witness: 0,1,3,9,27,81,243, modulus 1000.
def boundaryPairs : AperyPairData (⊤ : AddSubmonoid ℕ) 1000 7 where
  value := powerValue
  injective_value := by decide
  value_min i := top_min 1000 (powerValue i) (by
    have h : ∀ i, powerValue i < 1000 := by decide
    exact h i)
  pair_min i j := top_min 1000 (powerValue i + powerValue j)
    (by
      have h : ∀ i j, powerValue i + powerValue j < 1000 := by decide
      exact h i j)
  pair_unique := by decide

def boundaryData (j : ℕ) : Data 6 7 993 where
  layers := singleLayer j
  rank_lo := by decide
  embed := by decide
  budget := by norm_num [Layers.mass, singleLayer, volume]
  head_linear := by norm_num [singleLayer]
  triangular_bound _ := by norm_num [triangular]
  head_cap _ := by norm_num [singleLayer, triangular]
  tail_cap t := by dsimp [singleLayer]; split_ifs <;> norm_num

example (j : ℕ) : ∀ k, 1 ≤ k ∧ k ≤ 6 →
    TargetMargin.lower 7 6 k + (boundaryData j).layers.row 6 k 993 ≤
      TargetMargin.target 7 993 6 k := by
  apply (boundaryData j).all_rows_of_apery_pairs (⊤ : AddSubmonoid ℕ)
  intro _ _ _
  exact ⟨boundaryPairs⟩

example (r : ℕ) (hr : 6 ≤ r ∧ r ≤ 8) :
    ¬Boundary r (r + 1) (LargeSeed.triangularNat r) := by
  intro hb
  obtain ⟨B, hB, hc⟩ := hb hr.1 hr.2 rfl
  have : NeZero (r + 1 + LargeSeed.triangularNat r) := ⟨by omega⟩
  have h := sidon_card_bound (r + 1 + LargeSeed.triangularNat r) B hB
  rw [hc] at h
  obtain ⟨hlo, hhi⟩ := hr
  interval_cases r <;> norm_num [LargeSeed.triangularNat] at h

example (r e d : ℕ) (D : Data r e d) (c : ℕ → ℚ) (hb : Boundary r e d)
    (hc : ∀ k, 1 ≤ k ∧ k ≤ r → c k ≤ TargetMargin.lower e r k + D.layers.row r k d) :
    ∀ k, 1 ≤ k ∧ k ≤ r → c k ≤ TargetMargin.target e d r k := D.relative_rows c hb hc

#print axioms choose_balance
#print axioms binomial_balance
#print axioms factor_nonneg
#print axioms factor_pos
#print axioms head_weight_eq
#print axioms tail_weight_eq
#print axioms second_tail_identity
#print axioms normalized_tail_le
#print axioms weight_zero_le
#print axioms weight_head_le
#print axioms weight_tail_le
#print axioms row_le_scalar
#print axioms TargetMargin.choose_succ_cast
#print axioms TargetMargin.target_zero
#print axioms TargetMargin.target_step
#print axioms TargetMargin.capacity_step
#print axioms TargetMargin.target_margin
#print axioms Data.deficit_nat_lower
#print axioms Data.parameterization
#print axioms Data.small_corner
#print axioms Data.scalar_lt
#print axioms Data.row_capacity
#print axioms Data.all_rows
#print axioms Data.all_rows_of_apery_pairs
#print axioms Data.relative_rows
