module
public import NSP14.Width.HigherFromSecond
public import NSP14.Width.FiveHigher
public import NSP14.Width.SparseHigher
@[expose] public section
namespace NSP14.Tests.V06HigherFromSecond
open NSP14.Width

/-- Minimal embedding dimension: the only higher row is also the top row. -/
theorem capacity_two (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ 2) :
    (2:ℚ)*((2:ℕ).choose i:ℚ) ≤ (i:ℚ)*((2:ℕ).choose (i+1):ℚ)+
      2*((1:ℕ).choose (i-1):ℚ)+((1:ℕ).choose (i+1):ℚ) := by
  exact higher_capacity_from_second 2 2 2 (by decide) (by decide)
    (by norm_num [Nat.choose]) i hi hie

/-- The exact u=8 envelope pays every row through five. -/
theorem capacity_five_eight (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ 5) :
    (14:ℚ)*((5:ℕ).choose i:ℚ) ≤ (i:ℚ)*((8:ℕ).choose (i+1):ℚ)+
      8*((4:ℕ).choose (i-1):ℚ)+((4:ℕ).choose (i+1):ℚ) := by
  exact higher_capacity_from_second 5 8 14 (by decide) (by decide)
    (by norm_num [Nat.choose]) i hi hie

/-- The fractional quadratic envelope is allowed, including the top row. -/
theorem capacity_five_nine (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ 5) :
    (81/4:ℚ)*((5:ℕ).choose i:ℚ) ≤ (i:ℚ)*((9:ℕ).choose (i+1):ℚ)+
      9*((4:ℕ).choose (i-1):ℚ)+((4:ℕ).choose (i+1):ℚ) := by
  exact higher_capacity_from_second 5 9 (81/4) (by decide) (by decide)
    (by norm_num [Nat.choose]) i hi hie

example : (2:ℚ)*((2:ℕ).choose 2:ℚ) ≤ (2:ℚ)*((2:ℕ).choose 3:ℚ)+
    2*((1:ℕ).choose 1:ℚ)+((1:ℕ).choose 3:ℚ) :=
  capacity_two 2 (by decide) (by decide)
example : (14:ℚ)*((5:ℕ).choose 5:ℚ) ≤ (5:ℚ)*((8:ℕ).choose 6:ℚ)+
    8*((4:ℕ).choose 4:ℚ)+((4:ℕ).choose 6:ℚ) :=
  capacity_five_eight 5 (by decide) (by decide)
example : (81/4:ℚ)*((5:ℕ).choose 5:ℚ) ≤ (5:ℚ)*((9:ℕ).choose 6:ℚ)+
    9*((4:ℕ).choose 4:ℚ)+((4:ℕ).choose 6:ℚ) :=
  capacity_five_nine 5 (by decide) (by decide)
end NSP14.Tests.V06HigherFromSecond
