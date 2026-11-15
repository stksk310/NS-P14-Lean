module
public import NSP14.Width.DenseComparison
public import tests.WidthDenseResources
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
namespace NSP14.Tests.WidthDense
open NSP14.Homological
theorem q4_t2_Q_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ℚ) DenseResources.q4_t2.Variables (DenseResources.q4_t2.fullG (ℚ)) i≤ i*DenseResources.q4_t2.u.choose (i+1) :=
  DenseResources.q4_t2.actual_dense_firstterm (ℚ) 2 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t2_char2_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 2) DenseResources.q4_t2.Variables (DenseResources.q4_t2.fullG (ZMod 2)) i≤ i*DenseResources.q4_t2.u.choose (i+1) :=
  DenseResources.q4_t2.actual_dense_firstterm (ZMod 2) 2 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t2_char3_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 3) DenseResources.q4_t2.Variables (DenseResources.q4_t2.fullG (ZMod 3)) i≤ i*DenseResources.q4_t2.u.choose (i+1) :=
  DenseResources.q4_t2.actual_dense_firstterm (ZMod 3) 2 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t3_Q_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ℚ) DenseResources.q4_t3.Variables (DenseResources.q4_t3.fullG (ℚ)) i≤ i*DenseResources.q4_t3.u.choose (i+1) :=
  DenseResources.q4_t3.actual_dense_firstterm (ℚ) 3 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t3_char2_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 2) DenseResources.q4_t3.Variables (DenseResources.q4_t3.fullG (ZMod 2)) i≤ i*DenseResources.q4_t3.u.choose (i+1) :=
  DenseResources.q4_t3.actual_dense_firstterm (ZMod 2) 3 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t3_char3_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 3) DenseResources.q4_t3.Variables (DenseResources.q4_t3.fullG (ZMod 3)) i≤ i*DenseResources.q4_t3.u.choose (i+1) :=
  DenseResources.q4_t3.actual_dense_firstterm (ZMod 3) 3 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t4_Q_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ℚ) DenseResources.q4_t4.Variables (DenseResources.q4_t4.fullG (ℚ)) i≤ i*DenseResources.q4_t4.u.choose (i+1) :=
  DenseResources.q4_t4.actual_dense_firstterm (ℚ) 4 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t4_char2_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 2) DenseResources.q4_t4.Variables (DenseResources.q4_t4.fullG (ZMod 2)) i≤ i*DenseResources.q4_t4.u.choose (i+1) :=
  DenseResources.q4_t4.actual_dense_firstterm (ZMod 2) 4 (by decide) (by decide) (by decide) (by decide) i hi
theorem q4_t4_char3_all_positive (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 3) DenseResources.q4_t4.Variables (DenseResources.q4_t4.fullG (ZMod 3)) i≤ i*DenseResources.q4_t4.u.choose (i+1) :=
  DenseResources.q4_t4.actual_dense_firstterm (ZMod 3) 4 (by decide) (by decide) (by decide) (by decide) i hi
end NSP14.Tests.WidthDense
