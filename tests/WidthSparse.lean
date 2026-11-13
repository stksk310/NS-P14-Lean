module
public import NSP14.Width.SparseComparison
public import tests.WidthSparseData
public import tests.WidthSparseCache
public import NSP14.Endpoint.FiniteSocleWindow
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open NSP14 NSP14.Homological
namespace Run18SparseAcceptance


theorem six_rational_first : totalBetti (ℚ) six.Variables (six.fullG (ℚ)) 1≤(10:ℕ).choose 2+1 :=
  six.actual_first_sparse (ℚ) (by decide) (by decide)
theorem six_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ℚ) six.Variables (six.fullG (ℚ)) i≤ i*(10:ℕ).choose (i+1) :=
  six.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem six_charTwo_first : totalBetti (ZMod 2) six.Variables (six.fullG (ZMod 2)) 1≤(10:ℕ).choose 2+1 :=
  six.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem six_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ZMod 2) six.Variables (six.fullG (ZMod 2)) i≤ i*(10:ℕ).choose (i+1) :=
  six.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem six_charThree_first : totalBetti (ZMod 3) six.Variables (six.fullG (ZMod 3)) 1≤(10:ℕ).choose 2+1 :=
  six.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem six_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ZMod 3) six.Variables (six.fullG (ZMod 3)) i≤ i*(10:ℕ).choose (i+1) :=
  six.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie


theorem seven_rational_first : totalBetti (ℚ) seven.Variables (seven.fullG (ℚ)) 1≤(12:ℕ).choose 2+1 :=
  seven.actual_first_sparse (ℚ) (by decide) (by decide)
theorem seven_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤7) :
    totalBetti (ℚ) seven.Variables (seven.fullG (ℚ)) i≤ i*(12:ℕ).choose (i+1) :=
  seven.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem seven_charTwo_first : totalBetti (ZMod 2) seven.Variables (seven.fullG (ZMod 2)) 1≤(12:ℕ).choose 2+1 :=
  seven.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem seven_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤7) :
    totalBetti (ZMod 2) seven.Variables (seven.fullG (ZMod 2)) i≤ i*(12:ℕ).choose (i+1) :=
  seven.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem seven_charThree_first : totalBetti (ZMod 3) seven.Variables (seven.fullG (ZMod 3)) 1≤(12:ℕ).choose 2+1 :=
  seven.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem seven_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤7) :
    totalBetti (ZMod 3) seven.Variables (seven.fullG (ZMod 3)) i≤ i*(12:ℕ).choose (i+1) :=
  seven.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie


theorem eight_rational_first : totalBetti (ℚ) eight.Variables (eight.fullG (ℚ)) 1≤(14:ℕ).choose 2+1 :=
  eight.actual_first_sparse (ℚ) (by decide) (by decide)
theorem eight_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤8) :
    totalBetti (ℚ) eight.Variables (eight.fullG (ℚ)) i≤ i*(14:ℕ).choose (i+1) :=
  eight.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem eight_charTwo_first : totalBetti (ZMod 2) eight.Variables (eight.fullG (ZMod 2)) 1≤(14:ℕ).choose 2+1 :=
  eight.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem eight_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤8) :
    totalBetti (ZMod 2) eight.Variables (eight.fullG (ZMod 2)) i≤ i*(14:ℕ).choose (i+1) :=
  eight.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem eight_charThree_first : totalBetti (ZMod 3) eight.Variables (eight.fullG (ZMod 3)) 1≤(14:ℕ).choose 2+1 :=
  eight.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem eight_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤8) :
    totalBetti (ZMod 3) eight.Variables (eight.fullG (ZMod 3)) i≤ i*(14:ℕ).choose (i+1) :=
  eight.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie


theorem nine_rational_first : totalBetti (ℚ) nine.Variables (nine.fullG (ℚ)) 1≤(16:ℕ).choose 2+1 :=
  nine.actual_first_sparse (ℚ) (by decide) (by decide)
theorem nine_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤9) :
    totalBetti (ℚ) nine.Variables (nine.fullG (ℚ)) i≤ i*(16:ℕ).choose (i+1) :=
  nine.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem nine_charTwo_first : totalBetti (ZMod 2) nine.Variables (nine.fullG (ZMod 2)) 1≤(16:ℕ).choose 2+1 :=
  nine.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem nine_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤9) :
    totalBetti (ZMod 2) nine.Variables (nine.fullG (ZMod 2)) i≤ i*(16:ℕ).choose (i+1) :=
  nine.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem nine_charThree_first : totalBetti (ZMod 3) nine.Variables (nine.fullG (ZMod 3)) 1≤(16:ℕ).choose 2+1 :=
  nine.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem nine_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤9) :
    totalBetti (ZMod 3) nine.Variables (nine.fullG (ZMod 3)) i≤ i*(16:ℕ).choose (i+1) :=
  nine.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie


theorem ten_rational_first : totalBetti (ℚ) ten.Variables (ten.fullG (ℚ)) 1≤(18:ℕ).choose 2+1 :=
  ten.actual_first_sparse (ℚ) (by decide) (by decide)
theorem ten_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤10) :
    totalBetti (ℚ) ten.Variables (ten.fullG (ℚ)) i≤ i*(18:ℕ).choose (i+1) :=
  ten.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem ten_charTwo_first : totalBetti (ZMod 2) ten.Variables (ten.fullG (ZMod 2)) 1≤(18:ℕ).choose 2+1 :=
  ten.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem ten_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤10) :
    totalBetti (ZMod 2) ten.Variables (ten.fullG (ZMod 2)) i≤ i*(18:ℕ).choose (i+1) :=
  ten.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem ten_charThree_first : totalBetti (ZMod 3) ten.Variables (ten.fullG (ZMod 3)) 1≤(18:ℕ).choose 2+1 :=
  ten.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem ten_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤10) :
    totalBetti (ZMod 3) ten.Variables (ten.fullG (ZMod 3)) i≤ i*(18:ℕ).choose (i+1) :=
  ten.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie


theorem dilated_rational_first : totalBetti (ℚ) dilated.Variables (dilated.fullG (ℚ)) 1≤(10:ℕ).choose 2+1 :=
  dilated.actual_first_sparse (ℚ) (by decide) (by decide)
theorem dilated_rational_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ℚ) dilated.Variables (dilated.fullG (ℚ)) i≤ i*(10:ℕ).choose (i+1) :=
  dilated.actual_sparse_higher (ℚ) (by decide) (by decide) i hi hie
theorem dilated_charTwo_first : totalBetti (ZMod 2) dilated.Variables (dilated.fullG (ZMod 2)) 1≤(10:ℕ).choose 2+1 :=
  dilated.actual_first_sparse (ZMod 2) (by decide) (by decide)
theorem dilated_charTwo_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ZMod 2) dilated.Variables (dilated.fullG (ZMod 2)) i≤ i*(10:ℕ).choose (i+1) :=
  dilated.actual_sparse_higher (ZMod 2) (by decide) (by decide) i hi hie
theorem dilated_charThree_first : totalBetti (ZMod 3) dilated.Variables (dilated.fullG (ZMod 3)) 1≤(10:ℕ).choose 2+1 :=
  dilated.actual_first_sparse (ZMod 3) (by decide) (by decide)
theorem dilated_charThree_higher (i : ℕ) (hi : 2 ≤ i) (hie : i≤6) :
    totalBetti (ZMod 3) dilated.Variables (dilated.fullG (ZMod 3)) i≤ i*(10:ℕ).choose (i+1) :=
  dilated.actual_sparse_higher (ZMod 3) (by decide) (by decide) i hi hie

variable (k : Type) [Field k]
theorem nonCM_PC : six.coreP k=15 := by rw [six.coreP_computed];simp_rw [six_minima_cached];decide
theorem nonCM_PG : six.actualP k=10 := by rw [six.actualP_computed];simp_rw [six_survivors_cached];decide
theorem nonCM_cap (r : Fin six.u) : (0,2)∈six.competitorFiber r := by
  rw [←six.competitorTest_iff]
  unfold Endpoint.Data.competitorTest
  simp_rw [six_minima_cached]
  fin_cases r <;> decide
theorem nonCM_R : six.actualR k=1 := by rw [six.actualR_computed_window k 2 nonCM_cap];simp_rw [six_window_cached];decide
theorem nonCM_preserved : six.coreP k≠six.actualP k ∧ 0<six.actualR k := by
  rw [nonCM_PC,nonCM_PG,nonCM_R]
  decide
theorem top_row_charTwo : totalBetti (ZMod 2) six.Variables (six.fullG (ZMod 2)) 6≤
    6*(10:ℕ).choose 7 := six.actual_sparse_higher (ZMod 2) (by decide) (by decide) 6 (by decide) (by decide)
theorem beyond_source_charThree : totalBetti (ZMod 3) six.Variables (six.fullG (ZMod 3)) 7=0 :=
  six.actual_endpoint_above (ZMod 3) 7 (by decide)
end Run18SparseAcceptance
