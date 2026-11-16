module
public import tests.MainActualExamples
public import tests.V06Dense
@[expose] public section
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run20Rows
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem row_zero : S.IntervalComparison k 0 := S.p14_totalBetti_le_intervalCompletion k 0
theorem source_top : S.IntervalComparison k S.embeddingDimension := S.p14_totalBetti_le_intervalCompletion k S.embeddingDimension
theorem source_plus_one : S.IntervalComparison k (S.embeddingDimension+1) := S.p14_totalBetti_le_intervalCompletion k (S.embeddingDimension+1)
theorem target_top : S.IntervalComparison k S.intervalCompletionAll.embeddingDimension := S.p14_totalBetti_le_intervalCompletion k S.intervalCompletionAll.embeddingDimension

theorem source_above (i : ℕ) (hi : S.embeddingDimension < i) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i=0 :=
  totalBetti_eq_zero_of_gt k S.AtomExponent _ i (by rwa [S.atomExponent_card])

open Run20Examples
theorem ordinary_source_fifth :
    totalBetti k fourOrdinary.source.AtomExponent
      (ModuleCat.of (fourOrdinary.source.FullPolynomialRing k)
        (fourOrdinary.source.FormalTangentAlgebra k)) 5=0 :=
  source_above fourOrdinary.source k 5 (by rw [fourOrdinary.embeddingDimension];decide)

/-- Source has four atoms; the target has six, and its fifth Betti number is 5. -/
theorem ordinary_target_fifth :
    totalBetti k fourOrdinary.source.intervalCompletionAll.AtomExponent
      (ModuleCat.of (fourOrdinary.source.intervalCompletionAll.FullPolynomialRing k)
        (fourOrdinary.source.intervalCompletionAll.FormalTangentAlgebra k)) 5=5 := by
  rw [fourOrdinary.source.intervalCompletionAll_completed_totalBetti
    (by rw [fourOrdinary.embeddingDimension];decide) k 5]
  rw [fourOrdinary.source.ordinary_interval_completed_betti k
    (by rw [fourOrdinary.embeddingDimension];decide)
    (by rw [fourOrdinary.width,fourOrdinary.multiplicity];decide) 5 (by decide),fourOrdinary.multiplicity]
  rfl

theorem ordinary_fifth_comparison : fourOrdinary.source.IntervalComparison k 5 := fourOrdinary.source.p14_totalBetti_le_intervalCompletion k 5
example := ordinary_target_fifth (ZMod 2)
example := ordinary_target_fifth (ZMod 3)
example := ordinary_target_fifth ℚ

theorem nonCM_main (i : ℕ) :
    (Run18SparseAcceptance.six.coreP k≠Run18SparseAcceptance.six.actualP k ∧
      0<Run18SparseAcceptance.six.actualR k) ∧ Run18SparseAcceptance.six.source.IntervalComparison k i :=
  ⟨Run18SparseAcceptance.nonCM_preserved k,Run18SparseAcceptance.six.source.p14_totalBetti_le_intervalCompletion k i⟩
theorem dense_equality_and_main (i : ℕ) :
    ((0+1)*(5:ℕ).choose (0+2)+11*(4:ℕ).choose 0+3*(5:ℕ).choose 0+4*(3:ℕ).choose 0=
      (0+1)*(8:ℕ).choose (0+2)) ∧ DenseResources.q4_t3.source.IntervalComparison k i :=
  ⟨V06Dense.q4_t3_j0_eq,DenseResources.q4_t3.source.p14_totalBetti_le_intervalCompletion k i⟩
end NSP14.Tests.Run20Rows
