module
public import NSP14.Main
public import NSP14.ArithmeticSequence.Width
public import tests.SmallEmbeddingBase
public import tests.N4WidthFour
public import tests.N4ActualClosure
public import tests.WidthActualClosure
public import tests.WidthFive
@[expose] public section
open NSP14 NSP14.Homological
open scoped Classical
namespace NSP14.Tests.Run20Examples

def threeNarrow : ArithmeticSequence.Data where
  m := 4
  d := 1
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

def threeWide : SmallEmbedding.ThreeData where
  m := 4
  d := 1
  u := 3
  a := {1}
  q_one := by decide
  a_pos := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  a_lt := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def fourOrdinary : Endpoint.Data where
  m := 6
  d := 1
  u := 5
  a := {1,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem threeNarrow_atoms : threeNarrow.source.atoms={4,5,6} := by rw [threeNarrow.atoms];decide
theorem threeWide_atoms : threeWide.source.atoms={4,5,7} := by rw [threeWide.atoms];decide
theorem fourNarrow_atoms : (Run19WidthFour.data 6 (by omega)).source.atoms={6,7,9,10} := by
  rw [Endpoint.Data.atoms];decide
theorem fourOrdinary_atoms : fourOrdinary.source.atoms={6,7,9,11} := by rw [fourOrdinary.atoms];decide

theorem threeNarrow_boundary : threeNarrow.source.parameterRegion 2 ∧
    threeNarrow.source.width=threeNarrow.source.multiplicity-2 := by
  constructor
  · change threeNarrow.source.embeddingDimension=3;rw [threeNarrow.embeddingDimension];rfl
  · rw [threeNarrow.width,threeNarrow.multiplicity];rfl

theorem threeWide_boundary : threeWide.source.parameterRegion 2 ∧
    threeWide.source.width=threeWide.source.multiplicity-1 := by
  constructor
  · change threeWide.source.embeddingDimension=3;rw [threeWide.embeddingDimension];rfl
  · rw [threeWide.width,threeWide.multiplicity];rfl

theorem fourNarrow_boundary : (Run19WidthFour.data 6 (by omega)).source.parameterRegion 4 := by
  constructor
  · rw [Endpoint.Data.embeddingDimension];rfl
  · rw [Endpoint.Data.width,Endpoint.Data.multiplicity];decide

theorem fourOrdinary_boundary : fourOrdinary.source.parameterRegion 3 := by
  constructor
  · rw [fourOrdinary.embeddingDimension];decide
  · rw [fourOrdinary.width,fourOrdinary.multiplicity];decide

theorem naturals (k : Type) [Field k] (i : ℕ) : Run19Base.naturals.IntervalComparison k i :=
  Run19Base.naturals.p14_totalBetti_le_intervalCompletion k i
theorem naturals_Q (i : ℕ) : Run19Base.naturals.IntervalComparison ℚ i := Run19Base.naturals.p14_totalBetti_le_intervalCompletion ℚ i
theorem naturals_char2 (i : ℕ) : Run19Base.naturals.IntervalComparison (ZMod 2) i := Run19Base.naturals.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem naturals_char3 (i : ℕ) : Run19Base.naturals.IntervalComparison (ZMod 3) i := Run19Base.naturals.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem two_three (k : Type) [Field k] (i : ℕ) : Run19Base.twoThree.source.IntervalComparison k i :=
  Run19Base.twoThree.source.p14_totalBetti_le_intervalCompletion k i
theorem two_three_Q (i : ℕ) : Run19Base.twoThree.source.IntervalComparison ℚ i := Run19Base.twoThree.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem two_three_char2 (i : ℕ) : Run19Base.twoThree.source.IntervalComparison (ZMod 2) i := Run19Base.twoThree.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem two_three_char3 (i : ℕ) : Run19Base.twoThree.source.IntervalComparison (ZMod 3) i := Run19Base.twoThree.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem three_five (k : Type) [Field k] (i : ℕ) : Run19Base.threeFive.source.IntervalComparison k i :=
  Run19Base.threeFive.source.p14_totalBetti_le_intervalCompletion k i
theorem three_five_Q (i : ℕ) : Run19Base.threeFive.source.IntervalComparison ℚ i := Run19Base.threeFive.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem three_five_char2 (i : ℕ) : Run19Base.threeFive.source.IntervalComparison (ZMod 2) i := Run19Base.threeFive.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem three_five_char3 (i : ℕ) : Run19Base.threeFive.source.IntervalComparison (ZMod 3) i := Run19Base.threeFive.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem three_narrow (k : Type) [Field k] (i : ℕ) : threeNarrow.source.IntervalComparison k i :=
  threeNarrow.source.p14_totalBetti_le_intervalCompletion k i
theorem three_narrow_Q (i : ℕ) : threeNarrow.source.IntervalComparison ℚ i := threeNarrow.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem three_narrow_char2 (i : ℕ) : threeNarrow.source.IntervalComparison (ZMod 2) i := threeNarrow.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem three_narrow_char3 (i : ℕ) : threeNarrow.source.IntervalComparison (ZMod 3) i := threeNarrow.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem three_wide (k : Type) [Field k] (i : ℕ) : threeWide.source.IntervalComparison k i :=
  threeWide.source.p14_totalBetti_le_intervalCompletion k i
theorem three_wide_Q (i : ℕ) : threeWide.source.IntervalComparison ℚ i := threeWide.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem three_wide_char2 (i : ℕ) : threeWide.source.IntervalComparison (ZMod 2) i := threeWide.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem three_wide_char3 (i : ℕ) : threeWide.source.IntervalComparison (ZMod 3) i := threeWide.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem four_narrow (k : Type) [Field k] (i : ℕ) : (Run19WidthFour.data 6 (by omega)).source.IntervalComparison k i :=
  (Run19WidthFour.data 6 (by omega)).source.p14_totalBetti_le_intervalCompletion k i
theorem four_narrow_Q (i : ℕ) : (Run19WidthFour.data 6 (by omega)).source.IntervalComparison ℚ i := (Run19WidthFour.data 6 (by omega)).source.p14_totalBetti_le_intervalCompletion ℚ i
theorem four_narrow_char2 (i : ℕ) : (Run19WidthFour.data 6 (by omega)).source.IntervalComparison (ZMod 2) i := (Run19WidthFour.data 6 (by omega)).source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem four_narrow_char3 (i : ℕ) : (Run19WidthFour.data 6 (by omega)).source.IntervalComparison (ZMod 3) i := (Run19WidthFour.data 6 (by omega)).source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem four_ordinary (k : Type) [Field k] (i : ℕ) : fourOrdinary.source.IntervalComparison k i :=
  fourOrdinary.source.p14_totalBetti_le_intervalCompletion k i
theorem four_ordinary_Q (i : ℕ) : fourOrdinary.source.IntervalComparison ℚ i := fourOrdinary.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem four_ordinary_char2 (i : ℕ) : fourOrdinary.source.IntervalComparison (ZMod 2) i := fourOrdinary.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem four_ordinary_char3 (i : ℕ) : fourOrdinary.source.IntervalComparison (ZMod 3) i := fourOrdinary.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem nonCM_four (k : Type) [Field k] (i : ℕ) : Run19N4NonCM.D.source.IntervalComparison k i :=
  Run19N4NonCM.D.source.p14_totalBetti_le_intervalCompletion k i
theorem nonCM_four_Q (i : ℕ) : Run19N4NonCM.D.source.IntervalComparison ℚ i := Run19N4NonCM.D.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem nonCM_four_char2 (i : ℕ) : Run19N4NonCM.D.source.IntervalComparison (ZMod 2) i := Run19N4NonCM.D.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem nonCM_four_char3 (i : ℕ) : Run19N4NonCM.D.source.IntervalComparison (ZMod 3) i := Run19N4NonCM.D.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_AP (k : Type) [Field k] (i : ℕ) : WidthActualClosure.dilatedAP.source.IntervalComparison k i :=
  WidthActualClosure.dilatedAP.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_AP_Q (i : ℕ) : WidthActualClosure.dilatedAP.source.IntervalComparison ℚ i := WidthActualClosure.dilatedAP.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_AP_char2 (i : ℕ) : WidthActualClosure.dilatedAP.source.IntervalComparison (ZMod 2) i := WidthActualClosure.dilatedAP.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_AP_char3 (i : ℕ) : WidthActualClosure.dilatedAP.source.IntervalComparison (ZMod 3) i := WidthActualClosure.dilatedAP.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_hole (k : Type) [Field k] (i : ℕ) : WidthActualClosure.dilatedHole.source.IntervalComparison k i :=
  WidthActualClosure.dilatedHole.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_hole_Q (i : ℕ) : WidthActualClosure.dilatedHole.source.IntervalComparison ℚ i := WidthActualClosure.dilatedHole.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_hole_char2 (i : ℕ) : WidthActualClosure.dilatedHole.source.IntervalComparison (ZMod 2) i := WidthActualClosure.dilatedHole.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_hole_char3 (i : ℕ) : WidthActualClosure.dilatedHole.source.IntervalComparison (ZMod 3) i := WidthActualClosure.dilatedHole.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_dense2 (k : Type) [Field k] (i : ℕ) : WidthActualClosure.dilatedDense2.source.IntervalComparison k i :=
  WidthActualClosure.dilatedDense2.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_dense2_Q (i : ℕ) : WidthActualClosure.dilatedDense2.source.IntervalComparison ℚ i := WidthActualClosure.dilatedDense2.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_dense2_char2 (i : ℕ) : WidthActualClosure.dilatedDense2.source.IntervalComparison (ZMod 2) i := WidthActualClosure.dilatedDense2.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_dense2_char3 (i : ℕ) : WidthActualClosure.dilatedDense2.source.IntervalComparison (ZMod 3) i := WidthActualClosure.dilatedDense2.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_dense3 (k : Type) [Field k] (i : ℕ) : WidthActualClosure.dilatedDense3.source.IntervalComparison k i :=
  WidthActualClosure.dilatedDense3.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_dense3_Q (i : ℕ) : WidthActualClosure.dilatedDense3.source.IntervalComparison ℚ i := WidthActualClosure.dilatedDense3.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_dense3_char2 (i : ℕ) : WidthActualClosure.dilatedDense3.source.IntervalComparison (ZMod 2) i := WidthActualClosure.dilatedDense3.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_dense3_char3 (i : ℕ) : WidthActualClosure.dilatedDense3.source.IntervalComparison (ZMod 3) i := WidthActualClosure.dilatedDense3.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_dense4 (k : Type) [Field k] (i : ℕ) : WidthActualClosure.dilatedDense4.source.IntervalComparison k i :=
  WidthActualClosure.dilatedDense4.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_dense4_Q (i : ℕ) : WidthActualClosure.dilatedDense4.source.IntervalComparison ℚ i := WidthActualClosure.dilatedDense4.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_dense4_char2 (i : ℕ) : WidthActualClosure.dilatedDense4.source.IntervalComparison (ZMod 2) i := WidthActualClosure.dilatedDense4.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_dense4_char3 (i : ℕ) : WidthActualClosure.dilatedDense4.source.IntervalComparison (ZMod 3) i := WidthActualClosure.dilatedDense4.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem physical_sparse (k : Type) [Field k] (i : ℕ) : Run18SparseAcceptance.dilated.source.IntervalComparison k i :=
  Run18SparseAcceptance.dilated.source.p14_totalBetti_le_intervalCompletion k i
theorem physical_sparse_Q (i : ℕ) : Run18SparseAcceptance.dilated.source.IntervalComparison ℚ i := Run18SparseAcceptance.dilated.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem physical_sparse_char2 (i : ℕ) : Run18SparseAcceptance.dilated.source.IntervalComparison (ZMod 2) i := Run18SparseAcceptance.dilated.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem physical_sparse_char3 (i : ℕ) : Run18SparseAcceptance.dilated.source.IntervalComparison (ZMod 3) i := Run18SparseAcceptance.dilated.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem nonCM_six (k : Type) [Field k] (i : ℕ) : Run18SparseAcceptance.six.source.IntervalComparison k i :=
  Run18SparseAcceptance.six.source.p14_totalBetti_le_intervalCompletion k i
theorem nonCM_six_Q (i : ℕ) : Run18SparseAcceptance.six.source.IntervalComparison ℚ i := Run18SparseAcceptance.six.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem nonCM_six_char2 (i : ℕ) : Run18SparseAcceptance.six.source.IntervalComparison (ZMod 2) i := Run18SparseAcceptance.six.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem nonCM_six_char3 (i : ℕ) : Run18SparseAcceptance.six.source.IntervalComparison (ZMod 3) i := Run18SparseAcceptance.six.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem five_small (k : Type) [Field k] (i : ℕ) : DenseResources.q3_t0.source.IntervalComparison k i :=
  DenseResources.q3_t0.source.p14_totalBetti_le_intervalCompletion k i
theorem five_small_Q (i : ℕ) : DenseResources.q3_t0.source.IntervalComparison ℚ i := DenseResources.q3_t0.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem five_small_char2 (i : ℕ) : DenseResources.q3_t0.source.IntervalComparison (ZMod 2) i := DenseResources.q3_t0.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem five_small_char3 (i : ℕ) : DenseResources.q3_t0.source.IntervalComparison (ZMod 3) i := DenseResources.q3_t0.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem five_nonunit (k : Type) [Field k] (i : ℕ) : FiveHigher.antipodal_nonunit.source.IntervalComparison k i :=
  FiveHigher.antipodal_nonunit.source.p14_totalBetti_le_intervalCompletion k i
theorem five_nonunit_Q (i : ℕ) : FiveHigher.antipodal_nonunit.source.IntervalComparison ℚ i := FiveHigher.antipodal_nonunit.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem five_nonunit_char2 (i : ℕ) : FiveHigher.antipodal_nonunit.source.IntervalComparison (ZMod 2) i := FiveHigher.antipodal_nonunit.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem five_nonunit_char3 (i : ℕ) : FiveHigher.antipodal_nonunit.source.IntervalComparison (ZMod 3) i := FiveHigher.antipodal_nonunit.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem dense_equal_boundary (k : Type) [Field k] (i : ℕ) : DenseResources.q4_t3.source.IntervalComparison k i :=
  DenseResources.q4_t3.source.p14_totalBetti_le_intervalCompletion k i
theorem dense_equal_boundary_Q (i : ℕ) : DenseResources.q4_t3.source.IntervalComparison ℚ i := DenseResources.q4_t3.source.p14_totalBetti_le_intervalCompletion ℚ i
theorem dense_equal_boundary_char2 (i : ℕ) : DenseResources.q4_t3.source.IntervalComparison (ZMod 2) i := DenseResources.q4_t3.source.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem dense_equal_boundary_char3 (i : ℕ) : DenseResources.q4_t3.source.IntervalComparison (ZMod 3) i := DenseResources.q4_t3.source.p14_totalBetti_le_intervalCompletion (ZMod 3) i
theorem width_four_residues (m : ℕ) (hm : 6 ≤ m) (k : Type) [Field k] (i : ℕ) : (Run19WidthFour.data m hm).source.IntervalComparison k i :=
  (Run19WidthFour.data m hm).source.p14_totalBetti_le_intervalCompletion k i
end NSP14.Tests.Run20Examples
