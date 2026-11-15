module
public import audit.run18.ClosedGoals
public import tests.WidthDenseResources
public import tests.WidthSparse
public import tests.WidthEdgeGeneral
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14.Homological
set_option synthInstance.maxHeartbeats 200000
namespace NSP14.Tests.WidthActualClosure

theorem frozen_all_six : Run18.Requested.X_BHP_EK ∧ Run18.Requested.W_EDGE ∧ Run18.Requested.W_DENSE ∧
    Run18.Requested.W_SPARSE ∧ Run18.Requested.W_FIVE ∧ Run18.Requested.W_CLOSE := Run18.all_closed

def SourceRow (D : Endpoint.Data) (k : Type) [Field k] (he : 2≤D.source.embeddingDimension) (i : ℕ) : Prop :=
  totalBetti k D.source.AtomExponent (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
    totalBetti k (D.source.intervalCompletion he).AtomExponent
      (ModuleCat.of ((D.source.intervalCompletion he).FullPolynomialRing k) ((D.source.intervalCompletion he).FormalTangentAlgebra k)) i

def BoundaryRows (D : Endpoint.Data) (k : Type) [Field k] (he : 2≤D.source.embeddingDimension) : Prop :=
  SourceRow D k he 0 ∧ SourceRow D k he (D.q+2) ∧ SourceRow D k he (D.q+3) ∧
    SourceRow D k he ((D.source.intervalCompletion he).embeddingDimension)

theorem original_source (D : Endpoint.Data) (k : Type) [Field k]
    (hq : 3≤D.q) (hphys : D.d*D.u≤D.m-2) :
    Run18.Requested.Comparison D.source k (by rw [D.embeddingDimension]; omega) := by
  have he : 5≤D.source.embeddingDimension := by rw [D.embeddingDimension]; omega
  have hw : D.source.width≤D.source.multiplicity-2 := by rw [D.width,D.multiplicity]; exact hphys
  exact D.source.narrow_width_comparison k he hw

theorem original_boundaries (D : Endpoint.Data) (k : Type) [Field k]
    (hq : 3≤D.q) (hphys : D.d*D.u≤D.m-2) :
    BoundaryRows D k (by rw [D.embeddingDimension]; omega) := by
  have he : 2≤D.source.embeddingDimension := by rw [D.embeddingDimension]; omega
  have h : Run18.Requested.Comparison D.source k he := original_source D k hq hphys
  exact ⟨h 0,h (D.q+2),h (D.q+3),h ((D.source.intervalCompletion he).embeddingDimension)⟩

def dilatedAP : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem dilatedAP_physical_minimum : dilatedAP.m=dilatedAP.d*dilatedAP.u+2 := by decide

def dilatedHole : Endpoint.Data where
  m := 20
  d := 3
  u := 6
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem dilatedHole_physical_minimum : dilatedHole.m=dilatedHole.d*dilatedHole.u+2 := by decide

def dilatedDense2 : Endpoint.Data where
  m := 23
  d := 3
  u := 7
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem dilatedDense2_physical_minimum : dilatedDense2.m=dilatedDense2.d*dilatedDense2.u+2 := by decide

def dilatedDense3 : Endpoint.Data where
  m := 26
  d := 3
  u := 8
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem dilatedDense3_physical_minimum : dilatedDense3.m=dilatedDense3.d*dilatedDense3.u+2 := by decide

def dilatedDense4 : Endpoint.Data where
  m := 29
  d := 3
  u := 9
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem dilatedDense4_physical_minimum : dilatedDense4.m=dilatedDense4.d*dilatedDense4.u+2 := by decide

theorem dilatedAP_Q_boundaries : BoundaryRows dilatedAP (ℚ) (by rw [dilatedAP.embeddingDimension]; decide) :=
  original_boundaries dilatedAP (ℚ) (by decide) (by decide)

theorem dilatedAP_char2_boundaries : BoundaryRows dilatedAP (ZMod 2) (by rw [dilatedAP.embeddingDimension]; decide) :=
  original_boundaries dilatedAP (ZMod 2) (by decide) (by decide)

theorem dilatedAP_char3_boundaries : BoundaryRows dilatedAP (ZMod 3) (by rw [dilatedAP.embeddingDimension]; decide) :=
  original_boundaries dilatedAP (ZMod 3) (by decide) (by decide)

theorem dilatedHole_Q_boundaries : BoundaryRows dilatedHole (ℚ) (by rw [dilatedHole.embeddingDimension]; decide) :=
  original_boundaries dilatedHole (ℚ) (by decide) (by decide)

theorem dilatedHole_char2_boundaries : BoundaryRows dilatedHole (ZMod 2) (by rw [dilatedHole.embeddingDimension]; decide) :=
  original_boundaries dilatedHole (ZMod 2) (by decide) (by decide)

theorem dilatedHole_char3_boundaries : BoundaryRows dilatedHole (ZMod 3) (by rw [dilatedHole.embeddingDimension]; decide) :=
  original_boundaries dilatedHole (ZMod 3) (by decide) (by decide)

theorem dilatedDense2_Q_boundaries : BoundaryRows dilatedDense2 (ℚ) (by rw [dilatedDense2.embeddingDimension]; decide) :=
  original_boundaries dilatedDense2 (ℚ) (by decide) (by decide)

theorem dilatedDense2_char2_boundaries : BoundaryRows dilatedDense2 (ZMod 2) (by rw [dilatedDense2.embeddingDimension]; decide) :=
  original_boundaries dilatedDense2 (ZMod 2) (by decide) (by decide)

theorem dilatedDense2_char3_boundaries : BoundaryRows dilatedDense2 (ZMod 3) (by rw [dilatedDense2.embeddingDimension]; decide) :=
  original_boundaries dilatedDense2 (ZMod 3) (by decide) (by decide)

theorem dilatedDense3_Q_boundaries : BoundaryRows dilatedDense3 (ℚ) (by rw [dilatedDense3.embeddingDimension]; decide) :=
  original_boundaries dilatedDense3 (ℚ) (by decide) (by decide)

theorem dilatedDense3_char2_boundaries : BoundaryRows dilatedDense3 (ZMod 2) (by rw [dilatedDense3.embeddingDimension]; decide) :=
  original_boundaries dilatedDense3 (ZMod 2) (by decide) (by decide)

theorem dilatedDense3_char3_boundaries : BoundaryRows dilatedDense3 (ZMod 3) (by rw [dilatedDense3.embeddingDimension]; decide) :=
  original_boundaries dilatedDense3 (ZMod 3) (by decide) (by decide)

theorem dilatedDense4_Q_boundaries : BoundaryRows dilatedDense4 (ℚ) (by rw [dilatedDense4.embeddingDimension]; decide) :=
  original_boundaries dilatedDense4 (ℚ) (by decide) (by decide)

theorem dilatedDense4_char2_boundaries : BoundaryRows dilatedDense4 (ZMod 2) (by rw [dilatedDense4.embeddingDimension]; decide) :=
  original_boundaries dilatedDense4 (ZMod 2) (by decide) (by decide)

theorem dilatedDense4_char3_boundaries : BoundaryRows dilatedDense4 (ZMod 3) (by rw [dilatedDense4.embeddingDimension]; decide) :=
  original_boundaries dilatedDense4 (ZMod 3) (by decide) (by decide)

theorem dense2_Q_boundaries : BoundaryRows DenseResources.q4_t2 (ℚ) (by rw [DenseResources.q4_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t2 (ℚ) (by decide) (by decide)

theorem dense2_char2_boundaries : BoundaryRows DenseResources.q4_t2 (ZMod 2) (by rw [DenseResources.q4_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t2 (ZMod 2) (by decide) (by decide)

theorem dense2_char3_boundaries : BoundaryRows DenseResources.q4_t2 (ZMod 3) (by rw [DenseResources.q4_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t2 (ZMod 3) (by decide) (by decide)

theorem dense3_Q_boundaries : BoundaryRows DenseResources.q4_t3 (ℚ) (by rw [DenseResources.q4_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t3 (ℚ) (by decide) (by decide)

theorem dense3_char2_boundaries : BoundaryRows DenseResources.q4_t3 (ZMod 2) (by rw [DenseResources.q4_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t3 (ZMod 2) (by decide) (by decide)

theorem dense3_char3_boundaries : BoundaryRows DenseResources.q4_t3 (ZMod 3) (by rw [DenseResources.q4_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t3 (ZMod 3) (by decide) (by decide)

theorem dense4_Q_boundaries : BoundaryRows DenseResources.q4_t4 (ℚ) (by rw [DenseResources.q4_t4.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t4 (ℚ) (by decide) (by decide)

theorem dense4_char2_boundaries : BoundaryRows DenseResources.q4_t4 (ZMod 2) (by rw [DenseResources.q4_t4.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t4 (ZMod 2) (by decide) (by decide)

theorem dense4_char3_boundaries : BoundaryRows DenseResources.q4_t4 (ZMod 3) (by rw [DenseResources.q4_t4.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q4_t4 (ZMod 3) (by decide) (by decide)

theorem sparse_Q_boundaries : BoundaryRows Run18SparseAcceptance.six (ℚ) (by rw [Run18SparseAcceptance.six.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.six (ℚ) (by decide) (by decide)

theorem sparse_char2_boundaries : BoundaryRows Run18SparseAcceptance.six (ZMod 2) (by rw [Run18SparseAcceptance.six.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.six (ZMod 2) (by decide) (by decide)

theorem sparse_char3_boundaries : BoundaryRows Run18SparseAcceptance.six (ZMod 3) (by rw [Run18SparseAcceptance.six.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.six (ZMod 3) (by decide) (by decide)

theorem dilatedSparse_Q_boundaries : BoundaryRows Run18SparseAcceptance.dilated (ℚ) (by rw [Run18SparseAcceptance.dilated.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.dilated (ℚ) (by decide) (by decide)

theorem dilatedSparse_char2_boundaries : BoundaryRows Run18SparseAcceptance.dilated (ZMod 2) (by rw [Run18SparseAcceptance.dilated.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.dilated (ZMod 2) (by decide) (by decide)

theorem dilatedSparse_char3_boundaries : BoundaryRows Run18SparseAcceptance.dilated (ZMod 3) (by rw [Run18SparseAcceptance.dilated.embeddingDimension]; decide) :=
  original_boundaries Run18SparseAcceptance.dilated (ZMod 3) (by decide) (by decide)

theorem fiveAP_Q_boundaries : BoundaryRows DenseResources.q3_t0 (ℚ) (by rw [DenseResources.q3_t0.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t0 (ℚ) (by decide) (by decide)

theorem fiveAP_char2_boundaries : BoundaryRows DenseResources.q3_t0 (ZMod 2) (by rw [DenseResources.q3_t0.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t0 (ZMod 2) (by decide) (by decide)

theorem fiveAP_char3_boundaries : BoundaryRows DenseResources.q3_t0 (ZMod 3) (by rw [DenseResources.q3_t0.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t0 (ZMod 3) (by decide) (by decide)

theorem fiveHole_Q_boundaries : BoundaryRows DenseResources.q3_t1 (ℚ) (by rw [DenseResources.q3_t1.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t1 (ℚ) (by decide) (by decide)

theorem fiveHole_char2_boundaries : BoundaryRows DenseResources.q3_t1 (ZMod 2) (by rw [DenseResources.q3_t1.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t1 (ZMod 2) (by decide) (by decide)

theorem fiveHole_char3_boundaries : BoundaryRows DenseResources.q3_t1 (ZMod 3) (by rw [DenseResources.q3_t1.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t1 (ZMod 3) (by decide) (by decide)

theorem fiveDense2_Q_boundaries : BoundaryRows DenseResources.q3_t2 (ℚ) (by rw [DenseResources.q3_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t2 (ℚ) (by decide) (by decide)

theorem fiveDense2_char2_boundaries : BoundaryRows DenseResources.q3_t2 (ZMod 2) (by rw [DenseResources.q3_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t2 (ZMod 2) (by decide) (by decide)

theorem fiveDense2_char3_boundaries : BoundaryRows DenseResources.q3_t2 (ZMod 3) (by rw [DenseResources.q3_t2.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t2 (ZMod 3) (by decide) (by decide)

theorem fiveDense3_Q_boundaries : BoundaryRows DenseResources.q3_t3 (ℚ) (by rw [DenseResources.q3_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t3 (ℚ) (by decide) (by decide)

theorem fiveDense3_char2_boundaries : BoundaryRows DenseResources.q3_t3 (ZMod 2) (by rw [DenseResources.q3_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t3 (ZMod 2) (by decide) (by decide)

theorem fiveDense3_char3_boundaries : BoundaryRows DenseResources.q3_t3 (ZMod 3) (by rw [DenseResources.q3_t3.embeddingDimension]; decide) :=
  original_boundaries DenseResources.q3_t3 (ZMod 3) (by decide) (by decide)

theorem nonCM_actual_application (k : Type) [Field k] :
    (Run18SparseAcceptance.six.coreP k≠Run18SparseAcceptance.six.actualP k ∧ 0<Run18SparseAcceptance.six.actualR k) ∧
      BoundaryRows Run18SparseAcceptance.six k (by rw [Run18SparseAcceptance.six.embeddingDimension]; decide) :=
  ⟨Run18SparseAcceptance.nonCM_preserved k,original_boundaries Run18SparseAcceptance.six k (by decide) (by decide)⟩
end NSP14.Tests.WidthActualClosure
