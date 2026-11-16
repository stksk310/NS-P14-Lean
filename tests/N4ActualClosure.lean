module
public import NSP14.NarrowFour.Comparison
public import Mathlib.Algebra.Field.ZMod
public import NSP14.Endpoint.FiniteSocleWindow
@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 0
open NSP14

example (S : NumericalSemigroup) (k : Type) [Field k] (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) := NarrowFour.narrow_four_comparison S k he hw
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S ℚ he hw 0
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S (ZMod 2) he hw 4
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S (ZMod 3) he hw 5
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hm : D.d*D.u+2 ≤ D.m) :=
  NarrowFour.narrow_four_comparison D.source k (by rw [D.embeddingDimension,hq])
    (by rw [D.width,D.multiplicity];omega)

namespace NSP14.Tests.Run19N4NonCM
open scoped Classical
def D : Endpoint.Data where
  m := 8
  d := 1
  u := 6
  a := {1,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem cap (r : Fin D.u) : (0,4)∈D.competitorFiber r := by
  rw [←D.competitorTest_iff]
  fin_cases r <;> decide
example (k : Type) [Field k] : D.coreP k=9 ∧ D.actualP k=6 ∧ D.actualR k=1 := by
  refine ⟨?_,?_,?_⟩
  · rw [D.coreP_computed];decide
  · rw [D.actualP_computed];decide
  · rw [D.actualR_computed_window k 4 cap];decide
example (k : Type) [Field k] (i : ℕ) := NarrowFour.narrow_four_comparison D.source k
  (by rw [D.embeddingDimension];rfl) (by rw [D.width,D.multiplicity];decide) i
end NSP14.Tests.Run19N4NonCM
