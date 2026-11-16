module
public import NSP14.Lex.DistractionGraded
public import tests.LexLinearQuotientExamples
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.DistractionGradedExamples
open LexLinearQuotientExamples
variable (k : Type) [Field k]
local notation "K" => Lex.GenericDistractionField k 2

def DistractionMixedGradedRows : Prop := ∀ i : ℕ, 1 ≤ i → ∀ t : ℤ,
  Lex.quotientGradedBetti K 2 (Lex.genericDistractionIdeal k 2 (mixedIdeal K))
    (Lex.genericDistractionIdeal_homogeneous k 2 (mixedIdeal K)) i t=
      (if i=1 ∧ t=1 then 1 else 0)+(if i=1 ∧ t=2 then 1 else 0)+
      (if i=2 ∧ t=3 then 1 else 0)

theorem distraction_mixed_graded_rows : DistractionMixedGradedRows k := by
  intro i hi t
  rw [← Lex.genericDistraction_gradedBetti k 2 (mixedIdeal K) (mixed_homogeneous K) (mixed_lex K).1]
  exact mixed_graded_rows K i hi t

theorem base_char0 : DistractionMixedGradedRows ℚ := distraction_mixed_graded_rows ℚ
theorem base_char2 : DistractionMixedGradedRows (ZMod 2) := distraction_mixed_graded_rows (ZMod 2)
theorem base_char3 : DistractionMixedGradedRows (ZMod 3) := distraction_mixed_graded_rows (ZMod 3)
end NSP14.Tests.DistractionGradedExamples
