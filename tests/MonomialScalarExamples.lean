module
public import NSP14.Lex.MonomialExtensionGraded
public import tests.LexLinearQuotientExamples
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.MonomialScalarExamples
open LexLinearQuotientExamples
variable (k : Type) [Field k]
local notation "K" => Lex.GenericDistractionField k 2

def OriginalDistractionRows : Prop := ∀ i : ℕ, 1 ≤ i → ∀ t : ℤ,
  Lex.quotientGradedBetti K 2
    (Lex.genericDistractionIdeal k 2 (Lex.monomialExtension k K 2 (mixedIdeal k)))
    (Lex.genericDistractionIdeal_homogeneous k 2 (Lex.monomialExtension k K 2 (mixedIdeal k))) i t=
      (if i=1 ∧ t=1 then 1 else 0)+(if i=1 ∧ t=2 then 1 else 0)+
      (if i=2 ∧ t=3 then 1 else 0)

theorem original_mixed_rows : OriginalDistractionRows k := by
  intro i hi t
  rw [Lex.genericDistraction_original_gradedBetti k 2 (mixedIdeal k) (mixed_homogeneous k) (mixed_lex k).1]
  exact mixed_graded_rows k i hi t

theorem char0 : OriginalDistractionRows ℚ := original_mixed_rows ℚ
theorem char2 : OriginalDistractionRows (ZMod 2) := original_mixed_rows (ZMod 2)
theorem char3 : OriginalDistractionRows (ZMod 3) := original_mixed_rows (ZMod 3)
end NSP14.Tests.MonomialScalarExamples
