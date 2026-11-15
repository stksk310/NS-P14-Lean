module
public import NSP14.Lex.PrefixGeneratorCorrection
public import tests.LexLinearQuotientExamples
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Tests.PrefixGeneratorCorrection
open NSP14.Lex
open NSP14.Tests.LexLinearQuotientExamples
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type) [Field k]

theorem mixed_actual_last_generator_count (n : ℕ) :
    maxGeneratorDegreeCard k 2 (mixedIdeal k) n=if n=2 then 1 else 0 := by
  have hs : IsStronglyStable k 2 (mixedIdeal k) :=
    ⟨(mixed_lex k).1,fun v hv a b hp hab => (mixed_lex k).raise k 2 v hv a b hp hab⟩
  have hc := hs.top_gradedBetti_eq_generator_card k 2 (mixedIdeal k) (mixed_proper k) (mixed_homogeneous k) (by decide) n
  have hb := mixed_graded_rows k 2 (by decide) ((n:ℤ)+1)
  have he : (n:ℤ)+1=3 ↔ n=2 := by omega
  norm_num [he] at hb
  simpa only [Nat.reduceSub] using hc.symm.trans hb

theorem mixed_generator_degrees_char0 :
    maxGeneratorDegreeCard ℚ 2 (mixedIdeal ℚ) 1=0 ∧ maxGeneratorDegreeCard ℚ 2 (mixedIdeal ℚ) 2=1 ∧
      maxGeneratorDegreeCard ℚ 2 (mixedIdeal ℚ) 3=0 := by
  simpa using And.intro (mixed_actual_last_generator_count ℚ 1) (And.intro (mixed_actual_last_generator_count ℚ 2) (mixed_actual_last_generator_count ℚ 3))
theorem mixed_generator_degrees_char2 :
    maxGeneratorDegreeCard (ZMod 2) 2 (mixedIdeal (ZMod 2)) 1=0 ∧ maxGeneratorDegreeCard (ZMod 2) 2 (mixedIdeal (ZMod 2)) 2=1 ∧
      maxGeneratorDegreeCard (ZMod 2) 2 (mixedIdeal (ZMod 2)) 3=0 := by
  simpa using And.intro (mixed_actual_last_generator_count (ZMod 2) 1) (And.intro (mixed_actual_last_generator_count (ZMod 2) 2) (mixed_actual_last_generator_count (ZMod 2) 3))
theorem mixed_generator_degrees_char3 :
    maxGeneratorDegreeCard (ZMod 3) 2 (mixedIdeal (ZMod 3)) 1=0 ∧ maxGeneratorDegreeCard (ZMod 3) 2 (mixedIdeal (ZMod 3)) 2=1 ∧
      maxGeneratorDegreeCard (ZMod 3) 2 (mixedIdeal (ZMod 3)) 3=0 := by
  simpa using And.intro (mixed_actual_last_generator_count (ZMod 3) 1) (And.intro (mixed_actual_last_generator_count (ZMod 3) 2) (mixed_actual_last_generator_count (ZMod 3) 3))
end NSP14.Tests.PrefixGeneratorCorrection
