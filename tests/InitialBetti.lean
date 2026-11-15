module
public import NSP14.Lex.InitialBetti
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.InitialBetti
theorem actual_initial_graded_comparison (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (i : ℕ) (t : ℤ) :
    Lex.quotientGradedBetti k q I hI i t ≤
      Lex.quotientGradedBetti k q (Lex.initialIdeal k q MonomialOrder.degLex I)
        (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) i t :=
  Lex.quotientGradedBetti_initial_le k q I hI i t

noncomputable def binomialIdeal (k : Type) [Field k] : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0^2+MvPolynomial.X 1^2}

theorem binomial_homogeneous (k : Type) [Field k] :
    (binomialIdeal k).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 2) k) := by
  apply Ideal.homogeneous_span
  rintro _ rfl
  refine ⟨2,?_⟩
  have h := MvPolynomial.IsHomogeneous.add
    ((MvPolynomial.isHomogeneous_X (R:=k) (0:Fin 2)).pow 2)
    ((MvPolynomial.isHomogeneous_X (R:=k) (1:Fin 2)).pow 2)
  rw [MvPolynomial.mem_homogeneousSubmodule]
  simpa only [one_mul] using h

def BinomialInitialComparison (k : Type) [Field k] : Prop := ∀ i : ℕ,∀ t : ℤ,
  Lex.quotientGradedBetti k 2 (binomialIdeal k) (binomial_homogeneous k) i t ≤
    Lex.quotientGradedBetti k 2 (Lex.initialIdeal k 2 MonomialOrder.degLex (binomialIdeal k))
      (Lex.initialIdeal_homogeneous k 2 MonomialOrder.degLex (binomialIdeal k)) i t

theorem binomial_initial_comparison (k : Type) [Field k] : BinomialInitialComparison k :=
  Lex.quotientGradedBetti_initial_le k 2 (binomialIdeal k) (binomial_homogeneous k)

theorem binomial_initial_char0 : BinomialInitialComparison ℚ := binomial_initial_comparison ℚ
theorem binomial_initial_char2 : BinomialInitialComparison (ZMod 2) := binomial_initial_comparison (ZMod 2)
theorem binomial_initial_char3 : BinomialInitialComparison (ZMod 3) := binomial_initial_comparison (ZMod 3)
end NSP14.Tests.InitialBetti
