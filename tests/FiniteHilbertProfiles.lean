module
public import NSP14.Lex.FiniteHilbertProfiles
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.FiniteHilbertProfiles
variable (k : Type) [Field k] (q : ℕ)

theorem actual_fixed_hilbert_finite (H : ℕ → ℕ) :
    {I : Ideal (MvPolynomial (Fin q) k) | Lex.IsMonomial k q I ∧
      ∃ hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k),
        ∀ n,Lex.quotientHilbert k q I hI n=H n}.Finite :=
  Lex.finite_monomialIdeals_sameHilbert k q H

omit [Field k] in
theorem all_fields_generator_bound (H : ℕ → ℕ) :
    ∃ B : ℕ,∀ (L : Type) [Field L] (I : Ideal (MvPolynomial (Fin q) L))
      (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L)),
      Lex.IsMonomial L q I → (∀ n,Lex.quotientHilbert L q I hI n=H n) →
      ∀ a,Lex.MinimalGenerator L q I a → a.degree≤B :=
  Lex.uniform_monomialGenerator_degree_bound q H
end NSP14.Tests.FiniteHilbertProfiles
