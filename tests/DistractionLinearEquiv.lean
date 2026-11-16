module
public import NSP14.Lex.DistractionLinearEquiv
@[expose] public section
open scoped Classical
namespace NSP14.Tests.DistractionLinearEquiv
theorem actual_all_monomial_images (k : Type) [Field k] (q : ℕ) :
    ∃ e : MvPolynomial (Fin q) (Lex.GenericDistractionField k q) ≃ₗ[Lex.GenericDistractionField k q]
      MvPolynomial (Fin q) (Lex.GenericDistractionField k q),
      ∀ a : Fin q →₀ ℕ, e (MvPolynomial.monomial a 1)=Lex.genericFieldDistraction k q a :=
  ⟨Lex.genericPolynomialEquiv k q, Lex.genericPolynomialEquiv_monomial k q⟩
end NSP14.Tests.DistractionLinearEquiv
