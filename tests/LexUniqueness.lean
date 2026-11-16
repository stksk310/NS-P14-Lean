module
public import NSP14.Lex.Uniqueness
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.LexUniqueness
variable (k L : Type) [Field k] [Field L] (q : ℕ)

theorem actual_lex_unique (I J : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlI : Lex.IsLex k q I) (hlJ : Lex.IsLex k q J)
    (hH : ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q J hJ n) : I=J :=
  Lex.IsLex.eq_of_sameHilbert k q I J hI hJ hlI hlJ hH

theorem actual_lex_support_unique (I : Ideal (MvPolynomial (Fin q) k))
    (J : Ideal (MvPolynomial (Fin q) L))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L))
    (hlI : Lex.IsLex k q I) (hlJ : Lex.IsLex L q J)
    (hH : ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert L q J hJ n)
    (a : Fin q →₀ ℕ) : MvPolynomial.monomial a (1:k)∈I ↔ MvPolynomial.monomial a (1:L)∈J :=
  Lex.IsLex.monomial_mem_iff_of_sameHilbert k L q I J hI hJ hlI hlJ hH a
end NSP14.Tests.LexUniqueness
