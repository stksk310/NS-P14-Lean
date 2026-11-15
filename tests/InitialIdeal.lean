module
public import NSP14.Lex.InitialIdeal
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.InitialIdeal
/-- Whole Hilbert function, actual homogeneous ideal, and actual monomial initial ideal. -/
theorem actual_initial_Hilbert (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (J : Ideal (MvPolynomial (Fin q) k))
      (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      Lex.IsMonomial k q J ∧ ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q J hJ n := by
  exact ⟨Lex.initialIdeal k q MonomialOrder.degLex I,
    Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I,
    Lex.initialIdeal_isMonomial k q MonomialOrder.degLex I,
    Lex.initialIdeal_sameHilbert k q I hI⟩
theorem actual_principal_initial (k : Type) [Field k] (q : ℕ) (m : MonomialOrder (Fin q))
    (p : MvPolynomial (Fin q) k) (hp : p ≠ 0) :
    Lex.initialIdeal k q m (Ideal.span {p})=Ideal.span {MvPolynomial.monomial (m.degree p) (1:k)} :=
  Lex.initialIdeal_span_singleton k q m p hp
end NSP14.Tests.InitialIdeal
