module
public import NSP14.Lex.SmallVariableComparison
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.SmallVariableComparison
variable (k : Type) [Field k] (q : ℕ)

theorem actual_small_variable_bhp (hq : q≤2) (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : Lex.IsLex k q L)
    (hH : ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n)
    (i : ℕ) (t : ℤ) : Lex.quotientGradedBetti k q I hI i t≤Lex.quotientGradedBetti k q L hL i t :=
  Lex.quotientGradedBetti_le_lex_of_le_two k q hq I L hI hL hlL hH i t

theorem one_actual_whole_hilbert_lex (hq : q≤2) (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Ideal (MvPolynomial (Fin q) k))
      (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      Lex.IsLex k q L ∧ ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n :=
  Lex.exists_lex_sameHilbert_of_le_two k q hq I hI
end NSP14.Tests.SmallVariableComparison
