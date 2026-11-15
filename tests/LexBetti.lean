module
public import NSP14.Lex.BettiComparison
@[expose] public section
namespace NSP14.Tests.LexBetti
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem arbitrary_homogeneous_all_graded_rows (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : Lex.IsLex k q L) (hH : ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    Lex.quotientGradedBetti k q I hI i t≤Lex.quotientGradedBetti k q L hL i t :=
  Lex.quotientGradedBetti_le_lex k q I L hI hL hlL hH i hi t
end NSP14.Tests.LexBetti
