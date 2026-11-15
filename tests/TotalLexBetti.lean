module
public import NSP14.Lex.TotalBettiComparison
@[expose] public section
namespace NSP14.Tests.TotalLexBetti
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_total_comparison (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : Lex.IsLex k q L) (hH : ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n)
    (i : ℕ) (hi : 1 ≤ i) :
    Homological.totalBetti k (Fin q) (Endpoint.artinModule k (Fin q) I) i≤Homological.totalBetti k (Fin q) (Endpoint.artinModule k (Fin q) L) i :=
  Lex.quotientTotalBetti_le_lex k q I L hI hL hlL hH i hi
end NSP14.Tests.TotalLexBetti
