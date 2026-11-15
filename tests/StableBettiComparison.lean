module
public import NSP14.Lex.StableBettiComparison
@[expose] public section
namespace NSP14.Tests.StableBettiComparison
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_all_graded_rows (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) (hL : Lex.IsLex k q L)
    (hHomI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hHomL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hH : ∀ n,Lex.quotientHilbert k q I hHomI n=Lex.quotientHilbert k q L hHomL n)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    Lex.quotientGradedBetti k q I hHomI i t≤Lex.quotientGradedBetti k q L hHomL i t :=
  Lex.IsStronglyStable.graded_betti_le_lex k q I L hI hL hHomI hHomL hH i hi t
end NSP14.Tests.StableBettiComparison
