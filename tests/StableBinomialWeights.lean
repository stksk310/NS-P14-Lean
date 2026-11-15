module
public import NSP14.Lex.StableBinomialWeights
@[expose] public section
namespace NSP14.Tests.StableBinomialWeights
variable (k : Type) [Field k] (q d i : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_weighted_hilbert_comparison (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) (hL : Lex.IsLex k q L)
    (hHomI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hHomL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hH : Lex.quotientHilbert k q I hHomI d=Lex.quotientHilbert k q L hHomL d) :
    Lex.degreeBinomialSum k q I d i≤Lex.degreeBinomialSum k q L d i :=
  Lex.IsStronglyStable.binomial_degree_sum_le_lex_of_hilbert k q I L hI hL hHomI hHomL d i hH
end NSP14.Tests.StableBinomialWeights
