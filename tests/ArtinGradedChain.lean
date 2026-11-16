module
public import NSP14.Endpoint.ArtinGradedChain
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.ArtinGradedChain
theorem actual_chain_finite (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (t : ℤ) (i : ℕ) :
    Module.Finite k (Homological.gradedKoszulSpace k (Fin q) (Endpoint.artinModule k (Fin q) I)
      (Endpoint.artinGrading k (Fin q) I hI) (Homological.variableList k (Fin q)) t i) :=
  Endpoint.artinGradedChain_finite k q I hI t i
end NSP14.Tests.ArtinGradedChain
