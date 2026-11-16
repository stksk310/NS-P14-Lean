module
public import NSP14.Endpoint.InitialTransport
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
open NSP14.Homological
namespace NSP14.Tests.InitialTransport
theorem actual_initial_boundary_rank (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (t : ℤ) (i : ℕ) :
    Module.finrank k (Endpoint.initialBoundaryTransport k q I hI t i).range=
      Module.finrank k (gradedKoszulDifferential k (Fin q)
        (Endpoint.artinModule k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I))
        (Endpoint.artinGrading k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I)
          (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)) (variableList k (Fin q)) t i).range :=
  Endpoint.initialBoundaryTransport_rank k q I hI t i
end NSP14.Tests.InitialTransport
