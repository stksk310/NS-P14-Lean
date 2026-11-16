module
public import NSP14.Endpoint.InitialBoundary
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
open NSP14.Homological
namespace NSP14.Tests.InitialBoundary
theorem actual_boundary_triangular (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (t : ℤ) (i : ℕ)
    (s : Endpoint.ArtinChainIndex k q I t (i+1)) (r : Endpoint.ArtinChainIndex k q I t i)
    (hlt : MonomialOrder.degLex.toSyn (s.val.2.val+wedgeExponent
        (koszulSlotWedge (variableList k (Fin q)) (i+1) s.val.1)) <
      MonomialOrder.degLex.toSyn (r.val.2.val+wedgeExponent
        (koszulSlotWedge (variableList k (Fin q)) i r.val.1))) :
    (Endpoint.artinGradedChainBasis k q I hI t i).repr
      (gradedKoszulDifferential k (Fin q) (Endpoint.artinModule k (Fin q) I)
        (Endpoint.artinGrading k (Fin q) I hI) (variableList k (Fin q)) t i
        (Endpoint.artinGradedChainBasis k q I hI t (i+1) s)) r=0 :=
  Endpoint.artinGradedBoundary_triangular k q I hI t i s r hlt
end NSP14.Tests.InitialBoundary
