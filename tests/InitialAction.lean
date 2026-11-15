module
public import NSP14.Endpoint.InitialAction
@[expose] public section
namespace NSP14.Tests.InitialAction
theorem actual_variable_triangular (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (x : Fin q)
    (p j : Homological.StandardExponent MonomialOrder.degLex I)
    (h : MonomialOrder.degLex.toSyn (p.val+Finsupp.single x 1) < MonomialOrder.degLex.toSyn j.val) :
    Endpoint.artinCoordinates k (Fin q) I ((MvPolynomial.X x : Homological.VariableRing k (Fin q)) •
      (Endpoint.artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=0 :=
  Endpoint.artin_variable_triangular k q I x p j h
end NSP14.Tests.InitialAction
