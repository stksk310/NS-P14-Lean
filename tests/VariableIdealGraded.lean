module
public import NSP14.Endpoint.VariableIdealGraded
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.VariableIdealGraded
theorem actual_coordinate_graded (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
    (xs : List σ) (hx : xs.Nodup)
    (hI : (Homological.variablesIdeal k σ xs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (i : ℕ) (t : ℤ) :
    Homological.gradedBetti k σ (Endpoint.artinModule k σ (Homological.variablesIdeal k σ xs))
      (Endpoint.artinGrading k σ (Homological.variablesIdeal k σ xs) hI) i t=
      if (i:ℤ)=t then xs.length.choose i else 0 :=
  Endpoint.variable_ideal_gradedBetti k σ xs hx hI i t
end NSP14.Tests.VariableIdealGraded
