module
public import NSP14.Homological.IdealAdjoiningKoszul
@[expose] public section
open HomologicalComplex
namespace NSP14.Tests.KoszulVariableFactor
theorem actual_variable_factor_zero (k σ : Type) [Field k] [Fintype σ]
    (M N : ModuleCat (Homological.VariableRing k σ)) (f : M ⟶ N) (x : σ) (i : ℕ) :
    homologyMap ((Homological.coefficientKoszulFunctor k σ).map
      ((MvPolynomial.X x : Homological.VariableRing k σ) • f)) i=0 :=
  Homological.coefficientKoszul_variable_smul_zero k σ f x i
end NSP14.Tests.KoszulVariableFactor
