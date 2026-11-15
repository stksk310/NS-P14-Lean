module
public import NSP14.Homological.KoszulExteriorGrading
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
namespace NSP14.Tests.KoszulExteriorGrading
theorem actual_coefficient_degree (k σ : Type) [Field k] [Fintype σ]
    (M : ModuleCat (VariableRing k σ)) (G : GradedPolynomialModule k σ M) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a∈G.degreeSpace (deg a)) (i : ℕ) (a : J) (w : ⋀[k]^i (σ → k)) :
    (koszulExteriorTensorEquiv k σ M b i).symm (b a ⊗ₜ[k] w)∈
      (koszulChainGrading k σ M G (variableList k σ) i).degreeSpace (deg a) :=
  koszulExteriorTensorEquiv_symm_basis_homogeneous k σ M G b deg hb i a w
end NSP14.Tests.KoszulExteriorGrading
