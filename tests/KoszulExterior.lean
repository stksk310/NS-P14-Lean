module
public import NSP14.Homological.KoszulExterior
public import NSP14.Homological.KoszulSlotGrading
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
namespace NSP14.Tests.KoszulExterior
theorem actual_chain_tensor_coordinates (k σ : Type) [Field k] [Fintype σ]
    (M : ModuleCat (VariableRing k σ)) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M)) (j : ℕ) :
    ∃ e : coefficientModule k σ ((koszulList k σ (variableList k σ) M).X j) ≃ₗ[k]
        coefficientModule k σ M ⊗[k] (⋀[k]^j (σ → k)),
      ∀ s a, e (coefficientSlotIn k σ M (variableList k σ) j s a)=
        a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k j s :=
  ⟨koszulExteriorTensorEquiv k σ M b j,koszulExteriorTensorEquiv_slot k σ M b j⟩

theorem actual_tensor_boundary (k σ : Type) [Field k] [Fintype σ]
    (M : ModuleCat (VariableRing k σ)) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M)) (j : ℕ)
    (a : coefficientModule k σ M) (w : ⋀[k]^(j+1) (σ → k)) :
    koszulExteriorTensorEquiv k σ M b j
      (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j
        ((koszulExteriorTensorEquiv k σ M b (j+1)).symm (a ⊗ₜ[k] w))) =
      ∑ x : σ, ((MvPolynomial.X x : VariableRing k σ) • a) ⊗ₜ[k]
        koszulExteriorContraction k σ j (LinearMap.proj x) w :=
  koszulExteriorBoundary_tmul k σ M b j a w
end NSP14.Tests.KoszulExterior
