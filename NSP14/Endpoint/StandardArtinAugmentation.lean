module
public import NSP14.Endpoint.StandardArtinFinite
public import NSP14.Homological.RegularAugmentationBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) (hproper : I≠⊤)
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))

noncomputable def artinAugmentation : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (augmentation k σ) (by
    intro f hf
    rw [show augmentation k σ f=f.coeff 0 from MvPolynomial.aeval_zero' f]
    exact homogeneous_ideal_constant k σ I hproper hI f hf)

omit [Fintype σ] [LinearOrder σ] in
theorem artinAugmentation_comp : (artinAugmentation k σ I hproper hI).comp (Ideal.Quotient.mkₐ k I)=augmentation k σ :=
  Ideal.Quotient.liftₐ_comp _ _ _

noncomputable def artinRegularIso : artinModule k σ I ≅
    polynomialRegularModule k σ (MvPolynomial σ k ⧸ I) (Ideal.Quotient.mkₐ k I) :=
  LinearEquiv.toModuleIso
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

instance artinCoefficientFinite [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    Module.Finite k (coefficientModule k σ (artinModule k σ I)) :=
  Module.Finite.equiv (coefficientOriginalEquiv k σ _).symm

instance artinPolynomialFinite [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    Module.Finite (VariableRing k σ) (artinModule k σ I) := polynomialFinite_of_coefficientFinite _

omit [LinearOrder σ] in
include hproper hI in
theorem artin_betti_zero [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    totalBetti k σ (artinModule k σ I) 0=1 := by
  have h := regularAugmented_totalBetti_zero k σ (MvPolynomial σ k ⧸ I) (Ideal.Quotient.mkₐ k I)
    (artinAugmentation k σ I hproper hI) (Ideal.Quotient.mkₐ_surjective k I)
    (artinAugmentation_comp k σ I hproper hI)
  rw [totalBetti_iso k σ (artinRegularIso k σ I)]
  exact h
end NSP14.Endpoint
