module
public import NSP14.Homological.PolynomialBaseChangeModule
public import NSP14.Homological.PolynomialModules
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]

noncomputable def originalCoefficientEquiv (M : Type u) [AddCommGroup M] [Module k M]
    [Module (VariableRing k σ) M] [IsScalarTower k (VariableRing k σ) M] :
    coefficientModule k σ (ModuleCat.of (VariableRing k σ) M) ≃ₗ[k] M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    change (algebraMap k (VariableRing k σ) r) • (show M from a)=r • (show M from a)
    exact algebraMap_smul (VariableRing k σ) r (show M from a)

variable {k σ} {τ : Type u}
noncomputable def restrictPolynomial (φ : VariableRing k τ →ₐ[k] VariableRing k σ)
    (M : ModuleCat.{u} (VariableRing k σ)) : ModuleCat.{u} (VariableRing k τ) :=
  (ModuleCat.restrictScalars φ.toRingHom).obj M

noncomputable def restrictedCoefficientEquiv (φ : VariableRing k τ →ₐ[k] VariableRing k σ)
    (M : ModuleCat.{u} (VariableRing k σ)) :
    coefficientModule k τ (restrictPolynomial φ M) ≃ₗ[k] coefficientModule k σ M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    change φ (algebraMap k (VariableRing k τ) r) • (show M from a) =
      (algebraMap k (VariableRing k σ) r) • (show M from a)
    rw [φ.commutes]

noncomputable instance restrictedCoefficientFinite (φ : VariableRing k τ →ₐ[k] VariableRing k σ)
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite k (coefficientModule k σ M)] :
    Module.Finite k (coefficientModule k τ (restrictPolynomial φ M)) :=
  Module.Finite.equiv (restrictedCoefficientEquiv φ M).symm

theorem polynomialFinite_of_coefficientFinite (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite k (coefficientModule k σ M)] : Module.Finite (VariableRing k σ) M := by
  exact Module.Finite.of_restrictScalars_finite k (VariableRing k σ) (coefficientModule k σ M)

theorem restrictPolynomial_finite (φ : VariableRing k τ →ₐ[k] VariableRing k σ)
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite k (coefficientModule k σ M)] :
    Module.Finite (VariableRing k τ) (restrictPolynomial φ M) :=
  polynomialFinite_of_coefficientFinite (k:=k) (σ:=τ) _
end NSP14.Homological
