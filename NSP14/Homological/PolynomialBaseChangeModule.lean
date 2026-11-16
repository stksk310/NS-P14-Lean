module

public import NSP14.Homological.KoszulCoefficientBaseChange
public import Mathlib.Algebra.Algebra.Tower

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

noncomputable def coefficientModule (M : ModuleCat.{u} (VariableRing k σ)) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj M

noncomputable instance coefficientModulePolynomial (M : ModuleCat.{u} (VariableRing k σ)) :
    Module (VariableRing k σ) (coefficientModule k σ M) := inferInstanceAs (Module (VariableRing k σ) M)

instance coefficientModuleTower (M : ModuleCat.{u} (VariableRing k σ)) :
    IsScalarTower k (VariableRing k σ) (coefficientModule k σ M) where
  smul_assoc c p m := by
    rw [Algebra.smul_def,mul_smul]
    rfl

/-- Base change of the actual P-action as an algebra representation on L⊗ₖM. -/
noncomputable def extendedPolynomialRepresentation (M : ModuleCat.{u} (VariableRing k σ)) :
    VariableRing L σ →ₐ[L] Module.End L (L ⊗[k] coefficientModule k σ M) :=
  ((AlgHom.liftEquiv k L (VariableRing k σ) _)
    ((Module.End.baseChangeHom k L (coefficientModule k σ M)).comp
      (Algebra.lsmul k k (coefficientModule k σ M)))).comp
        (polynomialFieldExtension k L σ).symm.toAlgHom

/-- The coefficient tensor product with its proved, actual changed-polynomial-ring action. -/
noncomputable def polynomialBaseChangeModule (M : ModuleCat.{u} (VariableRing k σ)) :
    ModuleCat.{u} (VariableRing L σ) := by
  let : Module (VariableRing L σ) (L ⊗[k] coefficientModule k σ M) :=
    Module.compHom _ (extendedPolynomialRepresentation k L σ M).toRingHom
  exact ModuleCat.of _ (L ⊗[k] coefficientModule k σ M)

/-- The coefficient restriction is the original L-tensor vector space, with its actual action. -/
noncomputable def polynomialBaseChangeCoefficientIso (M : ModuleCat.{u} (VariableRing k σ)) :
    coefficientModule L σ (polynomialBaseChangeModule k L σ M) ≅
      (fieldExtension k L).obj (coefficientModule k σ M) := by
  let e : coefficientModule L σ (polynomialBaseChangeModule k L σ M) ≃ₗ[L]
      (L ⊗[k] coefficientModule k σ M) :=
    { toFun := fun a => a
      invFun := fun a => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c a => by
        change extendedPolynomialRepresentation k L σ M (algebraMap L (VariableRing L σ) c)
          (show L ⊗[k] coefficientModule k σ M from a) = c • (show L ⊗[k] coefficientModule k σ M from a)
        rw [(extendedPolynomialRepresentation k L σ M).commutes]
        rfl }
  exact e.toModuleIso

theorem polynomialBaseChange_variable (M : ModuleCat.{u} (VariableRing k σ))
    (x : σ) (c : L) (m : coefficientModule k σ M) :
    extendedPolynomialRepresentation k L σ M (MvPolynomial.X x) (c ⊗ₜ[k] m) =
      c ⊗ₜ[k] ((MvPolynomial.X x : VariableRing k σ) • m) := by
  change ((AlgHom.liftEquiv k L (VariableRing k σ) _)
    ((Module.End.baseChangeHom k L (coefficientModule k σ M)).comp
      (Algebra.lsmul k k (coefficientModule k σ M))))
        ((MvPolynomial.algebraTensorAlgEquiv k L).symm (MvPolynomial.X x)) (c ⊗ₜ[k] m) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X,AlgHom.liftEquiv_tmul,one_smul]
  rfl

end NSP14.Homological
