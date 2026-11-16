module
public import NSP14.Homological.PolynomialEquivBetti
public import NSP14.Homological.LinearVariables
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k τ σ : Type u) [Field k] [Fintype τ] [Fintype σ]

omit [Fintype τ] in
theorem augmentation_linearPolynomial (v : σ → k) : augmentation k σ (linearPolynomial k σ v)=0 := by
  rw [linearPolynomial_apply]
  change (augmentation k σ).toLinearMap (∑ i,v i • MvPolynomial.X i)=0
  simp only [map_sum,map_smul,AlgHom.toLinearMap_apply,augmentation_X,smul_zero,Finset.sum_const_zero]

theorem polynomialLinearEquiv_augmentation (e : (τ → k) ≃ₗ[k] (σ → k)) :
    (augmentation k σ).comp (polynomialLinearEquiv e).toAlgHom=augmentation k τ := by
  apply MvPolynomial.algHom_ext
  intro i
  change augmentation k σ (linearSubstitution e.toLinearMap (MvPolynomial.X i))=augmentation k τ (MvPolynomial.X i)
  rw [linearSubstitution_X,augmentation_linearPolynomial,augmentation_X]

theorem polynomialLinearEquiv_totalBetti (e : (τ → k) ≃ₗ[k] (σ → k))
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    letI := polynomialEquivRestricted_finite k τ σ (polynomialLinearEquiv e) M
    totalBetti k τ ((ModuleCat.restrictScalars (polynomialLinearEquiv e).toRingEquiv.toRingHom).obj M) i=
      totalBetti k σ M i :=
  polynomialEquiv_totalBetti k τ σ (polynomialLinearEquiv e) (polynomialLinearEquiv_augmentation k τ σ e) M i
end NSP14.Homological
