module
public import NSP14.Homological.Presentation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable (k σ : Type*) [Field k] [Fintype σ]

noncomputable def linearPolynomial : (σ → k) →ₗ[k] MvPolynomial σ k :=
  Fintype.linearCombination k (fun i : σ => MvPolynomial.X i)

theorem linearPolynomial_apply (v : σ → k) :
    linearPolynomial k σ v=∑ i,v i • (MvPolynomial.X i : MvPolynomial σ k) := rfl

theorem linearPolynomial_single (i : σ) : linearPolynomial k σ (Pi.single i 1)=MvPolynomial.X i := by
  rw [linearPolynomial_apply]
  simp [Pi.single,Function.update_apply]

variable {k σ} {τ : Type*} [Fintype τ]

noncomputable def linearSubstitution (e : (τ → k) →ₗ[k] (σ → k)) :
    MvPolynomial τ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => linearPolynomial k σ (e (Pi.single i 1)))

omit [Fintype τ] in
theorem linearSubstitution_X (e : (τ → k) →ₗ[k] (σ → k)) (i : τ) :
    linearSubstitution e (MvPolynomial.X i)=linearPolynomial k σ (e (Pi.single i 1)) :=
  MvPolynomial.aeval_X _ i

theorem linearSubstitution_linear (e : (τ → k) →ₗ[k] (σ → k)) (v : τ → k) :
    linearSubstitution e (linearPolynomial k τ v)=linearPolynomial k σ (e v) := by
  have he : ∑ i : τ,v i • Pi.single i (1:k)=v := by
    funext j
    simp [Pi.single,Function.update_apply]
  rw [linearPolynomial_apply]
  change (linearSubstitution e).toLinearMap (∑ i,v i • MvPolynomial.X i)=_
  rw [map_sum]
  simp only [map_smul,AlgHom.toLinearMap_apply,linearSubstitution_X]
  have h := congrArg (fun w => linearPolynomial k σ (e w)) he
  simp only [map_sum,map_smul] at h
  exact h

/-- An actual invertible linear change gives an actual polynomial algebra
isomorphism, with inverse substitution explicitly proved on the variables. -/
noncomputable def polynomialLinearEquiv (e : (τ → k) ≃ₗ[k] (σ → k)) :
    MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (linearSubstitution e.toLinearMap) (linearSubstitution e.symm.toLinearMap)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change linearSubstitution e.toLinearMap (linearSubstitution e.symm.toLinearMap (MvPolynomial.X i))=MvPolynomial.X i
      rw [linearSubstitution_X,linearSubstitution_linear]
      change linearPolynomial k σ (e (e.symm (Pi.single i 1)))=_
      rw [LinearEquiv.apply_symm_apply,linearPolynomial_single])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change linearSubstitution e.symm.toLinearMap (linearSubstitution e.toLinearMap (MvPolynomial.X i))=MvPolynomial.X i
      rw [linearSubstitution_X,linearSubstitution_linear]
      change linearPolynomial k τ (e.symm (e (Pi.single i 1)))=_
      rw [LinearEquiv.symm_apply_apply,linearPolynomial_single])
end NSP14.Homological
