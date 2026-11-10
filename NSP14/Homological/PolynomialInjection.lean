module
public import NSP14.Homological.ExtendPrefix
@[expose] public section
open scoped Classical
namespace NSP14.Homological
variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

/-- A split injection of coefficient spaces gives a split injection of
polynomial rings. This is about formal variables, not their images in A. -/
theorem linearSubstitution_injective (e : (τ → k) →ₗ[k] (σ → k))
    (he : Function.Injective e) : Function.Injective (linearSubstitution e) := by
  obtain ⟨g,hg⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr he)
  have hc : (linearSubstitution g).comp (linearSubstitution e)=AlgHom.id k (MvPolynomial τ k) := by
    apply MvPolynomial.algHom_ext
    intro i
    change linearSubstitution g (linearSubstitution e (MvPolynomial.X i))=MvPolynomial.X i
    rw [linearSubstitution_X,linearSubstitution_linear]
    have hge := LinearMap.congr_fun hg (Pi.single i 1)
    change g (e (Pi.single i 1))=Pi.single i 1 at hge
    rw [hge,linearPolynomial_single]
  have hl : Function.LeftInverse (linearSubstitution g) (linearSubstitution e) :=
    fun p => DFunLike.congr_fun hc p
  exact hl.injective
end NSP14.Homological
