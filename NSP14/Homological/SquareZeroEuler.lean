module
public import NSP14.Homological.KoszulRankOneAction
public import NSP14.Homological.KoszulIndependentImages
@[expose] public section
open CategoryTheory
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ))
  [Module.Finite k (coefficientModule k σ M)]
  (u₀ : coefficientModule k σ M) (ℓ : coefficientModule k σ M →ₗ[k] k)
  (hact : ∀ v (a : coefficientModule k σ M),
    (MvPolynomial.X v : VariableRing k σ) • a=ℓ a • ((MvPolynomial.X v : VariableRing k σ) • u₀))
  (ρ : σ → coefficientModule k σ M →ₗ[k] k)
  (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)

include hact hρ in
theorem koszulBoundaryRank_rankOne_eq (j : ℕ) :
    koszulBoundaryRank k σ M (j+1)=(Fintype.card σ).choose (j+1) := by
  apply le_antisymm
  · have h := coefficient_d_rankOne_rank_le k σ M u₀ ℓ hact (variableList k σ) j
    rw [coefficientKoszulListFunctor_full,coefficientKoszulFunctor_obj] at h
    simpa only [variableList_length,koszulBoundaryRank,chainBoundaryRank_succ] using h
  · exact koszulBoundaryRank_ge_choose k σ M u₀ ρ hρ j

include hact hρ in
/-- Exact Euler rows of a finite square-zero first-order module. The
variable images are independent, and every variable acts through the
actual constant projection. The proof computes the real boundary rank
with a signed-unit minor; it works in characteristic two. -/
theorem squareZero_bettiEuler [Module.Finite (VariableRing k σ) M]
    (hr : 1 ≤ Fintype.card σ) (j : ℕ) :
    bettiEuler k σ M j=((Fintype.card σ-1).choose j : ℤ)*
      Module.finrank k (coefficientModule k σ M)-((Fintype.card σ).choose (j+1) : ℤ) := by
  rw [finite_koszul_bettiEuler k σ M hr,koszulBoundaryRank_rankOne_eq k σ M u₀ ℓ hact ρ hρ]
end NSP14.Homological
