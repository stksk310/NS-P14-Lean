module
public import NSP14
@[expose] public section
open CategoryTheory NSP14.Homological
namespace FiniteKoszulEulerAcceptance
variable (k σ : Type) [Field k] [Fintype σ]
variable (M : ModuleCat (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
  [Module.Finite k (coefficientModule k σ M)]
theorem finite_length_euler (hr : 1 ≤ Fintype.card σ) (j : ℕ) :
    bettiEuler k σ M j = ((Fintype.card σ-1).choose j : ℤ)*
      Module.finrank k (coefficientModule k σ M) - (koszulBoundaryRank k σ M (j+1) : ℤ) :=
  finite_koszul_bettiEuler k σ M hr j
theorem finite_top (hr : 1 ≤ Fintype.card σ) :
    bettiEuler k σ M (Fintype.card σ)=0 := finite_koszul_bettiEuler_top k σ M hr
theorem zero_case [Subsingleton M] (j : ℕ) : bettiEuler k σ M j=0 :=
  bettiEuler_eq_zero_of_subsingleton k σ M j
end FiniteKoszulEulerAcceptance
