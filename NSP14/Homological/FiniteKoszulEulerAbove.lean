module
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ))
  [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)]

theorem finite_koszul_bettiEuler_eq_zero_of_ge (hr : 1 ≤ Fintype.card σ)
    (j : ℕ) (hj : Fintype.card σ ≤ j) : bettiEuler k σ M j=0 := by
  rw [finite_koszul_bettiEuler k σ M hr,
    koszulBoundaryRank_eq_zero_of_gt k σ M _ (by omega),
    Nat.choose_eq_zero_of_lt (by omega : Fintype.card σ-1 < j)]
  simp
end NSP14.Homological
