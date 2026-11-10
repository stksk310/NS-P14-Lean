module
public import NSP14.Homological.SquareZeroEuler
@[expose] public section
open CategoryTheory
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
  [Module.Finite k (coefficientModule k σ M)]
  (u₀ : coefficientModule k σ M) (ℓ : coefficientModule k σ M →ₗ[k] k)
  (hact : ∀ v (a : coefficientModule k σ M),
    (MvPolynomial.X v : VariableRing k σ) • a=ℓ a • ((MvPolynomial.X v : VariableRing k σ) • u₀))
  (ρ : σ → coefficientModule k σ M →ₗ[k] k)
  (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)
  (hlen : Module.finrank k (coefficientModule k σ M)=1+Fintype.card σ)

include hact hρ hlen in
theorem squareZero_totalBetti_zero : totalBetti k σ M 0=1 := by
  have h := koszul_betti_chain_rank k σ M 0
  have hz := chainBoundaryRank_zero k (coefficientKoszulComplex k σ M)
  change koszulBoundaryRank k σ M 0=0 at hz
  rw [hlen,koszulBoundaryRank_rankOne_eq k σ M u₀ ℓ hact ρ hρ 0,hz] at h
  simp only [Nat.zero_add,Nat.choose_zero_right,Nat.choose_one_right,Nat.mul_one,Nat.add_zero] at h
  omega

include hact hρ hlen in
/-- Exact ordinary Betti rows from real rank-one actions and independent
variable images, over every characteristic and any finite variable type. -/
theorem squareZero_ordinary_betti (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k σ M i=i*(Fintype.card σ+1).choose (i+1) := by
  cases i with
  | zero => omega
  | succ j =>
    have h := koszul_betti_chain_rank k σ M (j+1)
    rw [hlen,koszulBoundaryRank_rankOne_eq k σ M u₀ ℓ hact ρ hρ j,
      koszulBoundaryRank_rankOne_eq k σ M u₀ ℓ hact ρ hρ (j+1)] at h
    have hZ : (totalBetti k σ M (j+1) : ℤ)+
        ((Fintype.card σ).choose (j+1) : ℤ)+((Fintype.card σ).choose (j+2) : ℤ)=
          (1+Fintype.card σ : ℕ)*((Fintype.card σ).choose (j+1) : ℤ) := by exact_mod_cast h
    have hp := Nat.choose_succ_succ (Fintype.card σ) (j+1)
    change (Fintype.card σ+1).choose (j+2)=(Fintype.card σ).choose (j+1)+(Fintype.card σ).choose (j+2) at hp
    have hpZ : ((Fintype.card σ+1).choose (j+2) : ℤ)=
        ((Fintype.card σ).choose (j+1) : ℤ)+((Fintype.card σ).choose (j+2) : ℤ) := by exact_mod_cast hp
    have hm := Nat.add_one_mul_choose_eq (Fintype.card σ) (j+1)
    have hmZ : (Fintype.card σ+1 : ℕ)*((Fintype.card σ).choose (j+1) : ℤ)=
        ((Fintype.card σ+1).choose (j+2) : ℤ)*(j+2 : ℕ) := by exact_mod_cast hm
    have hβ : (totalBetti k σ M (j+1) : ℤ)=(j+1 : ℕ)*((Fintype.card σ+1).choose (j+2) : ℤ) := by
      push_cast at hZ hmZ ⊢
      nlinarith
    exact_mod_cast hβ
end NSP14.Homological
