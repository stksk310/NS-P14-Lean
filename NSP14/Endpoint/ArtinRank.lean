module
public import NSP14.Endpoint.CoreLowDegrees
public import NSP14.Endpoint.CoreAugmentation
public import NSP14.Homological.KoszulIndependentImages
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

theorem positive_artin_rank_sum (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)]
    (u₀ : coefficientModule k σ M) (ρ : σ → coefficientModule k σ M →ₗ[k] k)
    (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)
    (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k σ M i+(Fintype.card σ+1).choose (i+1)≤
      Module.finrank k (coefficientModule k σ M)*(Fintype.card σ).choose i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  have h := koszul_betti_chain_rank k σ M (j+1)
  have h1 := koszulBoundaryRank_ge_choose k σ M u₀ ρ hρ j
  have h2 := koszulBoundaryRank_ge_choose k σ M u₀ ρ hρ (j+1)
  have hp := Nat.choose_succ_succ (Fintype.card σ) (j+1)
  change (Fintype.card σ+1).choose (j+1+1)=
    (Fintype.card σ).choose (j+1)+(Fintype.card σ).choose (j+1+1) at hp
  change totalBetti k σ M (j+1)+(Fintype.card σ+1).choose (j+1+1)≤
    Module.finrank k (coefficientModule k σ M)*(Fintype.card σ).choose (j+1)
  omega
theorem positive_artin_rank_bound (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)]
    (u₀ : coefficientModule k σ M) (ρ : σ → coefficientModule k σ M →ₗ[k] k)
    (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)
    (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k σ M i≤Module.finrank k (coefficientModule k σ M)*(Fintype.card σ).choose i-
      (Fintype.card σ+1).choose (i+1) :=
  Nat.le_sub_of_add_le (positive_artin_rank_sum k σ M u₀ ρ hρ i hi)
end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def QCoreUnit : coefficientModule k D.a (D.QCoreModule k) := (D.QCoreCoefficientEquiv k).symm 1
noncomputable def QCoreLinearFunctional (b : D.a) : coefficientModule k D.a (D.QCoreModule k) →ₗ[k] k :=
  (Finsupp.lapply (D.internalMinimalIndex b)).comp (D.QCoreModuleCoordinates k).toLinearMap

theorem internalToQCore_X_basis (b : D.a) : D.internalToQCore k (MvPolynomial.X b)=
    D.QCoreBasis k (D.internalMinimalIndex b) := by
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X b))=_
  rw [D.internalToCore_X,D.QCoreBasis_apply]
  rfl

theorem QCore_linear_functionals (v w : D.a) :
    D.QCoreLinearFunctional k v ((MvPolynomial.X w : D.InternalRing k) • D.QCoreUnit k)=
      if v=w then 1 else 0 := by
  change D.QCoreCoordinates k (D.internalToQCore k (MvPolynomial.X w)*1) (D.internalMinimalIndex v)=_
  rw [mul_one,D.internalToQCore_X_basis,D.QCoreCoordinates_basis,Finsupp.single_apply]
  have he : D.internalMinimalIndex w=D.internalMinimalIndex v ↔ v=w :=
    ⟨fun h => (D.internalMinimalIndex_injective h).symm,fun h => by rw [h]⟩
  simp only [he]

theorem QCore_positive_betti_add (i : ℕ) (hi : 1 ≤ i) : totalBetti k D.a (D.QCoreModule k) i+
    (D.q+1).choose (i+1)≤D.coreP k*D.q.choose i := by
  have h := NSP14.Endpoint.positive_artin_rank_sum k D.a (D.QCoreModule k)
    (D.QCoreUnit k) (D.QCoreLinearFunctional k) (by
      intro v w
      by_cases h : v=w <;> simpa only [h,ite_true,ite_false] using D.QCore_linear_functionals k v w) i hi
  rw [(D.QCoreCoefficientEquiv k).finrank_eq,Fintype.card_coe] at h
  exact h

/-- Actual arbitrary-characteristic minor bound, including char 2,
for the genuine standard Artin quotient QC. -/
theorem QCore_positive_betti_bound (i : ℕ) (hi : 1 ≤ i) : totalBetti k D.a (D.QCoreModule k) i≤
    D.coreP k*D.q.choose i-(D.q+1).choose (i+1) := by
  have h := NSP14.Endpoint.positive_artin_rank_bound k D.a (D.QCoreModule k)
    (D.QCoreUnit k) (D.QCoreLinearFunctional k) (by
      intro v w
      by_cases h : v=w <;> simpa only [h,ite_true,ite_false] using D.QCore_linear_functionals k v w) i hi
  rw [(D.QCoreCoefficientEquiv k).finrank_eq,Fintype.card_coe] at h
  exact h
end NSP14.Endpoint.Data
