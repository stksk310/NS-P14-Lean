module
public import NSP14.Endpoint.StandardArtinGeneration
public import NSP14.Endpoint.StandardArtinQuadratic
public import NSP14.Endpoint.ArtinWeights
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]
  (hproper : I≠⊤) (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
  (hlinear : ∀ f∈I, f.IsHomogeneous 1 → f=0)

include hproper hI hlinear in
theorem artinHilbert_tail_sum : Module.finrank k (MvPolynomial σ k ⧸ I)=
    1+∑ n∈Finset.range (artinLimit k σ I),artinHilbert k σ I hI (n+1) := by
  have h := artinHilbert_sum k σ I hI
  rw [Finset.sum_range_succ',artinHilbert_zero k σ I hI hproper hlinear] at h
  omega

include hproper hI hlinear in
theorem artin_first_harmonic (hq : 2≤Fintype.card σ) :
    (totalBetti k σ (artinModule k σ I) 1 : ℚ)≤
      weightedFirst (Fintype.card σ) (artinLimit k σ I) (artinHilbert k σ I hI) := by
  let : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  exact cyclic_first_harmonic k σ (artinModule k σ I) (artinGrading k σ I hI)
    (artinLimit k σ I) (artin_generated_zero k σ I hproper hI hlinear)
    (by intro n hn;simpa only [zero_add] using artinGrading_above k σ I hI n hn)
    (artinHilbert_zero k σ I hI hproper hlinear) (artin_betti_zero k σ I hproper hI)

include hproper hI hlinear in
theorem artin_first_third (hq : 2≤Fintype.card σ) :
    (totalBetti k σ (artinModule k σ I) 1 : ℚ)≤
      ((Fintype.card σ:ℚ)-1)*Module.finrank k (MvPolynomial σ k ⧸ I)/3+
        ((Fintype.card σ:ℚ)+1)*(Fintype.card σ+2)/6 :=
  (artin_first_harmonic k σ I hproper hI hlinear hq).trans
    (weightedFirst_third _ _ _ _ hq (by exact (by decide : 1≤2).trans (le_max_left _ _))
      (artinHilbert_one k σ I hI hproper hlinear) (artinHilbert_tail_sum k σ I hproper hI hlinear))

include hproper hI hlinear in
theorem artin_first_fourth (hq : 2≤Fintype.card σ) :
    (totalBetti k σ (artinModule k σ I) 1 : ℚ)≤
      ((Fintype.card σ:ℚ)-1)*Module.finrank k (MvPolynomial σ k ⧸ I)/4+
        ((Fintype.card σ:ℚ)+1)^2/4+((Fintype.card σ:ℚ)-1)*artinHilbert k σ I hI 2/12 :=
  (artin_first_harmonic k σ I hproper hI hlinear hq).trans
    (weightedFirst_fourth _ _ _ _ hq (le_max_left _ _)
      (artinHilbert_one k σ I hI hproper hlinear) (artinHilbert_tail_sum k σ I hproper hI hlinear))

include hproper hI hlinear in
theorem artin_first_signed (hq : 2≤Fintype.card σ) :
    (totalBetti k σ (artinModule k σ I) 1 : ℚ)-(Module.finrank k (MvPolynomial σ k ⧸ I):ℚ)≤
      (Fintype.card σ:ℚ)-1+∑ n∈Finset.range (artinLimit k σ I),
        ((Fintype.card σ:ℚ)-(n+1)-2)*(artinHilbert k σ I hI (n+1):ℚ)/(n+2) := by
  have h := sub_le_sub_right (artin_first_harmonic k σ I hproper hI hlinear hq)
    (Module.finrank k (MvPolynomial σ k ⧸ I):ℚ)
  rw [weightedFirst_signed _ _ _ _ (by omega) (artinHilbert_tail_sum k σ I hproper hI hlinear)] at h
  exact h

include hproper hI hlinear in
theorem artin_positive_rows (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k σ (artinModule k σ I) i≤Module.finrank k (MvPolynomial σ k ⧸ I)*(Fintype.card σ).choose i-
      (Fintype.card σ+1).choose (i+1) := by
  have h := positive_artin_rank_bound k σ (artinModule k σ I) (artinUnit k σ I)
    (artinLinearFunctional k σ I hproper hI hlinear)
    (by
      intro v w
      by_cases h : v=w <;> simpa only [h,ite_true,ite_false] using artin_linear_functionals k σ I hproper hI hlinear v w) i hi
  rw [(coefficientOriginalEquiv k σ (MvPolynomial σ k ⧸ I)).finrank_eq] at h
  exact h

include hproper hI hlinear in
theorem artin_first_five (hq : Fintype.card σ=5) :
    (totalBetti k σ (artinModule k σ I) 1 : ℚ)-(Module.finrank k (MvPolynomial σ k ⧸ I):ℚ)≤14 := by
  have h := sub_le_sub_right (artin_first_harmonic k σ I hproper hI hlinear (by omega))
    (Module.finrank k (MvPolynomial σ k ⧸ I):ℚ)
  rw [hq] at h
  have h1 := artinHilbert_one k σ I hI hproper hlinear
  have h2 := artinHilbert_two_bound σ k I hI
  rw [hq] at h1 h2
  exact h.trans (weightedFirst_five _ _ _ (le_max_left _ _) h1 h2
    (artinHilbert_tail_sum k σ I hproper hI hlinear))
end NSP14.Endpoint
