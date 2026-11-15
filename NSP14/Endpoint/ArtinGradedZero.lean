module
public import NSP14.Endpoint.ArtinShift
public import NSP14.Endpoint.StandardArtinAugmentation
public import NSP14.Homological.GradedKoszulPieces
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]

omit [LinearOrder σ] in
theorem artin_totalBetti_zero_general (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    totalBetti k σ (artinModule k σ I) 0=1 := by
  let := regularPresentation_finite k σ (MvPolynomial σ k ⧸ I) (Ideal.Quotient.mkₐ k I)
    (Ideal.Quotient.mkₐ_surjective k I)
  have h := regularAugmented_totalBetti_zero k σ (MvPolynomial σ k ⧸ I) (Ideal.Quotient.mkₐ k I)
    (artinAugmentation k σ I hproper hI) (Ideal.Quotient.mkₐ_surjective k I)
    (artinAugmentation_comp k σ I hproper hI)
  rw [totalBetti_iso k σ (artinRegularIso k σ I)]
  exact h

theorem proper_zero_standard (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (0 : σ →₀ ℕ) ∈ StandardExponent MonomialOrder.degLex I := by
  intro p hp hp0 hle
  have he : MonomialOrder.degLex.degree p=0 := le_antisymm hle (by intro i; exact Nat.zero_le _)
  have hn := MonomialOrder.degLex.coeff_degree_ne_zero_iff.mpr hp0
  apply hn
  rw [he]
  exact homogeneous_ideal_constant k σ I hproper hI p hp

noncomputable def properArtinZeroIndex (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    StandardExponent MonomialOrder.degLex I := ⟨0,proper_zero_standard k σ I hproper hI⟩

noncomputable def properArtinZeroEquiv (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨properArtinZeroIndex k σ I hproper hI,by simp [properArtinZeroIndex]⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    have hn : p.val.val.degree=0 := by exact_mod_cast p.property
    exact ((Finsupp.degree_eq_zero_iff p.val.val).mp hn).symm
  right_inv _ := rfl

theorem artinGrading_zero_dim_general (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    Module.finrank k ((artinGrading k σ I hI).piece 0)=1 := by
  let A := {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=0}
  let : Finite A := Finite.of_equiv PUnit (properArtinZeroEquiv k σ I hproper hI).symm
  let : Fintype A := Fintype.ofFinite A
  change Module.finrank k (A →₀ k)=1
  rw [Module.finrank_finsupp_self,←Nat.card_eq_fintype_card,
    Nat.card_congr (properArtinZeroEquiv k σ I hproper hI)]
  simp

theorem artinGrading_negative (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (q : ℤ) (hq : q < 0) :
    Subsingleton ((artinGrading k σ I hI).piece q) := by
  let A := {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=q}
  let : IsEmpty A := ⟨fun p => by
    have hp := p.property
    have hn := Int.natCast_nonneg p.val.val.degree
    omega⟩
  change Subsingleton (A →₀ k)
  infer_instance

theorem artin_gradedBetti_zero_diagonal (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    gradedBetti k σ (artinModule k σ I) (artinGrading k σ I hI) 0 0=1 := by
  let G := artinGrading k σ I hI
  let C := gradedKoszulComplex k σ (artinModule k σ I) G (variableList k σ) 0
  let : Subsingleton (C.X 1) := by
    apply gradedKoszulSpace_subsingleton k σ (artinModule k σ I) G (variableList k σ) 0 1
    exact artinGrading_negative k σ I hI _ (by norm_num)
  have hin : (C.sc 0).f=0 := by
    have hz : C.d 1 0=0 := (ModuleCat.isZero_of_subsingleton (C.X 1)).eq_of_src _ _
    change C.dTo 0=0
    rw [C.dTo_eq (show (ComplexShape.down ℕ).Rel 1 0 from rfl),hz,comp_zero]
  have hout : (C.sc 0).g=0 := by
    change C.dFrom 0=0
    exact C.dFrom_eq_zero (by intro h; change (ComplexShape.down ℕ).next 0+1=0 at h; omega)
  let e : C.homology 0 ≅ C.X 0 := (ShortComplex.HomologyData.ofZeros (C.sc 0) hin hout).left.homologyIso
  have h := e.toLinearEquiv.finrank_eq
  change gradedBetti k σ (artinModule k σ I) G 0 0=
    Module.finrank k (gradedKoszulSpace k σ (artinModule k σ I) G (variableList k σ) 0 0) at h
  rw [h,gradedKoszulSpace_zero_finrank]
  exact artinGrading_zero_dim_general k σ I hproper hI

/-- The actual zeroth graded Tor of every proper homogeneous quotient,
without assuming the quotient or its chains finite over the field. -/
theorem artin_gradedBetti_zero (I : Ideal (MvPolynomial σ k)) (hproper : I ≠ ⊤)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (t : ℤ) :
    gradedBetti k σ (artinModule k σ I) (artinGrading k σ I hI) 0 t=
      if (0:ℤ)=t then 1 else 0 := by
  by_cases h0 : (0:ℤ)=t
  · subst t
    rw [ite_eq_left rfl]
    exact artin_gradedBetti_zero_diagonal k σ I hproper hI
  rw [ite_eq_right h0]
  let G := artinGrading k σ I hI
  change gradedBetti k σ (artinModule k σ I) G 0 t=0
  have hd : gradedBetti k σ (artinModule k σ I) G 0 0=1 :=
    artin_gradedBetti_zero_diagonal k σ I hproper hI
  obtain ⟨s,hs,he⟩ := gradedBetti_total k σ (artinModule k σ I) G 0
  rw [artin_totalBetti_zero_general k σ I hproper hI] at he
  have hzmem : (0:ℤ) ∈ s := by
    by_contra hn
    let : Subsingleton ((gradedKoszulComplex k σ (artinModule k σ I) G (variableList k σ) 0).homology 0) :=
      ModuleCat.subsingleton_of_isZero (hs 0 hn)
    have hz : gradedBetti k σ (artinModule k σ I) G 0 0=0 := Module.finrank_zero_of_subsingleton
    omega
  by_cases ht : t ∈ s
  · have hsub : ({0,t} : Finset ℤ) ⊆ s := by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl|rfl
      · exact hzmem
      · exact ht
    have hl := Finset.sum_le_sum_of_subset hsub (f:=gradedBetti k σ (artinModule k σ I) G 0)
    have hpair : (∑ j ∈ ({0,t} : Finset ℤ),gradedBetti k σ (artinModule k σ I) G 0 j)=
        1+gradedBetti k σ (artinModule k σ I) G 0 t := by
      rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using h0),Finset.sum_singleton,hd]
    rw [hpair,←he] at hl
    omega
  · let : Subsingleton ((gradedKoszulComplex k σ (artinModule k σ I) G (variableList k σ) t).homology 0) :=
      ModuleCat.subsingleton_of_isZero (hs t ht)
    exact Module.finrank_zero_of_subsingleton

end NSP14.Endpoint
