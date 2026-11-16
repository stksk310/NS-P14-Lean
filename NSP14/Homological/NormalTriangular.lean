module
public import NSP14.Homological.StandardMonomials
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Homological
variable (k : Type) {σ : Type} [Field k] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))

/-- The unique actual standard-supported representative cannot have a
larger leading term than its original polynomial. -/
theorem normal_representative_degree_le (f : MvPolynomial σ k)
    (r : normalSpace m I) (hfr : f-r.val ∈ I) :
    m.toSyn (m.degree r.val) ≤ m.toSyn (m.degree f) := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hr0 : r.val ≠ 0 := by
    intro he
    rw [he,m.degree_zero,map_zero] at hlt
    exact not_lt_of_ge bot_le hlt
  have hs : m.degree r.val ∈ StandardExponent m I :=
    (Finsupp.mem_supported k _).mp r.property (m.degree_mem_support hr0)
  have hp0 : f-r.val ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    rw [he'] at hlt
    exact lt_irrefl _ hlt
  have hd : m.degree (f-r.val)=m.degree r.val := by
    rw [←neg_sub r.val f,m.degree_neg,m.degree_sub_of_lt hlt]
  exact hs (f-r.val) hfr hp0 (by rw [hd])

noncomputable def actualNormalForm (f : MvPolynomial σ k) : MvPolynomial σ k :=
  ((standardMonomialQuotientEquiv m I).symm (Ideal.Quotient.mk I f)).val

theorem actualNormalForm_difference (f : MvPolynomial σ k) : f-actualNormalForm k m I f ∈ I := by
  apply Ideal.Quotient.eq.mp
  exact ((standardMonomialQuotientEquiv m I).apply_symm_apply (Ideal.Quotient.mk I f)).symm

theorem actualNormalForm_of_mem (f : MvPolynomial σ k) (hf : f ∈ I) : actualNormalForm k m I f=0 := by
  unfold actualNormalForm
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf,map_zero]
  rfl

theorem actualNormalForm_degree_le (f : MvPolynomial σ k) :
    m.toSyn (m.degree (actualNormalForm k m I f)) ≤ m.toSyn (m.degree f) :=
  normal_representative_degree_le k m I f _ (actualNormalForm_difference k m I f)

theorem actualNormalForm_coeff_zero_above (f : MvPolynomial σ k) (v : σ →₀ ℕ)
    (hv : m.toSyn (m.degree f) < m.toSyn v) : (actualNormalForm k m I f).coeff v=0 :=
  m.coeff_eq_zero_of_lt ((actualNormalForm_degree_le k m I f).trans_lt hv)

theorem actualNormalForm_normal (r : normalSpace m I) : actualNormalForm k m I r.val=r.val := by
  change ((standardMonomialQuotientEquiv m I).symm ((standardMonomialQuotientEquiv m I) r)).val=r.val
  rw [LinearEquiv.symm_apply_apply]

theorem actualNormalForm_monomial (v : σ →₀ ℕ) (hv : v ∈ StandardExponent m I) :
    actualNormalForm k m I (MvPolynomial.monomial v 1)=MvPolynomial.monomial v 1 := by
  have hm : MvPolynomial.monomial v (1:k) ∈ normalSpace m I := by
    change (MvPolynomial.monomial v (1:k)).coeff ∈ Finsupp.supported k k (StandardExponent m I)
    rw [Finsupp.mem_supported]
    intro d hd
    change d ∈ (MvPolynomial.monomial v (1:k)).support at hd
    have he : d=v := by simpa only [MvPolynomial.support_monomial,ite_eq_right one_ne_zero,
      Finset.mem_singleton] using hd
    simpa only [he] using hv
  exact actualNormalForm_normal k m I ⟨_,hm⟩

/-- Reducing a nonstandard monomial produces only strictly smaller terms. -/
theorem actualNormalForm_coeff_zero_ge_nonstandard (v : σ →₀ ℕ) (hv : v ∉ StandardExponent m I)
    (w : σ →₀ ℕ) (hw : m.toSyn v ≤ m.toSyn w) :
    (actualNormalForm k m I (MvPolynomial.monomial v 1)).coeff w=0 := by
  by_cases he : v=w
  · subst w
    by_contra hn
    have hs := ((standardMonomialQuotientEquiv m I).symm
      (Ideal.Quotient.mk I (MvPolynomial.monomial v (1:k)))).property
    exact hv ((Finsupp.mem_supported k _).mp hs (MvPolynomial.mem_support_iff.mpr hn))
  · apply actualNormalForm_coeff_zero_above k m I
    have hlt : m.toSyn v < m.toSyn w := lt_of_le_of_ne hw (fun h => he (m.toSyn.injective h))
    simpa only [m.degree_monomial,ite_eq_right one_ne_zero] using hlt
end NSP14.Homological
