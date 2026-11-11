module
public import NSP14.Endpoint.StandardHomogeneous
public import NSP14.Endpoint.BasisGrading
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k))

noncomputable abbrev artinModule := ModuleCat.of (VariableRing k σ) (MvPolynomial σ k ⧸ I)

noncomputable def artinCoordinates : coefficientModule k σ (artinModule k σ I) ≃ₗ[k]
    (StandardExponent MonomialOrder.degLex I →₀ k) :=
  (coefficientOriginalEquiv k σ _).trans
    ((standardMonomialQuotientEquiv MonomialOrder.degLex I).symm.trans
      (normalCoordinates MonomialOrder.degLex I))

theorem artinCoordinates_single (p : StandardExponent MonomialOrder.degLex I) :
    (artinCoordinates k σ I).symm (Finsupp.single p 1)=
      (show artinModule k σ I from Ideal.Quotient.mk I (MvPolynomial.monomial p.val 1)) := by
  exact standardMonomialBasis_apply MonomialOrder.degLex I p

theorem normal_quotient_difference (f : MvPolynomial σ k) :
    f-((standardMonomialQuotientEquiv MonomialOrder.degLex I).symm (Ideal.Quotient.mk I f)).val∈I := by
  apply Ideal.Quotient.eq.mp
  exact ((standardMonomialQuotientEquiv MonomialOrder.degLex I).apply_symm_apply (Ideal.Quotient.mk I f)).symm

theorem artin_variable_homogeneous
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : σ) (p j : StandardExponent MonomialOrder.degLex I)
    (hj : (j.val.degree : ℤ)≠(p.val.degree : ℤ)+1) :
    artinCoordinates k σ I ((MvPolynomial.X x : VariableRing k σ) •
      (artinCoordinates k σ I).symm (Finsupp.single p 1)) j=0 := by
  rw [artinCoordinates_single]
  let f : MvPolynomial σ k := MvPolynomial.X x*MvPolynomial.monomial p.val 1
  let r := (standardMonomialQuotientEquiv MonomialOrder.degLex I).symm (Ideal.Quotient.mk I f)
  have hf : f.IsHomogeneous (p.val.degree+1) := by
    simpa only [Nat.add_comm] using
      (MvPolynomial.isHomogeneous_X (R:=k) x).mul (MvPolynomial.isHomogeneous_monomial (1:k) rfl)
  have hr := normal_homogeneous k σ I hI (p.val.degree+1) f hf r
    (normal_quotient_difference k σ I f)
  change r.val.coeff j.val=0
  by_contra hc
  have hd : j.val.degree=p.val.degree+1 := by
    rw [MvPolynomial.IsHomogeneous,MvPolynomial.IsWeightedHomogeneous] at hr
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one j.val).trans (hr hc)
  exact hj (by exact_mod_cast hd)

/-- The grading belongs to the actual quotient by the given homogeneous
ideal. Its basis uses the actual initial ideal of all elements of I. -/
noncomputable def artinGrading
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    GradedPolynomialModule k σ (artinModule k σ I) :=
  basisGrading k σ _ (artinModule k σ I) (artinCoordinates k σ I)
    (fun p => (p.val.degree : ℤ)) (artin_variable_homogeneous k σ I hI)
end NSP14.Endpoint
