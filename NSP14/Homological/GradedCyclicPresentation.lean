module
public import NSP14.Homological.GradedMonomials
public import NSP14.Endpoint.ArtinGradedMaps
public import NSP14.Homological.RegularRestriction
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Homological
variable (k σ : Type) [Field k] (M : ModuleCat (VariableRing k σ))
    (G : GradedPolynomialModule k σ M) (m : coefficientModule k σ M)

def cyclicAction : MvPolynomial σ k →ₗ[k] coefficientModule k σ M :=
  (LinearMap.toSpanSingleton (VariableRing k σ) (coefficientModule k σ M) m).restrictScalars k

theorem cyclicAction_apply (p : MvPolynomial σ k) : cyclicAction k σ M m p=p • m := rfl

theorem cyclicAction_monomial_degree (hm : m∈G.degreeSpace 0) (α : σ →₀ ℕ) (c : k) :
    cyclicAction k σ M m (MvPolynomial.monomial α c)∈G.degreeSpace (α.degree:ℤ) := by
  have hh := graded_monomial_mem k σ M G α 0 m hm
  have hp : MvPolynomial.monomial α c=c • MvPolynomial.monomial α (1:k) := by
    rw [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  rw [hp,map_smul]
  apply (G.degreeSpace (α.degree:ℤ)).smul_mem c
  simpa only [zero_add,cyclicAction_apply] using hh

theorem gradedProjection_of_degree (n p : ℤ) (a : coefficientModule k σ M) (ha : a∈G.degreeSpace p) :
    gradedProjection k σ M G n a=if p=n then a else 0 := by
  obtain ⟨b,hb⟩ := ha
  rw [← hb,gradedProjection_inclusion]

theorem cyclicAction_component (hm : m∈G.degreeSpace 0) (p : MvPolynomial σ k) (n : ℕ) :
    gradedProjection k σ M G (n:ℤ) (cyclicAction k σ M m p)=
      cyclicAction k σ M m (MvPolynomial.homogeneousComponent n p) := by
  induction p using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,hf,hg]
  | monomial α c =>
    rw [gradedProjection_of_degree k σ M G (n:ℤ) (α.degree:ℤ) _ (cyclicAction_monomial_degree k σ M G m hm α c)]
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases he : α.degree=n
    · simp only [he,ite_true]
    · have hne : (α.degree:ℤ)≠(n:ℤ) := by exact_mod_cast he
      simp only [hne,ite_false,Ne.symm he,map_zero]
end NSP14.Homological

namespace NSP14.Endpoint
variable (k σ : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    (φ : MvPolynomial σ k →ₐ[k] A)
    (G : GradedPolynomialModule k σ (polynomialRegularModule k σ A φ))

theorem gradedUnit_kernel_homogeneous
    (hm : (regularRestrictionCoefficientEquiv k σ A φ).symm 1∈G.degreeSpace 0) :
    (RingHom.ker φ.toRingHom).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n p hp
  change φ ((MvPolynomial.decomposition.decompose' p n : MvPolynomial σ k))=0
  rw [MvPolynomial.decomposition.decompose'_apply]
  let m := (regularRestrictionCoefficientEquiv k σ A φ).symm 1
  have he (f : MvPolynomial σ k) :
      cyclicAction k σ (polynomialRegularModule k σ A φ) m f=
        (regularRestrictionCoefficientEquiv k σ A φ).symm (φ f) := by
    change φ f*1=φ f
    exact mul_one _
  have hh := cyclicAction_component k σ (polynomialRegularModule k σ A φ) G m hm p n
  rw [he,he] at hh
  have hp' : φ p=0 := hp
  rw [hp',map_zero,map_zero] at hh
  have hout := congrArg (regularRestrictionCoefficientEquiv k σ A φ) hh.symm
  simpa only [LinearEquiv.apply_symm_apply,map_zero] using hout


variable [Fintype σ] [LinearOrder σ]

def cyclicQuotientModuleIso (hφ : Function.Surjective φ) :
    artinModule k σ (RingHom.ker φ.toRingHom) ≅ polynomialRegularModule k σ A φ := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let f : artinModule k σ (RingHom.ker φ.toRingHom) →ₗ[VariableRing k σ] polynomialRegularModule k σ A φ := {
    toFun a := e a
    map_add' a b := e.map_add a b
    map_smul' p a := by
      change e (Ideal.Quotient.mk _ p*a)=φ p*e a
      rw [map_mul]
      rfl }
  exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective f e.bijective)

def cyclicQuotientBasis (hφ : Function.Surjective φ) :
    Module.Basis (StandardExponent MonomialOrder.degLex (RingHom.ker φ.toRingHom)) k
      (coefficientModule k σ (polynomialRegularModule k σ A φ)) :=
  (standardMonomialBasis MonomialOrder.degLex (RingHom.ker φ.toRingHom)).map
    ((Ideal.quotientKerAlgEquivOfSurjective hφ).toLinearEquiv.trans
      (regularRestrictionCoefficientEquiv k σ A φ).symm)

theorem cyclicQuotientBasis_homogeneous (hφ : Function.Surjective φ)
    (hm : (regularRestrictionCoefficientEquiv k σ A φ).symm 1∈G.degreeSpace 0)
    (p : StandardExponent MonomialOrder.degLex (RingHom.ker φ.toRingHom)) :
    cyclicQuotientBasis k σ A φ hφ p∈G.degreeSpace (p.val.degree:ℤ) := by
  rw [cyclicQuotientBasis,Module.Basis.map_apply,LinearEquiv.trans_apply,standardMonomialBasis_apply]
  change (regularRestrictionCoefficientEquiv k σ A φ).symm (φ (MvPolynomial.monomial p.val (1:k)))∈G.degreeSpace (p.val.degree:ℤ)
  have hh := cyclicAction_monomial_degree k σ (polynomialRegularModule k σ A φ) G
    ((regularRestrictionCoefficientEquiv k σ A φ).symm 1) hm p.val (1:k)
  have he : cyclicAction k σ (polynomialRegularModule k σ A φ)
      ((regularRestrictionCoefficientEquiv k σ A φ).symm 1) (MvPolynomial.monomial p.val (1:k))=
      (regularRestrictionCoefficientEquiv k σ A φ).symm (φ (MvPolynomial.monomial p.val (1:k))) := by
    change φ (MvPolynomial.monomial p.val (1:k))*1=_
    exact mul_one _
  simpa only [he] using hh

theorem gradedUnit_quotientHilbert [Module.Finite k A] (hφ : Function.Surjective φ)
    (hm : (regularRestrictionCoefficientEquiv k σ A φ).symm 1∈G.degreeSpace 0) (n : ℕ) :
    Module.finrank k ((artinGrading k σ (RingHom.ker φ.toRingHom) (gradedUnit_kernel_homogeneous k σ A φ G hm)).piece (n:ℤ))=
      Module.finrank k (G.piece (n:ℤ)) := by
  let b := cyclicQuotientBasis k σ A φ hφ
  have hb := cyclicQuotientBasis_homogeneous k σ A φ G hφ hm
  let : Finite (StandardExponent MonomialOrder.degLex (RingHom.ker φ.toRingHom)) := b.linearIndependent.finite
  let : Fintype {p : StandardExponent MonomialOrder.degLex (RingHom.ker φ.toRingHom) // (p.val.degree:ℤ)=(n:ℤ)} := Fintype.ofFinite _
  have hh := gradedBasis_piece_finrank k σ (polynomialRegularModule k σ A φ) G b
    (fun p => (p.val.degree:ℤ)) hb (n:ℤ)
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex (RingHom.ker φ.toRingHom) // (p.val.degree:ℤ)=(n:ℤ)} →₀ k)=_
  rw [hh,Module.finrank_finsupp_self,Nat.card_eq_fintype_card]
end NSP14.Endpoint

