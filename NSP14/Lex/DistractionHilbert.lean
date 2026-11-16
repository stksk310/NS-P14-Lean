module
public import NSP14.Lex.DistractionIdeal
public import NSP14.Endpoint.ArtinGradedChain
@[expose] public section
open scoped Classical
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem artinFieldMap_degree
    (I J : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (f : coefficientModule k (Fin q) (Endpoint.artinModule k (Fin q) I) →ₗ[k]
      coefficientModule k (Fin q) (Endpoint.artinModule k (Fin q) J))
    (hb : ∀ p : StandardExponent MonomialOrder.degLex I,
      f (Endpoint.artinMonomialBasis k q I p)∈
        (Endpoint.artinGrading k (Fin q) J hJ).degreeSpace (p.val.degree:ℤ))
    (t : ℤ) (a : coefficientModule k (Fin q) (Endpoint.artinModule k (Fin q) I))
    (ha : a∈(Endpoint.artinGrading k (Fin q) I hI).degreeSpace t) :
    f a∈(Endpoint.artinGrading k (Fin q) J hJ).degreeSpace t := by
  have h : (Endpoint.artinGrading k (Fin q) I hI).degreeSpace t ≤
      ((Endpoint.artinGrading k (Fin q) J hJ).degreeSpace t).comap f := by
    rw [← homogeneous_basis_span k (Fin q) (Endpoint.artinModule k (Fin q) I)
      (Endpoint.artinGrading k (Fin q) I hI) (Endpoint.artinMonomialBasis k q I)
      (fun p => (p.val.degree:ℤ)) (Endpoint.artinMonomialBasis_homogeneous k q I hI) t]
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change f (Endpoint.artinMonomialBasis k q I p.val)∈
      (Endpoint.artinGrading k (Fin q) J hJ).degreeSpace t
    simpa only [p.property] using hb p.val
  exact h ha

variable (I : Ideal (MvPolynomial (Fin q) (GenericDistractionField k q)))
    (hmono : IsMonomial (GenericDistractionField k q) q I)

def genericDistractionCoefficientEquiv :
    coefficientModule (GenericDistractionField k q) (Fin q)
      (Endpoint.artinModule (GenericDistractionField k q) (Fin q) I) ≃ₗ[GenericDistractionField k q]
    coefficientModule (GenericDistractionField k q) (Fin q)
      (Endpoint.artinModule (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)) :=
  (coefficientOriginalEquiv _ (Fin q) _).trans ((genericDistractionQuotientEquiv k q I hmono).trans
    (coefficientOriginalEquiv _ (Fin q) _).symm)

theorem genericDistractionCoefficientEquiv_mk
    (f : MvPolynomial (Fin q) (GenericDistractionField k q)) :
    genericDistractionCoefficientEquiv k q I hmono (Ideal.Quotient.mk I f)=
      Ideal.Quotient.mk (genericDistractionIdeal k q I) (genericPolynomialEquiv k q f) := rfl

theorem genericDistractionCoefficientEquiv_symm_mk
    (f : MvPolynomial (Fin q) (GenericDistractionField k q)) :
    (genericDistractionCoefficientEquiv k q I hmono).symm
      (Ideal.Quotient.mk (genericDistractionIdeal k q I) f)=
      Ideal.Quotient.mk I ((genericPolynomialEquiv k q).symm f) := by
  apply (genericDistractionCoefficientEquiv k q I hmono).injective
  rw [LinearEquiv.apply_symm_apply,genericDistractionCoefficientEquiv_mk,LinearEquiv.apply_symm_apply]

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q)))

theorem genericDistractionCoefficientEquiv_degree
    (t : ℤ) (a : coefficientModule (GenericDistractionField k q) (Fin q)
      (Endpoint.artinModule (GenericDistractionField k q) (Fin q) I))
    (ha : a∈(Endpoint.artinGrading (GenericDistractionField k q) (Fin q) I hI).degreeSpace t) :
    genericDistractionCoefficientEquiv k q I hmono a∈
      (Endpoint.artinGrading (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I)).degreeSpace t := by
  apply artinFieldMap_degree _ _ _ _ hI (genericDistractionIdeal_homogeneous k q I)
    (genericDistractionCoefficientEquiv k q I hmono).toLinearMap ?_ t a ha
  intro p
  change genericDistractionCoefficientEquiv k q I hmono (Endpoint.artinMonomialBasis _ q I p)∈_
  rw [Endpoint.artinMonomialBasis_apply,genericDistractionCoefficientEquiv_mk,genericPolynomialEquiv_monomial]
  exact Endpoint.artin_mk_homogeneous _ _ _ _ _ _ (genericFieldDistraction_homogeneous k q p.val)

theorem genericDistractionCoefficientEquiv_symm_degree
    (t : ℤ) (a : coefficientModule (GenericDistractionField k q) (Fin q)
      (Endpoint.artinModule (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)))
    (ha : a∈(Endpoint.artinGrading (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)
      (genericDistractionIdeal_homogeneous k q I)).degreeSpace t) :
    (genericDistractionCoefficientEquiv k q I hmono).symm a∈
      (Endpoint.artinGrading (GenericDistractionField k q) (Fin q) I hI).degreeSpace t := by
  apply artinFieldMap_degree _ _ _ _ (genericDistractionIdeal_homogeneous k q I) hI
    (genericDistractionCoefficientEquiv k q I hmono).symm.toLinearMap ?_ t a ha
  intro p
  change (genericDistractionCoefficientEquiv k q I hmono).symm
    (Endpoint.artinMonomialBasis _ q (genericDistractionIdeal k q I) p)∈_
  rw [Endpoint.artinMonomialBasis_apply,genericDistractionCoefficientEquiv_symm_mk]
  apply Endpoint.artin_mk_homogeneous
  apply (genericPolynomialEquiv_homogeneous_iff k q p.val.degree _).mp
  rw [LinearEquiv.apply_symm_apply]
  exact MvPolynomial.isHomogeneous_monomial 1 rfl

theorem genericDistractionCoefficientEquiv_map_degree (t : ℤ) :
    ((Endpoint.artinGrading (GenericDistractionField k q) (Fin q) I hI).degreeSpace t).map
      (genericDistractionCoefficientEquiv k q I hmono).toLinearMap =
    (Endpoint.artinGrading (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)
      (genericDistractionIdeal_homogeneous k q I)).degreeSpace t := by
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    exact genericDistractionCoefficientEquiv_degree k q I hmono hI t b hb
  · intro a ha
    exact ⟨(genericDistractionCoefficientEquiv k q I hmono).symm a,
      genericDistractionCoefficientEquiv_symm_degree k q I hmono hI t a ha,
      (genericDistractionCoefficientEquiv k q I hmono).apply_symm_apply a⟩

def genericDistractionPieceEquiv (t : ℤ) :
    (Endpoint.artinGrading (GenericDistractionField k q) (Fin q) I hI).piece t ≃ₗ[GenericDistractionField k q]
    (Endpoint.artinGrading (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)
      (genericDistractionIdeal_homogeneous k q I)).piece t :=
  ((Endpoint.artinGrading (GenericDistractionField k q) (Fin q) I hI).rangeEquiv t).trans
    (((genericDistractionCoefficientEquiv k q I hmono).ofSubmodules _ _
      (genericDistractionCoefficientEquiv_map_degree k q I hmono hI t)).trans
      ((Endpoint.artinGrading (GenericDistractionField k q) (Fin q) (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I)).rangeEquiv t).symm)

theorem genericDistraction_sameHilbert
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q)))
    (hmono : IsMonomial (GenericDistractionField k q) q I) (n : ℕ) :
    quotientHilbert (GenericDistractionField k q) q I hI n =
      quotientHilbert (GenericDistractionField k q) q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) n :=
  (genericDistractionPieceEquiv k q I hmono hI n).finrank_eq
end NSP14.Lex
