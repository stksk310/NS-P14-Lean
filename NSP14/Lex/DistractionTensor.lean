module
public import NSP14.Lex.DistractionHilbert
public import NSP14.Lex.GenericDistractionBoundary
public import NSP14.Lex.InitialIdeal
public import NSP14.Homological.BasiswiseTensor
@[expose] public section
open scoped Classical TensorProduct
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

def genericDistractionTensorEquiv (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ) :
    coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) ⊗[K] (⋀[K]^j (Fin q → K)) ≃ₗ[K]
      coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) ⊗[K]
        (⋀[K]^j (Fin q → K)) :=
  (basiswiseTensorEquiv (Endpoint.artinMonomialBasis K q I)
    (fun a => genericDistractionWedgeEquiv k q j a.val)).trans
    (TensorProduct.congr (genericDistractionCoefficientEquiv k q I hmono) (LinearEquiv.refl K _))

theorem genericDistractionTensorEquiv_monomial (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ) (a : Fin q →₀ ℕ)
    (w : ⋀[K]^j (Fin q → K)) :
    genericDistractionTensorEquiv k q I hmono j
      ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
        Ideal.Quotient.mk I (MvPolynomial.monomial a 1)) ⊗ₜ[K] w)=
      (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) from
        Ideal.Quotient.mk (genericDistractionIdeal k q I) (genericFieldDistraction k q a)) ⊗ₜ[K]
          genericDistractionWedgeEquiv k q j a w := by
  by_cases ha : MvPolynomial.monomial a (1:K)∈I
  · have hsrc : (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
        Ideal.Quotient.mk I (MvPolynomial.monomial a 1))=0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have htgt := congrArg (genericDistractionCoefficientEquiv k q I hmono) hsrc
    rw [genericDistractionCoefficientEquiv_mk,genericPolynomialEquiv_monomial,map_zero] at htgt
    rw [hsrc,htgt,TensorProduct.zero_tmul,TensorProduct.zero_tmul,map_zero]
  · let p : StandardExponent MonomialOrder.degLex I :=
      ⟨a,(standardExponent_iff_not_mem K q hmono MonomialOrder.degLex a).mpr ha⟩
    have hb : (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
        Ideal.Quotient.mk I (MvPolynomial.monomial a 1))=Endpoint.artinMonomialBasis K q I p :=
      (Endpoint.artinMonomialBasis_apply K q I p).symm
    rw [hb]
    unfold genericDistractionTensorEquiv
    rw [LinearEquiv.trans_apply,basiswiseTensorEquiv_tmul,TensorProduct.congr_tmul]
    change genericDistractionCoefficientEquiv k q I hmono (Endpoint.artinMonomialBasis K q I p) ⊗ₜ[K]
      genericDistractionWedgeEquiv k q j a w=_
    rw [← hb,genericDistractionCoefficientEquiv_mk,genericPolynomialEquiv_monomial]

def genericDistractionBasis (I : Ideal (MvPolynomial (Fin q) K)) (hmono : IsMonomial K q I) :
    Module.Basis (StandardExponent MonomialOrder.degLex I) K
      (coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))) :=
  (Endpoint.artinMonomialBasis K q I).map (genericDistractionCoefficientEquiv k q I hmono)

theorem genericDistractionBasis_apply (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (p : StandardExponent MonomialOrder.degLex I) :
    genericDistractionBasis k q I hmono p =
      Ideal.Quotient.mk (genericDistractionIdeal k q I) (genericFieldDistraction k q p.val) := by
  rw [genericDistractionBasis,Module.Basis.map_apply,Endpoint.artinMonomialBasis_apply,
    genericDistractionCoefficientEquiv_mk,genericPolynomialEquiv_monomial]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericDistractionBasis_homogeneous (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (p : StandardExponent MonomialOrder.degLex I) :
    genericDistractionBasis k q I hmono p∈
      (Endpoint.artinGrading K (Fin q) (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I)).degreeSpace (p.val.degree:ℤ) := by
  change genericDistractionCoefficientEquiv k q I hmono (Endpoint.artinMonomialBasis K q I p)∈_
  exact genericDistractionCoefficientEquiv_degree k q I hmono hI _ _
    (Endpoint.artinMonomialBasis_homogeneous K q I hI p)
end NSP14.Lex
