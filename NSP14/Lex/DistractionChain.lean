module
public import NSP14.Lex.DistractionTensor
@[expose] public section
open scoped Classical TensorProduct BigOperators
open CategoryTheory HomologicalComplex NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

theorem genericArtin_scalar_one (J : Ideal (MvPolynomial (Fin q) K)) (f : MvPolynomial (Fin q) K) :
    f • (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) J) from Ideal.Quotient.mk J 1)=
      Ideal.Quotient.mk J f := by
  change Ideal.Quotient.mk J f * Ideal.Quotient.mk J 1=Ideal.Quotient.mk J f
  rw [map_one,mul_one]

theorem genericArtin_variable_monomial (J : Ideal (MvPolynomial (Fin q) K))
    (a : Fin q →₀ ℕ) (i : Fin q) :
    (MvPolynomial.X i : VariableRing K (Fin q)) •
      (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) J) from
        Ideal.Quotient.mk J (MvPolynomial.monomial a 1))=
      Ideal.Quotient.mk J (MvPolynomial.monomial (a+Finsupp.single i 1) 1) := by
  change Ideal.Quotient.mk J (MvPolynomial.X i*MvPolynomial.monomial a 1)=_
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,add_comm]

theorem genericDistractionTensorEquiv_comm_monomial (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ) (a : Fin q →₀ ℕ)
    (w : ⋀[K]^(j+1) (Fin q → K)) :
    koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) j
      (genericDistractionTensorEquiv k q I hmono (j+1)
        ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
          Ideal.Quotient.mk I (MvPolynomial.monomial a 1)) ⊗ₜ[K] w))=
    genericDistractionTensorEquiv k q I hmono j
      (koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) j
          ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
            Ideal.Quotient.mk I (MvPolynomial.monomial a 1)) ⊗ₜ[K] w)) := by
  rw [genericDistractionTensorEquiv_monomial]
  have hleft := genericDistractionBoundary_monomial k q
    (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
    (genericDistractionBasis k q I hmono) j a
    (show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) from
      Ideal.Quotient.mk (genericDistractionIdeal k q I) 1) w
  simp_rw [genericArtin_scalar_one] at hleft
  rw [hleft,koszulExteriorBoundary_tmul,map_sum]
  simp_rw [genericArtin_variable_monomial,genericDistractionTensorEquiv_monomial]

theorem genericDistractionTensorEquiv_comm (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ)
    (z : coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) ⊗[K]
      (⋀[K]^(j+1) (Fin q → K))) :
    koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) j (genericDistractionTensorEquiv k q I hmono (j+1) z)=
    genericDistractionTensorEquiv k q I hmono j
      (koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) j z) := by
  have h : (koszulExteriorBoundary K (Fin q)
      (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) j).comp (genericDistractionTensorEquiv k q I hmono (j+1)).toLinearMap=
    (genericDistractionTensorEquiv k q I hmono j).toLinearMap.comp
      (koszulExteriorBoundary K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) j) := by
    apply ((Endpoint.artinMonomialBasis K q I).tensorProduct (koszulExteriorBasis (σ:=Fin q) K (j+1))).ext
    rintro ⟨p,s⟩
    rw [Module.Basis.tensorProduct_apply]
    change koszulExteriorBoundary K (Fin q) _ _ j
      (genericDistractionTensorEquiv k q I hmono (j+1)
        (Endpoint.artinMonomialBasis K q I p ⊗ₜ[K] koszulExteriorBasis (σ:=Fin q) K (j+1) s))=_
    rw [Endpoint.artinMonomialBasis_apply]
    exact genericDistractionTensorEquiv_comm_monomial k q I hmono j p.val _
  exact LinearMap.congr_fun h z


abbrev genericCoefficientKoszulComplex (I : Ideal (MvPolynomial (Fin q) K)) :=
  (coefficientKoszulListFunctor K (Fin q) (variableList K (Fin q))).obj
    (Endpoint.artinModule K (Fin q) I)

def genericDistractionChainEquiv (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ) :
    (genericCoefficientKoszulComplex k q I).X j ≃ₗ[K]
    (genericCoefficientKoszulComplex k q (genericDistractionIdeal k q I)).X j :=
  (koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) I)
    (Endpoint.artinMonomialBasis K q I) j).trans
    ((genericDistractionTensorEquiv k q I hmono j).trans
      (koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
        (genericDistractionBasis k q I hmono) j).symm)

theorem genericDistractionChainEquiv_comm (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (j : ℕ) (a : (genericCoefficientKoszulComplex k q I).X (j+1)) :
    (genericCoefficientKoszulComplex k q (genericDistractionIdeal k q I)).d (j+1) j
      (genericDistractionChainEquiv k q I hmono (j+1) a)=
    genericDistractionChainEquiv k q I hmono j
      ((genericCoefficientKoszulComplex k q I).d (j+1) j a) := by
  apply (koszulExteriorTensorEquiv K (Fin q)
    (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
    (genericDistractionBasis k q I hmono) j).injective
  have h := genericDistractionTensorEquiv_comm k q I hmono j
    (koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) I)
      (Endpoint.artinMonomialBasis K q I) (j+1) a)
  change koszulExteriorTensorEquiv K (Fin q) _ _ j
      ((genericCoefficientKoszulComplex k q (genericDistractionIdeal k q I)).d (j+1) j
        ((koszulExteriorTensorEquiv K (Fin q) _ _ (j+1)).symm
          (genericDistractionTensorEquiv k q I hmono (j+1)
            (koszulExteriorTensorEquiv K (Fin q) _ _ (j+1) a)))) =
    genericDistractionTensorEquiv k q I hmono j
      (koszulExteriorTensorEquiv K (Fin q) _ _ j
        ((genericCoefficientKoszulComplex k q I).d (j+1) j
          ((koszulExteriorTensorEquiv K (Fin q) _ _ (j+1)).symm
            (koszulExteriorTensorEquiv K (Fin q) _ _ (j+1) a)))) at h
  rw [LinearEquiv.symm_apply_apply] at h
  simp only [genericDistractionChainEquiv,LinearEquiv.trans_apply]
  erw [LinearEquiv.apply_symm_apply]
  exact h

def genericDistractionChainIso (I : Ideal (MvPolynomial (Fin q) K)) (hmono : IsMonomial K q I) :
    genericCoefficientKoszulComplex k q I ≅
      genericCoefficientKoszulComplex k q (genericDistractionIdeal k q I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (genericDistractionChainEquiv k q I hmono j).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact genericDistractionChainEquiv_comm k q I hmono j a)

theorem genericDistraction_totalBetti (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ) :
    totalBetti K (Fin q) (Endpoint.artinModule K (Fin q) I) i=
      totalBetti K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) i := by
  let e : coefficientKoszulComplex K (Fin q) (Endpoint.artinModule K (Fin q) I) ≅
      coefficientKoszulComplex K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) :=
    genericDistractionChainIso k q I hmono
  exact ((coefficientKoszulHomologyIso K (Fin q) (Endpoint.artinModule K (Fin q) I) i).symm ≪≫
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso e ≪≫
    coefficientKoszulHomologyIso K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) i).toLinearEquiv.finrank_eq
end NSP14.Lex
