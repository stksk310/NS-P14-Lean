module
public import NSP14.Lex.DistractionChain
public import NSP14.Homological.KoszulExteriorGrading
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory HomologicalComplex NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

abbrev genericKoszulChainGrading (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K)) (i : ℕ) :=
  koszulChainGrading K (Fin q) (Endpoint.artinModule K (Fin q) I)
    (Endpoint.artinGrading K (Fin q) I hI) (variableList K (Fin q)) i

theorem genericDistractionChainEquiv_tensor (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ) (a : Fin q →₀ ℕ) (w : ⋀[K]^i (Fin q → K)) :
    genericDistractionChainEquiv k q I hmono i
      ((koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) i).symm
          ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) I) from
            Ideal.Quotient.mk I (MvPolynomial.monomial a 1)) ⊗ₜ[K] w))=
      (koszulExteriorTensorEquiv K (Fin q)
        (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
          (genericDistractionBasis k q I hmono) i).symm
        ((show coefficientModule K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I)) from
          Ideal.Quotient.mk (genericDistractionIdeal k q I) (genericFieldDistraction k q a)) ⊗ₜ[K]
            genericDistractionWedgeEquiv k q i a w) := by
  simp only [genericDistractionChainEquiv,LinearEquiv.trans_apply]
  erw [LinearEquiv.apply_symm_apply]
  rw [genericDistractionTensorEquiv_monomial]
  rfl

theorem genericDistractionChainEquiv_basis (I : Ideal (MvPolynomial (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ)
    (s : KoszulSlot (variableList K (Fin q)).length i) (p : StandardExponent MonomialOrder.degLex I) :
    genericDistractionChainEquiv k q I hmono i
      (koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) (variableList K (Fin q)) i (s,p))=
      (koszulExteriorTensorEquiv K (Fin q)
        (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
          (genericDistractionBasis k q I hmono) i).symm
        (genericDistractionBasis k q I hmono p ⊗ₜ[K]
          genericDistractionWedgeEquiv k q i p.val (koszulExteriorBasis (σ:=Fin q) K i s)) := by
  simp only [genericDistractionChainEquiv,LinearEquiv.trans_apply]
  erw [koszulExteriorTensorEquiv_basis]
  rw [Endpoint.artinMonomialBasis_apply,genericDistractionTensorEquiv_monomial,genericDistractionBasis_apply]
  rfl

theorem genericDistractionChainEquiv_basis_homogeneous (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ)
    (s : KoszulSlot (variableList K (Fin q)).length i) (p : StandardExponent MonomialOrder.degLex I) :
    genericDistractionChainEquiv k q I hmono i
      (koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) (variableList K (Fin q)) i (s,p))∈
      (genericKoszulChainGrading k q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) i).degreeSpace (p.val.degree:ℤ) := by
  rw [genericDistractionChainEquiv_basis]
  exact koszulExteriorTensorEquiv_symm_basis_homogeneous K (Fin q)
    (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
    (Endpoint.artinGrading K (Fin q) (genericDistractionIdeal k q I) (genericDistractionIdeal_homogeneous k q I))
    (genericDistractionBasis k q I hmono) (fun p => (p.val.degree:ℤ))
    (genericDistractionBasis_homogeneous k q I hmono hI) i p _

theorem genericDistractionChainEquiv_degree (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ) (t : ℤ)
    (a : coefficientModule K (Fin q) ((koszulList K (Fin q) (variableList K (Fin q))
      (Endpoint.artinModule K (Fin q) I)).X i))
    (ha : a∈(genericKoszulChainGrading k q I hI i).degreeSpace t) :
    genericDistractionChainEquiv k q I hmono i a ∈
      (genericKoszulChainGrading k q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) i).degreeSpace t := by
  apply homogeneousBasisMap_degree K (Fin q) _ _
    (genericKoszulChainGrading k q I hI i)
    (genericKoszulChainGrading k q (genericDistractionIdeal k q I) (genericDistractionIdeal_homogeneous k q I) i)
    (koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) I)
      (Endpoint.artinMonomialBasis K q I) (variableList K (Fin q)) i)
    (fun a => (a.2.val.degree:ℤ))
    (koszulSlotBasis_homogeneous K (Fin q) _ _ (Endpoint.artinMonomialBasis K q I)
      (fun p => (p.val.degree:ℤ)) (Endpoint.artinMonomialBasis_homogeneous K q I hI) _ i)
    (genericDistractionChainEquiv k q I hmono i).toLinearMap ?_ t a ha
  rintro ⟨s,p⟩
  exact genericDistractionChainEquiv_basis_homogeneous k q I hI hmono i s p

theorem genericDistractionChainEquiv_basis_preimage (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ)
    (s : KoszulSlot (variableList K (Fin q)).length i) (p : StandardExponent MonomialOrder.degLex I) :
    koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) (variableList K (Fin q)) i (s,p)∈
    ((genericKoszulChainGrading k q I hI i).degreeSpace (p.val.degree:ℤ)).map
      (genericDistractionChainEquiv k q I hmono i).toLinearMap := by
  refine ⟨(koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) I)
    (Endpoint.artinMonomialBasis K q I) i).symm
      (Endpoint.artinMonomialBasis K q I p ⊗ₜ[K]
        (genericDistractionWedgeEquiv k q i p.val).symm (koszulExteriorBasis (σ:=Fin q) K i s)),?_,?_⟩
  · exact koszulExteriorTensorEquiv_symm_basis_homogeneous K (Fin q)
      (Endpoint.artinModule K (Fin q) I) (Endpoint.artinGrading K (Fin q) I hI)
      (Endpoint.artinMonomialBasis K q I) (fun p => (p.val.degree:ℤ))
      (Endpoint.artinMonomialBasis_homogeneous K q I hI) i p _
  · change genericDistractionChainEquiv k q I hmono i
      ((koszulExteriorTensorEquiv K (Fin q) (Endpoint.artinModule K (Fin q) I)
        (Endpoint.artinMonomialBasis K q I) i).symm
        (Endpoint.artinMonomialBasis K q I p ⊗ₜ[K]
          (genericDistractionWedgeEquiv k q i p.val).symm (koszulExteriorBasis (σ:=Fin q) K i s)))=_
    rw [Endpoint.artinMonomialBasis_apply,genericDistractionChainEquiv_tensor,LinearEquiv.apply_symm_apply]
    apply (koszulExteriorTensorEquiv K (Fin q)
      (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) i).injective
    erw [LinearEquiv.apply_symm_apply,koszulExteriorTensorEquiv_basis]
    rw [genericDistractionBasis_apply]

theorem genericDistractionChainEquiv_map_degree (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ) (t : ℤ) :
    ((genericKoszulChainGrading k q I hI i).degreeSpace t).map
      (genericDistractionChainEquiv k q I hmono i).toLinearMap =
      (genericKoszulChainGrading k q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) i).degreeSpace t := by
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    exact genericDistractionChainEquiv_degree k q I hI hmono i t b hb
  · rw [← homogeneous_basis_span K (Fin q)
      ((koszulList K (Fin q) (variableList K (Fin q))
        (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))).X i)
      (genericKoszulChainGrading k q (genericDistractionIdeal k q I) (genericDistractionIdeal_homogeneous k q I) i)
      (koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
        (genericDistractionBasis k q I hmono) (variableList K (Fin q)) i)
      (fun a => (a.2.val.degree:ℤ))
      (koszulSlotBasis_homogeneous K (Fin q) _ _ (genericDistractionBasis k q I hmono)
        (fun p => (p.val.degree:ℤ)) (genericDistractionBasis_homogeneous k q I hmono hI) _ i) t]
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change koszulSlotBasis K (Fin q) (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
      (genericDistractionBasis k q I hmono) (variableList K (Fin q)) i p.val∈
      ((genericKoszulChainGrading k q I hI i).degreeSpace t).map
        (genericDistractionChainEquiv k q I hmono i).toLinearMap
    have h := genericDistractionChainEquiv_basis_preimage k q I hI hmono i p.val.1 p.val.2
    simpa only [p.property] using h

abbrev genericGradedKoszulComplex (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K)) (t : ℤ) :=
  gradedKoszulComplex K (Fin q) (Endpoint.artinModule K (Fin q) I)
    (Endpoint.artinGrading K (Fin q) I hI) (variableList K (Fin q)) t

def genericDistractionGradedChainEquiv (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (t : ℤ) (i : ℕ) :
    (genericGradedKoszulComplex k q I hI t).X i ≃ₗ[K]
      (genericGradedKoszulComplex k q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) t).X i :=
  (genericDistractionChainEquiv k q I hmono i).ofSubmodules _ _
    (genericDistractionChainEquiv_map_degree k q I hI hmono i (t-(i:ℤ)))

def genericDistractionGradedChainIso (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (t : ℤ) :
    genericGradedKoszulComplex k q I hI t ≅
      genericGradedKoszulComplex k q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (genericDistractionGradedChainEquiv k q I hI hmono t i).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      have hdI : (genericGradedKoszulComplex k q I hI t).d (j+1) j=
          ModuleCat.ofHom (gradedKoszulDifferential K (Fin q) (Endpoint.artinModule K (Fin q) I)
            (Endpoint.artinGrading K (Fin q) I hI) (variableList K (Fin q)) t j) := by
        dsimp only [genericGradedKoszulComplex,gradedKoszulComplex]
        exact ChainComplex.of_d _ _ j
      have hdJ : (genericGradedKoszulComplex k q (genericDistractionIdeal k q I)
          (genericDistractionIdeal_homogeneous k q I) t).d (j+1) j=
          ModuleCat.ofHom (gradedKoszulDifferential K (Fin q)
            (Endpoint.artinModule K (Fin q) (genericDistractionIdeal k q I))
            (Endpoint.artinGrading K (Fin q) (genericDistractionIdeal k q I)
              (genericDistractionIdeal_homogeneous k q I)) (variableList K (Fin q)) t j) := by
        dsimp only [genericGradedKoszulComplex,gradedKoszulComplex]
        exact ChainComplex.of_d _ _ j
      rw [hdI,hdJ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      change (genericCoefficientKoszulComplex k q (genericDistractionIdeal k q I)).d (j+1) j
          (genericDistractionChainEquiv k q I hmono (j+1) a.val)=
        genericDistractionChainEquiv k q I hmono j
          ((genericCoefficientKoszulComplex k q I).d (j+1) j a.val)
      exact genericDistractionChainEquiv_comm k q I hmono j a.val)

theorem genericDistraction_gradedBetti (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : IsMonomial K q I) (i : ℕ) (t : ℤ) :
    quotientGradedBetti K q I hI i t=
      quotientGradedBetti K q (genericDistractionIdeal k q I)
        (genericDistractionIdeal_homogeneous k q I) i t :=
  ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
    (genericDistractionGradedChainIso k q I hI hmono t)).toLinearEquiv.finrank_eq
end NSP14.Lex
