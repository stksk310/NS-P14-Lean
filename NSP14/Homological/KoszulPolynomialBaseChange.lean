module

public import NSP14.Homological.PolynomialBaseChangeFinite
public import NSP14.Homological.KoszulTorNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

/-- Actual polynomial scalar extension commutes with the variable Koszul differential. -/
noncomputable def koszulPolynomialBaseChangeIso (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ)) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj (koszulList k σ xs M) ≅
      koszulList L σ xs (polynomialBaseChangeModule k L σ M) := by
  induction xs with
  | nil => exact (singleMapHomologicalComplex (polynomialBaseChangeFunctor k L σ) _ 0).app M
  | cons x xs ih =>
    let K := koszulList k σ xs M
    let F := polynomialBaseChangeFunctor k L σ
    have he : (F.mapHomologicalComplex _).map ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) =
        (MvPolynomial.X x : VariableRing L σ) • 𝟙 ((F.mapHomologicalComplex _).obj K) := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact polynomialBaseChangeFunctor_variable k L σ (K.X i) x
    exact homotopyCofiber.mapHomologicalComplexObjIso ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) F ≪≫
      eqToIso (by rw [he]; rfl) ≪≫
      (scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).mapIso ih

noncomputable def polynomialBaseChangeCoefficientNatIso :
    polynomialBaseChangeFunctor k L σ ⋙ ModuleCat.restrictScalars (algebraMap L (VariableRing L σ)) ≅
      ModuleCat.restrictScalars (algebraMap k (VariableRing k σ)) ⋙ fieldExtension k L :=
  NatIso.ofComponents (polynomialBaseChangeCoefficientIso k L σ) (by
    intro M N f
    apply ModuleCat.hom_ext
    ext a
    rfl)

noncomputable def coefficientChainBaseChangeIso (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) :
    ((ModuleCat.restrictScalars (algebraMap L (VariableRing L σ))).mapHomologicalComplex _).obj
      (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj K) ≅
    ((fieldExtension k L).mapHomologicalComplex _).obj
      (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => polynomialBaseChangeCoefficientIso k L σ (K.X i))
    (fun i j _ => ((polynomialBaseChangeCoefficientNatIso k L σ).hom.naturality (K.d i j)).symm)

/-- This is now the coefficient tensor complex versus Koszul over the actual L[X]-module. -/
noncomputable def koszulPolynomialCoefficientBaseChangeIso [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) :
    ((fieldExtension k L).mapHomologicalComplex _).obj (coefficientKoszulComplex k σ M) ≅
      coefficientKoszulComplex L σ (polynomialBaseChangeModule k L σ M) :=
  (coefficientChainBaseChangeIso k L σ (koszulList k σ (variableList k σ) M)).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap L (VariableRing L σ))).mapHomologicalComplex _).mapIso
      (koszulPolynomialBaseChangeIso k L σ (variableList k σ) M)

/-- Genuine changed-polynomial-module homology base change; no finite-chain hypothesis. -/
noncomputable def koszulPolynomialHomologyBaseChangeIso [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    (fieldExtension k L).obj (koszulHomologyK k σ M i) ≅
      koszulHomologyK L σ (polynomialBaseChangeModule k L σ M) i :=
  (fieldExtension k L).mapIso (coefficientKoszulHomologyIso k σ M i).symm ≪≫
    (fieldExtensionHomologyIso k L (coefficientKoszulComplex k σ M) i).symm ≪≫
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (koszulPolynomialCoefficientBaseChangeIso k L σ M) ≪≫
    coefficientKoszulHomologyIso L σ (polynomialBaseChangeModule k L σ M) i

/-- Total Betti is preserved under actual scalar extension to L[X], in the same characteristic. -/
theorem totalBetti_baseChange [Fintype σ] (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    totalBetti L σ (polynomialBaseChangeModule k L σ M) i=totalBetti k σ M i :=
  (koszulPolynomialHomologyBaseChangeIso k L σ M i).toLinearEquiv.finrank_eq.symm.trans
    (fieldExtension_finrank k L (koszulHomologyK k σ M i))

end NSP14.Homological
