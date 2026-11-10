module
public import NSP14.Ordinary.CutBEuler
public import NSP14.Semigroup.HeadFirstOrderAlgebra
public import NSP14.Homological.TrivSqZeroCoordinates
public import NSP14.Homological.SquareZeroModel
public import NSP14.Homological.PolynomialLinearMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- Algebra coordinates in the same extended basis whose prefix is the
selected cut. The complementary degree-one coordinates are retained. -/
noncomputable def firstOrderHeadExtendedEquiv :
    S.FirstOrderHead k ≃ₐ[k] FirstOrderRing k S.actualCutRank C.complementRank :=
  (S.firstOrderHeadTrivEquiv k).trans
    (trivSqZeroCoordinatesEquiv k S.NonXAtom (Fin (S.actualCutRank+C.complementRank)) C.extendedCoefficientEquiv.symm)

theorem firstOrderHeadExtendedEquiv_linear (c : S.headDegree k 1) :
    C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) c.val)=
      TrivSqZeroExt.inr (C.extendedHeadBasis.equivFun c) := by
  apply TrivSqZeroExt.ext
  · exact S.firstOrderConstant_linear_zero k c
  · change C.extendedCoefficientEquiv.symm
      (S.headLinearCoordinates k (S.firstOrderLinearPart k (Ideal.Quotient.mk (S.highIdeal k 2) c.val)))=_
    rw [S.firstOrderLinearPart_linear]
    simp [extendedCoefficientEquiv]

theorem firstOrderHeadExtendedEquiv_lambda (v : Fin S.actualCutRank) :
    C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val)=
      TrivSqZeroExt.inr (Pi.single (Fin.castAdd C.complementRank v) 1) := by
  rw [C.firstOrderHeadExtendedEquiv_linear,← C.extendedHeadBasis_prefix v]
  congr 1
  funext i
  simp [Module.Basis.equivFun_self,Pi.single_apply,eq_comm]

noncomputable def cutBModelCoefficientEquiv :
    coefficientModule k (Fin S.actualCutRank) C.cutB ≃ₗ[k]
      coefficientModule k (Fin S.actualCutRank) (firstOrderModule k S.actualCutRank C.complementRank) :=
  (C.cutBCoefficientEquiv.trans C.firstOrderHeadExtendedEquiv.toLinearEquiv).trans
    (firstOrderCoefficientEquiv k S.actualCutRank C.complementRank).symm

theorem cutBModelCoefficientEquiv_apply (a : coefficientModule k (Fin S.actualCutRank) C.cutB) :
    firstOrderCoefficientEquiv k S.actualCutRank C.complementRank (C.cutBModelCoefficientEquiv a)=
      C.firstOrderHeadExtendedEquiv (C.cutBCoefficientEquiv a) := by
  exact (firstOrderCoefficientEquiv k S.actualCutRank C.complementRank).apply_symm_apply _

theorem cutBModel_variable (v : Fin S.actualCutRank) (a : coefficientModule k (Fin S.actualCutRank) C.cutB) :
    C.cutBModelCoefficientEquiv ((MvPolynomial.X v : S.CutPolynomialRing k) • a)=
      (MvPolynomial.X v : S.CutPolynomialRing k) • C.cutBModelCoefficientEquiv a := by
  apply (firstOrderCoefficientEquiv k S.actualCutRank C.complementRank).injective
  rw [C.cutBModelCoefficientEquiv_apply,C.cutB_variable,map_mul,C.firstOrderHeadExtendedEquiv_lambda,
    firstOrder_variable,C.cutBModelCoefficientEquiv_apply]

/-- Actual P-module isomorphism, rather than a dimension-only replacement
of B. Its model retains f=e-r-1 extra first-degree generators. -/
noncomputable def cutBModelIso : C.cutB ≅ firstOrderModule k S.actualCutRank C.complementRank :=
  (LinearEquiv.ofBijective
    (polynomialHomOfVariables k (Fin S.actualCutRank) C.cutBModelCoefficientEquiv.toLinearMap C.cutBModel_variable).hom
    C.cutBModelCoefficientEquiv.bijective).toModuleIso
end NSP14.NumericalSemigroup.LinearCutData
