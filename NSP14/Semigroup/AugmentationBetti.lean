module
public import NSP14.Homological.RegularAugmentationBetti
public import NSP14.Semigroup.AtomVariableOrder
public import NSP14.Semigroup.HeadSquareZeroBetti
public import NSP14.Homological.ActualTorTransport
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem headConstant_mul (a b : S.HeadAlgebra k) :
    S.headConstant k (a*b)=S.headConstant k a*S.headConstant k b := by
  have h := S.firstOrderConstant_mul k (Ideal.Quotient.mk (S.highIdeal k 2) a) (Ideal.Quotient.mk (S.highIdeal k 2) b)
  simpa only [← map_mul,S.firstOrderConstant_mk] using h

noncomputable def headAugmentation : S.HeadAlgebra k →ₐ[k] k where
  toFun := S.headConstant k
  map_zero' := (S.headConstant k).map_zero
  map_add' := (S.headConstant k).map_add
  map_one' := S.headConstant_one k
  map_mul' := S.headConstant_mul k
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,S.headConstant_one]
    simp

noncomputable def tangentAugmentation : S.TangentAlgebra k →ₐ[k] k :=
  (S.headAugmentation k).comp (S.toHeadAlgebra k)

theorem headAugmentation_polynomial :
    (S.headAugmentation k).comp (S.polynomialToA k)=augmentation k S.NonXAtom := by
  apply MvPolynomial.algHom_ext
  intro a
  change S.headConstant k (S.polynomialToA k (MvPolynomial.X a))=_
  rw [S.polynomialToA_X,augmentation_X]
  exact S.headConstant_linear_zero k (S.linearAtom k a)

theorem tangentAugmentation_polynomial :
    (S.tangentAugmentation k).comp (S.fullPolynomialToG k)=augmentation k S.AtomExponent := by
  apply MvPolynomial.algHom_ext
  intro a
  change S.tangentAugmentation k (S.fullPolynomialToG k (MvPolynomial.X a))=_
  rw [S.fullPolynomialToG_X,augmentation_X]
  by_cases hm : a.val.val=S.multiplicity
  · have he : a.val=S.multiplicityExponent := Subtype.ext hm
    rw [he]
    change S.headAugmentation k (S.toHeadAlgebra k (S.xElement k))=0
    have hx : S.toHeadAlgebra k (S.xElement k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
    rw [hx,map_zero]
  · change S.headConstant k (S.headMonomial k a.val)=0
    exact S.headConstant_linear_zero k (S.linearAtom k ⟨a.val,a.property,hm⟩)

noncomputable def regularHeadModuleIso :
    polynomialRegularModule k S.NonXAtom (S.HeadAlgebra k) (S.polynomialToA k) ≅ S.headPolynomialModule k := by
  let e : polynomialRegularModule k S.NonXAtom (S.HeadAlgebra k) (S.polynomialToA k) ≃ₗ[S.PolynomialRing k]
      S.headPolynomialModule k :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

/-- Zeroth intrinsic Betti is one for every actual source, without an
ordinary-width or finite coefficient-dimensional G assumption. -/
theorem actualG_totalBetti_zero :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) 0=1 := by
  let := regularPresentation_finite k S.AtomExponent (S.TangentAlgebra k) (S.fullPolynomialToG k) (S.fullPolynomialToG_surjective k)
  rw [← totalBetti_iso k S.AtomExponent (S.regularFullModuleIso k)]
  exact regularAugmented_totalBetti_zero k S.AtomExponent (S.TangentAlgebra k)
    (S.fullPolynomialToG k) (S.tangentAugmentation k) (S.fullPolynomialToG_surjective k) (S.tangentAugmentation_polynomial k)

theorem actualA_totalBetti_zero : totalBetti k S.NonXAtom (S.headPolynomialModule k) 0=1 := by
  let := regularPresentation_finite k S.NonXAtom (S.HeadAlgebra k) (S.polynomialToA k) (S.polynomialToA_surjective k)
  rw [← totalBetti_iso k S.NonXAtom (S.regularHeadModuleIso k)]
  exact regularAugmented_totalBetti_zero k S.NonXAtom (S.HeadAlgebra k)
    (S.polynomialToA k) (S.headAugmentation k) (S.polynomialToA_surjective k) (S.headAugmentation_polynomial k)
theorem completed_totalBetti_zero :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 0=1 := by
  rw [← S.completed_totalBetti k,S.actualG_totalBetti_zero k]
end NSP14.NumericalSemigroup
