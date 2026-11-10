module
public import NSP14.Ordinary.CutBModel
public import NSP14.Homological.FirstOrderAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem extendedPolynomialEquiv_X (i : Fin (S.actualCutRank+C.complementRank)) :
    C.extendedPolynomialEquiv (MvPolynomial.X i)=
      S.linearFormPolynomial k (S.headLinearCoordinates k (C.extendedHeadBasis i)) := by
  change linearSubstitution C.extendedCoefficientEquiv.toLinearMap (MvPolynomial.X i)=_
  rw [linearSubstitution_X]
  simp only [extendedCoefficientEquiv,LinearEquiv.coe_coe,LinearEquiv.trans_apply]
  simp only [Module.Basis.equivFun_symm_apply]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (S.linearFormPolynomial_eq k _).symm

noncomputable def extendedPolynomialToB :
    MvPolynomial (Fin (S.actualCutRank+C.complementRank)) k →ₐ[k] S.FirstOrderHead k :=
  (Ideal.Quotient.mkₐ k (S.highIdeal k 2)).comp
    ((S.polynomialToA k).comp C.extendedPolynomialEquiv.toAlgHom)

theorem extendedPolynomialToB_X (i : Fin (S.actualCutRank+C.complementRank)) :
    C.extendedPolynomialToB (MvPolynomial.X i)=
      Ideal.Quotient.mk (S.highIdeal k 2) (C.extendedHeadBasis i).val := by
  change Ideal.Quotient.mk (S.highIdeal k 2) (S.polynomialToA k (C.extendedPolynomialEquiv (MvPolynomial.X i)))=_
  rw [C.extendedPolynomialEquiv_X,S.polynomialToA_linearForm,S.linearHeadMap_coordinates]

/-- Every non-x variable in the extended presentation has the actual
first-order action in these coordinates, including all complement/Z
variables. This is stronger than merely recording dim H0=f+1. -/
theorem extendedPolynomialToB_model :
    C.firstOrderHeadExtendedEquiv.toAlgHom.comp C.extendedPolynomialToB=
      firstOrderPolynomial k (S.actualCutRank+C.complementRank) 0 := by
  apply MvPolynomial.algHom_ext
  intro i
  change C.firstOrderHeadExtendedEquiv (C.extendedPolynomialToB (MvPolynomial.X i))=_
  rw [C.extendedPolynomialToB_X,C.firstOrderHeadExtendedEquiv_linear]
  calc
    _ = (TrivSqZeroExt.inr (Pi.single (Fin.castAdd 0 i) (1:k)) : FirstOrderRing k (S.actualCutRank+C.complementRank) 0) := by
      congr 1
      funext j
      simp [Module.Basis.equivFun_self,Pi.single_apply,eq_comm]
    _ = _ := (firstOrderPolynomial_X k (S.actualCutRank+C.complementRank) 0 i).symm
end NSP14.NumericalSemigroup.LinearCutData
