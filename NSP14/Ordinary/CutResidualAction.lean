module
public import NSP14.Ordinary.CutResidualAlgebra
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def extendedPolynomialToA :
    MvPolynomial (Fin (S.actualCutRank+C.complementRank)) k →ₐ[k] S.HeadAlgebra k :=
  (S.polynomialToA k).comp C.extendedPolynomialEquiv.toAlgHom

theorem extendedPolynomialToA_X (i : Fin (S.actualCutRank+C.complementRank)) :
    C.extendedPolynomialToA (MvPolynomial.X i)=(C.extendedHeadBasis i).val := by
  change S.polynomialToA k (C.extendedPolynomialEquiv (MvPolynomial.X i))=_
  rw [C.extendedPolynomialEquiv_X,S.polynomialToA_linearForm,S.linearHeadMap_coordinates]

theorem headToResidual_basis (i : Fin (S.actualCutRank+C.complementRank)) :
    C.headToResidual (C.extendedHeadBasis i).val=
      TrivSqZeroExt.inr (complementCoordinates k S.actualCutRank C.complementRank (Pi.single i (1:k))) := by
  change firstOrderDropPrefix k S.actualCutRank C.complementRank
    (C.firstOrderHeadExtendedEquiv (Ideal.Quotient.mk (S.highIdeal k 2) (C.extendedHeadBasis i).val))=_
  rw [C.firstOrderHeadExtendedEquiv_linear]
  have he : C.extendedHeadBasis.equivFun (C.extendedHeadBasis i)=Pi.single i (1:k) := by
    funext j
    simp [Module.Basis.equivFun_self,Pi.single_apply,eq_comm]
  rw [he,firstOrderDropPrefix,TrivSqZeroExt.map_inr]

theorem headToResidual_complement (i : Fin C.complementRank) :
    C.headToResidual (C.extendedHeadBasis (Fin.natAdd S.actualCutRank i)).val=
      TrivSqZeroExt.inr (Pi.single i (1:k)) := by
  rw [C.headToResidual_basis,complementCoordinates_single_complement]

noncomputable def complementPolynomialToA :
    MvPolynomial (Fin C.complementRank) k →ₐ[k] S.HeadAlgebra k :=
  C.extendedPolynomialToA.comp (MvPolynomial.rename (Fin.natAdd S.actualCutRank))

theorem complementPolynomialToA_X (i : Fin C.complementRank) :
    C.complementPolynomialToA (MvPolynomial.X i)=
      (C.extendedHeadBasis (Fin.natAdd S.actualCutRank i)).val := by
  change C.extendedPolynomialToA (MvPolynomial.rename (Fin.natAdd S.actualCutRank) (MvPolynomial.X i))=_
  rw [MvPolynomial.rename_X,C.extendedPolynomialToA_X]

/-- Equality of actual Z algebra actions, before applying any dimension
or Tor estimate. In particular Z sends the unit to its own independent
complement coordinate, and kills the first-degree maximal ideal. -/
theorem headToResidual_Z_action :
    C.headToResidual.comp C.complementPolynomialToA=firstOrderPolynomial k C.complementRank 0 := by
  apply MvPolynomial.algHom_ext
  intro i
  change C.headToResidual (C.complementPolynomialToA (MvPolynomial.X i))=_
  rw [C.complementPolynomialToA_X,C.headToResidual_complement]
  calc
    _ = (TrivSqZeroExt.inr (Pi.single (Fin.castAdd 0 i) (1:k)) : FirstOrderRing k C.complementRank 0) := by rfl
    _ = _ := (firstOrderPolynomial_X k C.complementRank 0 i).symm

theorem cutResidualEquiv_mk (a : S.HeadAlgebra k) :
    C.cutResidualEquiv (Ideal.Quotient.mk (S.linearCutIdeal k C.forms S.actualCutRank) a)=C.headToResidual a := by
  simp only [cutResidualEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk C.headToResidual_surjective a

noncomputable def complementPolynomialToResidual :
    MvPolynomial (Fin C.complementRank) k →ₐ[k]
      (S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank) :=
  (Ideal.Quotient.mkₐ k (S.linearCutIdeal k C.forms S.actualCutRank)).comp C.complementPolynomialToA

theorem cutResidual_Z_action :
    C.cutResidualEquiv.toAlgHom.comp C.complementPolynomialToResidual=
      firstOrderPolynomial k C.complementRank 0 := by
  rw [← C.headToResidual_Z_action]
  apply AlgHom.ext
  intro p
  exact C.cutResidualEquiv_mk (C.complementPolynomialToA p)
end NSP14.NumericalSemigroup.LinearCutData
