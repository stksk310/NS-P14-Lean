module
public import NSP14.Semigroup.CutBasis
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def extendedCutProjection :
    MvPolynomial (Fin (S.actualCutRank+C.complementRank)) k →ₐ[k] S.CutPolynomialRing k :=
  MvPolynomial.aeval (fun i => if h : i.val < S.actualCutRank then MvPolynomial.X ⟨i.val,h⟩ else 0)

theorem extendedCutProjection_prefix (i : Fin S.actualCutRank) :
    C.extendedCutProjection (MvPolynomial.X (Fin.castAdd C.complementRank i))=MvPolynomial.X i := by
  rw [extendedCutProjection,MvPolynomial.aeval_X]
  simp only [Fin.val_castAdd,dite_eq_left i.isLt]

/-- An explicit polynomial left retraction, by the prefix-preserving actual
linear variable change, then setting only the complementary variables to zero. -/
noncomputable def polynomialRetraction : S.PolynomialRing k →ₐ[k] S.CutPolynomialRing k :=
  C.extendedCutProjection.comp C.extendedPolynomialEquiv.symm.toAlgHom

theorem polynomialRetraction_form (i : Fin S.actualCutRank) :
    C.polynomialRetraction (C.polynomialForm i)=MvPolynomial.X i := by
  change C.extendedCutProjection (C.extendedPolynomialEquiv.symm (C.polynomialForm i))=_
  rw [← C.extendedPolynomialEquiv_prefix i,AlgEquiv.symm_apply_apply,C.extendedCutProjection_prefix]

theorem polynomialRetraction_comp :
    C.polynomialRetraction.comp C.toPolynomialRing=AlgHom.id k (S.CutPolynomialRing k) := by
  apply MvPolynomial.algHom_ext
  intro i
  change C.polynomialRetraction (C.toPolynomialRing (MvPolynomial.X i))=MvPolynomial.X i
  rw [C.toPolynomialRing_X,C.polynomialRetraction_form]
end NSP14.NumericalSemigroup.LinearCutData
