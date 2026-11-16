module
public import NSP14.Semigroup.CutPolynomialInjection
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- Number of non-x variables complementary to this very cut. -/
noncomputable def complementRank (_C : S.LinearCutData k) : ℕ := Module.finrank k (S.headDegree k 1)-S.actualCutRank

theorem complementRank_eq : C.complementRank=S.embeddingDimension-S.actualCutRank-1 := by
  unfold complementRank
  rw [S.headDegree_one_finrank]
  omega

noncomputable def extendedHeadBasis :
    Module.Basis (Fin (S.actualCutRank+C.complementRank)) k (S.headDegree k 1) :=
  NSP14.Homological.basisExtendingPrefix C.forms C.independent

theorem extendedHeadBasis_prefix (i : Fin S.actualCutRank) :
    C.extendedHeadBasis (Fin.castAdd C.complementRank i)=C.forms i :=
  NSP14.Homological.basisExtendingPrefix_apply C.forms C.independent i

theorem extendedHeadBasis_card : S.actualCutRank+C.complementRank=S.embeddingDimension-1 := by
  have hle := C.independent.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  have h := S.headDegree_one_finrank k
  unfold complementRank
  omega

noncomputable def extendedCoefficientEquiv :
    (Fin (S.actualCutRank+C.complementRank) → k) ≃ₗ[k] (S.NonXAtom → k) :=
  C.extendedHeadBasis.equivFun.symm.trans (S.headLinearCoordinates k)

noncomputable def extendedPolynomialEquiv :
    MvPolynomial (Fin (S.actualCutRank+C.complementRank)) k ≃ₐ[k] S.PolynomialRing k :=
  NSP14.Homological.polynomialLinearEquiv C.extendedCoefficientEquiv

/-- Invertible polynomial variable change, preserving each original selected
lambda as a literal polynomial, not merely preserving their span. -/
theorem extendedPolynomialEquiv_prefix (i : Fin S.actualCutRank) :
    C.extendedPolynomialEquiv (MvPolynomial.X (Fin.castAdd C.complementRank i))=C.polynomialForm i := by
  change NSP14.Homological.linearSubstitution C.extendedCoefficientEquiv.toLinearMap
    (MvPolynomial.X _)=_
  rw [NSP14.Homological.linearSubstitution_X]
  simp only [extendedCoefficientEquiv,LinearEquiv.coe_coe,LinearEquiv.trans_apply]
  simp only [Module.Basis.equivFun_symm_apply]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  rw [C.extendedHeadBasis_prefix]
  exact (S.linearFormPolynomial_eq k _).symm
end NSP14.NumericalSemigroup.LinearCutData
