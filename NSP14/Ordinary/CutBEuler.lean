module
public import NSP14.Ordinary.CutFirstOrder
public import NSP14.Semigroup.HeadLinearTruncation
public import NSP14.Homological.SquareZeroEuler
public import NSP14.Ordinary.TargetMargin
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological NSP14.Ordinary
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutBUnit : coefficientModule k (Fin S.actualCutRank) C.cutB :=
  C.cutBCoefficientEquiv.symm 1
noncomputable def cutBConstant : coefficientModule k (Fin S.actualCutRank) C.cutB →ₗ[k] k :=
  (S.firstOrderConstant k).comp C.cutBCoefficientEquiv.toLinearMap
noncomputable def cutBLinearCoordinate (v : Fin S.actualCutRank) :
    coefficientModule k (Fin S.actualCutRank) C.cutB →ₗ[k] k :=
  ((C.extendedHeadBasis.coord (Fin.castAdd C.complementRank v)).comp (S.firstOrderLinearPart k)).comp
    C.cutBCoefficientEquiv.toLinearMap

theorem cutB_variable (v : Fin S.actualCutRank) (a : coefficientModule k (Fin S.actualCutRank) C.cutB) :
    C.cutBCoefficientEquiv ((MvPolynomial.X v : S.CutPolynomialRing k) • a)=
      Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val*C.cutBCoefficientEquiv a := by
  change (show S.FirstOrderHead k from (MvPolynomial.X v : S.CutPolynomialRing k) • (show C.cutB from a))=
    Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val*(show S.FirstOrderHead k from a)
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective (show S.FirstOrderHead k from a)
  rw [C.cutB_X_mk,map_mul]

theorem cutB_variable_unit (v : Fin S.actualCutRank) :
    C.cutBCoefficientEquiv ((MvPolynomial.X v : S.CutPolynomialRing k) • C.cutBUnit)=
      Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val := by
  rw [C.cutB_variable]
  change Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val*(1 : S.FirstOrderHead k)=_
  exact mul_one (Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val)

theorem cutB_rankOne (v : Fin S.actualCutRank) (a : coefficientModule k (Fin S.actualCutRank) C.cutB) :
    (MvPolynomial.X v : S.CutPolynomialRing k) • a=
      C.cutBConstant a • ((MvPolynomial.X v : S.CutPolynomialRing k) • C.cutBUnit) := by
  apply C.cutBCoefficientEquiv.injective
  rw [C.cutB_variable,map_smul,C.cutB_variable_unit]
  change Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val*C.cutBCoefficientEquiv a=
    S.firstOrderConstant k (C.cutBCoefficientEquiv a) •
      Ideal.Quotient.mk (S.highIdeal k 2) (C.forms v).val
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective (C.cutBCoefficientEquiv a)
  rw [← hb,← map_mul,S.firstOrderConstant_mk]
  exact S.headLinear_mul_mod_high k (C.forms v) b

theorem cutB_independent (v w : Fin S.actualCutRank) :
    C.cutBLinearCoordinate v ((MvPolynomial.X w : S.CutPolynomialRing k) • C.cutBUnit)=
      if v=w then 1 else 0 := by
  change C.extendedHeadBasis.coord (Fin.castAdd C.complementRank v)
    (S.firstOrderLinearPart k (C.cutBCoefficientEquiv ((MvPolynomial.X w : S.CutPolynomialRing k) • C.cutBUnit)))=_
  rw [C.cutB_variable_unit]
  rw [S.firstOrderLinearPart_linear,← C.extendedHeadBasis_prefix w]
  by_cases he : v=w
  · subst w;simp
  · simp [he]

theorem cutBEuler_eq (j : ℕ) : C.cutBEuler j=
    ((S.actualCutRank-1).choose j : ℤ)*S.embeddingDimension-(S.actualCutRank.choose (j+1) : ℤ) := by
  let := C.cutB_finite
  let := C.cutB_coefficientFinite
  unfold cutBEuler
  rw [squareZero_bettiEuler k (Fin S.actualCutRank) C.cutB C.cutBUnit C.cutBConstant C.cutB_rankOne
    C.cutBLinearCoordinate (by intro v w;by_cases h : v=w <;> simpa [h] using C.cutB_independent v w)
    (by simpa only [Fintype.card_fin] using (show 1 ≤ S.actualCutRank by have := S.actualCutRank_two_le;omega)),
    Fintype.card_fin,C.cutB_length]

theorem cutBEuler_lower (j : ℕ) : (C.cutBEuler j : ℚ)=TargetMargin.lower S.embeddingDimension S.actualCutRank j := by
  rw [C.cutBEuler_eq]
  push_cast
  unfold TargetMargin.lower
  have hp := Nat.choose_succ_succ (S.actualCutRank-1) j
  change (S.actualCutRank-1+1).choose (j+1)=(S.actualCutRank-1).choose j+(S.actualCutRank-1).choose (j+1) at hp
  rw [Nat.sub_add_cancel (show 1 ≤ S.actualCutRank by have := S.actualCutRank_two_le;omega)] at hp
  have hq : (S.actualCutRank.choose (j+1) : ℚ)=
      ((S.actualCutRank-1).choose j : ℚ)+((S.actualCutRank-1).choose (j+1) : ℚ) := by exact_mod_cast hp
  rw [hq]
  ring
end NSP14.NumericalSemigroup.LinearCutData
