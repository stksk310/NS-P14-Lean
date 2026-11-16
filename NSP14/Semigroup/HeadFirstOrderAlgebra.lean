module
public import NSP14.Semigroup.HeadFirstOrderSplit
public import Mathlib.Algebra.TrivSqZeroExt.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

private theorem native_mul_one (a : S.FirstOrderHead k) : a*1=a := mul_one a
private theorem native_one_mul (a : S.FirstOrderHead k) : 1*a=a := one_mul a
private theorem native_smul_add (c : k) (a b : S.FirstOrderHead k) : c • (a+b)=c • a+c • b := smul_add c a b
private theorem native_smul_smul (c d : k) (a : S.FirstOrderHead k) : c • (d • a)=(c*d) • a := smul_smul c d a

theorem firstOrderHead_mul_expansion (a b : S.FirstOrderHead k) :
    a*b=(S.firstOrderConstant k a*S.firstOrderConstant k b) • (1 : S.FirstOrderHead k)+
      S.firstOrderConstant k a • Ideal.Quotient.mk (S.highIdeal k 2) (S.firstOrderLinearPart k b).val+
      S.firstOrderConstant k b • Ideal.Quotient.mk (S.highIdeal k 2) (S.firstOrderLinearPart k a).val := by
  conv_lhs => rw [S.firstOrderHead_decompose k a,S.firstOrderHead_decompose k b]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,native_one_mul,native_mul_one,
    S.firstOrder_linear_mul_zero,add_zero,native_smul_add,native_smul_smul]
  rw [mul_comm (S.firstOrderConstant k b) (S.firstOrderConstant k a)]
  abel

theorem firstOrderConstant_mul (a b : S.FirstOrderHead k) :
    S.firstOrderConstant k (a*b)=S.firstOrderConstant k a*S.firstOrderConstant k b := by
  rw [S.firstOrderHead_mul_expansion]
  simp only [map_add,map_smul,S.firstOrderConstant_one,S.firstOrderConstant_linear_zero,
    smul_eq_mul,mul_one,mul_zero,add_zero]

theorem firstOrderLinearPart_mul (a b : S.FirstOrderHead k) :
    S.firstOrderLinearPart k (a*b)=S.firstOrderConstant k a • S.firstOrderLinearPart k b+
      S.firstOrderConstant k b • S.firstOrderLinearPart k a := by
  rw [S.firstOrderHead_mul_expansion]
  simp only [map_add,map_smul,S.firstOrderLinearPart_one,S.firstOrderLinearPart_linear,
    smul_zero,zero_add]

noncomputable def firstOrderHeadTrivLinearEquiv :
    S.FirstOrderHead k ≃ₗ[k] TrivSqZeroExt k (S.NonXAtom → k) :=
  (S.firstOrderHeadSplit k).trans (LinearEquiv.prodCongr (LinearEquiv.refl k k) (S.headLinearCoordinates k))

theorem firstOrderHeadTrivLinearEquiv_one : S.firstOrderHeadTrivLinearEquiv k 1=1 := by
  apply TrivSqZeroExt.ext
  · exact S.firstOrderConstant_one k
  · change S.headLinearCoordinates k (S.firstOrderLinearPart k 1)=0
    rw [S.firstOrderLinearPart_one,map_zero]

theorem firstOrderHeadTrivLinearEquiv_mul (a b : S.FirstOrderHead k) :
    S.firstOrderHeadTrivLinearEquiv k (a*b)=S.firstOrderHeadTrivLinearEquiv k a*S.firstOrderHeadTrivLinearEquiv k b := by
  apply TrivSqZeroExt.ext
  · exact S.firstOrderConstant_mul k a b
  · change S.headLinearCoordinates k (S.firstOrderLinearPart k (a*b))=_
    rw [TrivSqZeroExt.snd_mul,op_smul_eq_smul,S.firstOrderLinearPart_mul,map_add,map_smul,map_smul]
    rfl

/-- The actual truncated head algebra is a square-zero extension of the
actual first-degree space, with its multiplication and coefficient field. -/
noncomputable def firstOrderHeadTrivEquiv :
    S.FirstOrderHead k ≃ₐ[k] TrivSqZeroExt k (S.NonXAtom → k) :=
  AlgEquiv.ofLinearEquiv (S.firstOrderHeadTrivLinearEquiv k)
    (S.firstOrderHeadTrivLinearEquiv_one k) (S.firstOrderHeadTrivLinearEquiv_mul k)
end NSP14.NumericalSemigroup
