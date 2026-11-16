module
public import NSP14.Semigroup.HeadFirstOrderCoordinates
public import NSP14.Semigroup.CutAugmentation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def headConstant : S.HeadAlgebra k →ₗ[k] k :=
  (Finsupp.lapply S.zeroHeadExponent).comp (S.headQuotientEquiv k).toLinearMap

theorem headBasis_zero : S.headBasis k S.zeroHeadExponent=1 := by
  rw [S.headBasis_eq_initial]
  change Ideal.Quotient.mk (S.xIdeal k) (S.initialMonomial k (0 : S.carrier))=1
  rw [S.initialMonomial_zero,map_one]

theorem headBasis_coordinates (h : S.HeadExponent) :
    S.headQuotientEquiv k (S.headBasis k h)=Finsupp.single h 1 :=
  (S.headQuotientEquiv k).apply_symm_apply (Finsupp.single h 1)

theorem headConstant_one : S.headConstant k 1=1 := by
  rw [← S.headBasis_zero k]
  change S.headQuotientEquiv k (S.headBasis k S.zeroHeadExponent) S.zeroHeadExponent=1
  rw [S.headBasis_coordinates]
  simp

theorem headConstant_high_zero (a : S.HeadAlgebra k) (ha : a ∈ S.highIdeal k 2) : S.headConstant k a=0 := by
  exact (Finsupp.mem_supported' k _).mp ha S.zeroHeadExponent
    (by change ¬2 ≤ S.order 0;rw [S.order_zero];decide)

theorem head_order_zero_eq (h : S.HeadExponent) (hh : S.order h.val.val=0) : h=S.zeroHeadExponent := by
  apply Subtype.ext
  apply Subtype.ext
  exact (S.order_eq_zero_iff h.val.property).mp hh

theorem headGradeProject_zero_eq (a : S.HeadAlgebra k) :
    S.headGradeProject k 0 a=S.headConstant k a • (1 : S.HeadAlgebra k) := by
  apply (S.headQuotientEquiv k).injective
  ext h
  rw [S.headGradeProject_coordinates,map_smul,← S.headBasis_zero k,S.headBasis_coordinates]
  by_cases hh : S.order h.val.val=0
  · have he := S.head_order_zero_eq h hh
    subst h
    simp only [Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one]
    rfl
  · have he : S.zeroHeadExponent ≠ h := by
      intro hz
      subst h
      exact hh S.order_zero
    simp [hh,he]

theorem head_positivePart (a : S.HeadAlgebra k) :
    a-S.headConstant k a • (1 : S.HeadAlgebra k) ∈ S.highSpace k 1 := by
  rw [← S.headGradeProject_zero_eq k a]
  change S.headQuotientEquiv k (a-S.headGradeProject k 0 a) ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro h hn
  change ¬1 ≤ S.order h.val.val at hn
  have hh : S.order h.val.val=0 := by omega
  rw [map_sub,Finsupp.sub_apply,S.headGradeProject_coordinates,ite_eq_left hh,sub_self]

theorem headLinear_mul_mod_high (c : S.headDegree k 1) (a : S.HeadAlgebra k) :
    Ideal.Quotient.mkₐ k (S.highIdeal k 2) (c.val*a)=
      S.headConstant k a • Ideal.Quotient.mkₐ k (S.highIdeal k 2) c.val := by
  have hm : c.val*(a-S.headConstant k a • (1 : S.HeadAlgebra k)) ∈ S.highIdeal k 2 :=
    S.form_mul_highSpace k 1 c (a-S.headConstant k a • (1 : S.HeadAlgebra k)) (S.head_positivePart k a)
  have hz : Ideal.Quotient.mkₐ k (S.highIdeal k 2) (c.val*(a-S.headConstant k a • (1 : S.HeadAlgebra k)))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [mul_sub,mul_smul_comm,mul_one,map_sub,map_smul] at hz
  exact sub_eq_zero.mp hz

noncomputable def firstOrderConstant : S.FirstOrderHead k →ₗ[k] k :=
  ((S.highIdeal k 2).restrictScalars k).liftQ (S.headConstant k)
    (by intro a ha;exact S.headConstant_high_zero k a ha)

theorem firstOrderConstant_mk (a : S.HeadAlgebra k) :
    S.firstOrderConstant k (Ideal.Quotient.mk (S.highIdeal k 2) a)=S.headConstant k a := rfl

theorem firstOrderConstant_one : S.firstOrderConstant k 1=1 := by
  exact S.headConstant_one k
end NSP14.NumericalSemigroup
