module
public import NSP14.Semigroup.HeadLinearTruncation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem head_remainder_high (a : S.HeadAlgebra k) :
    a-S.headGradeProject k 0 a-S.headGradeProject k 1 a ∈ S.highIdeal k 2 := by
  change S.headQuotientEquiv k (a-S.headGradeProject k 0 a-S.headGradeProject k 1 a) ∈
    Finsupp.supported k k {h : S.HeadExponent | 2 ≤ S.order h.val.val}
  rw [Finsupp.mem_supported']
  intro h hn
  change ¬2 ≤ S.order h.val.val at hn
  rw [map_sub,map_sub,Finsupp.sub_apply,Finsupp.sub_apply,S.headGradeProject_coordinates,S.headGradeProject_coordinates]
  by_cases ho : S.order h.val.val=0
  · simp [ho]
  · have h1 : S.order h.val.val=1 := by omega
    simp [h1]

theorem firstOrderHead_decompose (a : S.FirstOrderHead k) :
    a=S.firstOrderConstant k a • (1 : S.FirstOrderHead k)+
      Ideal.Quotient.mk (S.highIdeal k 2) (S.firstOrderLinearPart k a).val := by
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  have hz : Ideal.Quotient.mkₐ k (S.highIdeal k 2)
      (b-S.headGradeProject k 0 b-S.headGradeProject k 1 b)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (S.head_remainder_high k b)
  rw [map_sub,map_sub,sub_sub] at hz
  have he := sub_eq_zero.mp hz
  rw [S.headGradeProject_zero_eq,map_smul,map_one] at he
  exact he

theorem headConstant_linear_zero (c : S.headDegree k 1) : S.headConstant k c.val=0 := by
  exact (Finsupp.mem_supported' k _).mp ((S.mem_headDegree_coordinates k 1 c.val).mp c.property)
    S.zeroHeadExponent (by change S.order 0 ≠ 1;rw [S.order_zero];decide)

theorem firstOrderConstant_linear_zero (c : S.headDegree k 1) :
    S.firstOrderConstant k (Ideal.Quotient.mk (S.highIdeal k 2) c.val)=0 := S.headConstant_linear_zero k c

theorem headLinearPart_one : S.headLinearPart k 1=0 := by
  apply Subtype.ext
  apply S.headGradeProject_other k 1 0 (by decide) 1
  have h := S.headMonomial_mem_degree k (0 : S.carrier) 0 S.order_zero
  simpa only [headMonomial,S.initialMonomial_zero,map_one] using h

theorem firstOrderLinearPart_one : S.firstOrderLinearPart k 1=0 := S.headLinearPart_one k

noncomputable def firstOrderHeadSplit : S.FirstOrderHead k ≃ₗ[k] (k × S.headDegree k 1) where
  toLinearMap := (S.firstOrderConstant k).prod (S.firstOrderLinearPart k)
  invFun a := a.1 • (1 : S.FirstOrderHead k)+Ideal.Quotient.mk (S.highIdeal k 2) a.2.val
  left_inv a := (S.firstOrderHead_decompose k a).symm
  right_inv a := by
    apply Prod.ext
    · change S.firstOrderConstant k (a.1 • (1 : S.FirstOrderHead k)+Ideal.Quotient.mk (S.highIdeal k 2) a.2.val)=a.1
      rw [map_add,map_smul,S.firstOrderConstant_one,S.firstOrderConstant_linear_zero,smul_eq_mul,mul_one,add_zero]
    · change S.firstOrderLinearPart k (a.1 • (1 : S.FirstOrderHead k)+Ideal.Quotient.mk (S.highIdeal k 2) a.2.val)=a.2
      rw [map_add,map_smul,S.firstOrderLinearPart_one,S.firstOrderLinearPart_linear,smul_zero,zero_add]

theorem firstOrder_linear_mul_zero (a b : S.headDegree k 1) :
    Ideal.Quotient.mk (S.highIdeal k 2) a.val*Ideal.Quotient.mk (S.highIdeal k 2) b.val=0 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact S.headDegree_le_highSpace k 2 2 le_rfl (S.headDegree_mul_mem k (n:=1) (p:=1) a.property b.property)
end NSP14.NumericalSemigroup
