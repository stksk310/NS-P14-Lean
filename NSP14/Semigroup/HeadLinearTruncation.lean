module
public import NSP14.Semigroup.HeadConstant
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem headGradeProject_high_zero (n : ℕ) (hn : n<2) (a : S.HeadAlgebra k)
    (ha : a ∈ S.highIdeal k 2) : S.headGradeProject k n a=0 := by
  apply (S.headQuotientEquiv k).injective
  ext h
  rw [S.headGradeProject_coordinates,map_zero,Finsupp.zero_apply]
  by_cases ho : S.order h.val.val=n
  · rw [ite_eq_left ho]
    exact (Finsupp.mem_supported' k _).mp ha h (by change ¬2 ≤ S.order h.val.val;omega)
  · exact ite_eq_right ho

noncomputable def headLinearPart : S.HeadAlgebra k →ₗ[k] S.headDegree k 1 :=
  (S.headGradeProject k 1).codRestrict (S.headDegree k 1) (S.headGradeProject_mem_degree k 1)

theorem headLinearPart_self (c : S.headDegree k 1) : S.headLinearPart k c.val=c :=
  Subtype.ext (S.headGradeProject_self k 1 c.val c.property)

theorem headLinearPart_high_zero (a : S.HeadAlgebra k) (ha : a ∈ S.highIdeal k 2) :
    S.headLinearPart k a=0 := Subtype.ext (S.headGradeProject_high_zero k 1 (by decide) a ha)

noncomputable def firstOrderLinearPart : S.FirstOrderHead k →ₗ[k] S.headDegree k 1 :=
  ((S.highIdeal k 2).restrictScalars k).liftQ (S.headLinearPart k)
    (by intro a ha;exact S.headLinearPart_high_zero k a ha)

theorem firstOrderLinearPart_mk (a : S.HeadAlgebra k) :
    S.firstOrderLinearPart k (Ideal.Quotient.mk (S.highIdeal k 2) a)=S.headLinearPart k a := rfl

theorem firstOrderLinearPart_linear (c : S.headDegree k 1) :
    S.firstOrderLinearPart k (Ideal.Quotient.mk (S.highIdeal k 2) c.val)=c := S.headLinearPart_self k c
end NSP14.NumericalSemigroup
