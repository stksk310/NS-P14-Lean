module
public import NSP14.Homological.StandardMonomials
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
@[expose] public section
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k]

theorem normal_component (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k))
    (n : ℕ) (r : normalSpace m I) : MvPolynomial.homogeneousComponent n r.val∈normalSpace m I := by
  change (MvPolynomial.homogeneousComponent n r.val).coeff∈Finsupp.supported k k (StandardExponent m I)
  rw [Finsupp.mem_supported]
  intro β hβ
  have hb : β∈r.val.support := by
    change β∈(MvPolynomial.homogeneousComponent n r.val).support at hβ
    rw [MvPolynomial.support_homogeneousComponent] at hβ
    exact (Finset.mem_filter.mp hβ).1
  exact (Finsupp.mem_supported k _).mp r.property hb

/-- Actual division preserves the degree for every homogeneous ideal. -/
theorem normal_homogeneous [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (f : MvPolynomial σ k) (hf : f.IsHomogeneous n)
    (r : normalSpace MonomialOrder.degLex I) (hr : f-r.val∈I) : r.val.IsHomogeneous n := by
  have hc := MvPolynomial.homogeneousComponent_mem_of_mem hI hr n
  rw [map_sub,MvPolynomial.homogeneousComponent_eq_self hf] at hc
  have hi : r.val-MvPolynomial.homogeneousComponent n r.val∈I := by
    have := I.sub_mem hc hr
    convert this using 1; abel
  have hz := normal_in_ideal_eq_zero MonomialOrder.degLex I _
    ((normalSpace MonomialOrder.degLex I).sub_mem r.property (normal_component k σ _ I n r)) hi
  have he : r.val=MvPolynomial.homogeneousComponent n r.val := sub_eq_zero.mp hz
  rw [he]
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
end NSP14.Endpoint
