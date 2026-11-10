module

public import NSP14.Semigroup.AperyStandard
public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

theorem qDegree_iSup_eq_top : (⨆ n, S.qDegree k n) = ⊤ := by
  apply top_unique
  intro a _
  have he := (S.aperyQuotientBasis k).linearCombination_repr a
  rw [← he, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (⨆ n, S.qDegree k n).sum_mem
  intro x _
  apply (⨆ n, S.qDegree k n).smul_mem
  apply le_iSup (S.qDegree k) (S.order x.val.val)
  exact (S.aperyQuotientBasis_eq_initial k x).symm ▸ S.qMonomial_mem_degree k x.val _ rfl

/-- Distinct inherited degrees have disjoint coefficient supports, even in arbitrary sums. -/
theorem qDegree_iSupIndep : iSupIndep (S.qDegree k) := by
  intro n
  apply disjoint_iff_inf_le.mpr
  rintro a ⟨han, hao⟩
  have hs : (⨆ p ≠ n, S.qDegree k p) ≤
      (Finsupp.supported k k {x : S.AperyExponent | S.order x.val.val ≠ n}).comap
        (S.aperyQuotientEquiv k).toLinearMap := by
    apply iSup₂_le
    intro p hpn b hb
    change S.aperyQuotientEquiv k b ∈ Finsupp.supported k k _
    rw [Finsupp.mem_supported']
    intro x hx
    have he : S.order x.val.val = n := Classical.not_not.mp hx
    have hne : S.order x.val.val ≠ p := by omega
    exact (Finsupp.mem_supported' k _).1 ((S.mem_qDegree_coordinates k p b).1 hb) x hne
  have ho := hs hao
  change a = 0
  apply (S.aperyQuotientEquiv k).injective
  ext x
  by_cases hx : S.order x.val.val = n
  · exact (Finsupp.mem_supported' k _).1 ho x (by exact fun h => h hx)
  · exact (Finsupp.mem_supported' k _).1 ((S.mem_qDegree_coordinates k n a).1 han) x hx

theorem qDegree_isInternal : DirectSum.IsInternal (S.qDegree k) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (S.qDegree_iSupIndep k) (S.qDegree_iSup_eq_top k)

noncomputable instance qDegreeGradedMonoid : SetLike.GradedMonoid (S.qDegree k) where
  one_mem := by
    have h := S.qMonomial_mem_degree k (0 : S.carrier) 0 S.order_zero
    simpa only [S.qMonomial_zero] using h
  mul_mem := fun _ _ _ _ ha hb => S.qDegree_mul_mem k ha hb

/-- Registered grading of the actual ring Q=A/N, using its inherited quotient-degree images. -/
noncomputable instance aperyGradedAlgebra : GradedAlgebra (R := k) (A := S.AperyAlgebra k) (S.qDegree k) :=
  DirectSum.IsInternal.gradedAlgebra (S.qDegree_isInternal k)

end NSP14.NumericalSemigroup
