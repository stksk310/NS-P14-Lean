module

public import NSP14.Semigroup.AperyGradedAlgebra
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

theorem headDegree_iSup_eq_top : (⨆ n, S.headDegree k n) = ⊤ := by
  apply top_unique
  intro a _
  have he := (S.headBasis k).linearCombination_repr a
  rw [← he, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (⨆ n, S.headDegree k n).sum_mem
  intro x _
  apply (⨆ n, S.headDegree k n).smul_mem
  apply le_iSup (S.headDegree k) (S.order x.val.val)
  exact (S.headMonomial_eq_basis k x) ▸ S.headMonomial_mem_degree k x.val _ rfl

/-- Distinct inherited degrees have disjoint coefficient supports, even in arbitrary sums. -/
theorem headDegree_iSupIndep : iSupIndep (S.headDegree k) := by
  intro n
  apply disjoint_iff_inf_le.mpr
  rintro a ⟨han, hao⟩
  have hs : (⨆ p ≠ n, S.headDegree k p) ≤
      (Finsupp.supported k k {x : S.HeadExponent | S.order x.val.val ≠ n}).comap
        (S.headQuotientEquiv k).toLinearMap := by
    apply iSup₂_le
    intro p hpn b hb
    change S.headQuotientEquiv k b ∈ Finsupp.supported k k _
    rw [Finsupp.mem_supported']
    intro x hx
    have he : S.order x.val.val = n := Classical.not_not.mp hx
    have hne : S.order x.val.val ≠ p := by omega
    exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k p b).1 hb) x hne
  have ho := hs hao
  change a = 0
  apply (S.headQuotientEquiv k).injective
  ext x
  by_cases hx : S.order x.val.val = n
  · exact (Finsupp.mem_supported' k _).1 ho x (by exact fun h => h hx)
  · exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n a).1 han) x hx

theorem headDegree_isInternal : DirectSum.IsInternal (S.headDegree k) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (S.headDegree_iSupIndep k) (S.headDegree_iSup_eq_top k)


omit [Nontrivial k] in
theorem headDegree_mul_mem {n p : ℕ} {a b : S.HeadAlgebra k}
    (ha : a ∈ S.headDegree k n) (hb : b ∈ S.headDegree k p) : a * b ∈ S.headDegree k (n + p) := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  refine ⟨S.gradedMul k n p f g, ?_⟩
  change S.toHeadAlgebra k (DirectSum.of _ (n + p) (S.gradedMul k n p f g)) =
    S.toHeadAlgebra k (DirectSum.of _ n f) * S.toHeadAlgebra k (DirectSum.of _ p g)
  rw [← S.tangent_of_mul, map_mul]

noncomputable instance headDegreeGradedMonoid : SetLike.GradedMonoid (S.headDegree k) where
  one_mem := by
    have h := S.headMonomial_mem_degree k (0 : S.carrier) 0 S.order_zero
    simpa only [headMonomial, S.initialMonomial_zero, map_one] using h
  mul_mem := fun _ _ _ _ ha hb => S.headDegree_mul_mem k ha hb

noncomputable instance headGradedAlgebra :
    GradedAlgebra (R := k) (A := S.HeadAlgebra k) (S.headDegree k) :=
  DirectSum.IsInternal.gradedAlgebra (S.headDegree_isInternal k)

theorem headGradeProject_self (n : ℕ) (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k n) :
    S.headGradeProject k n a = a := by
  apply (S.headQuotientEquiv k).injective
  ext x
  have hc := S.headGradeProject_coordinates k n a x
  by_cases hx : S.order x.val.val = n
  · exact hc.trans (ite_eq_left hx)
  · have hz := (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n a).1 ha) x hx
    exact hc.trans ((ite_eq_right_iff.mpr (fun h => (hx h).elim)).trans hz.symm)

theorem headGradeProject_other (n p : ℕ) (hpn : p ≠ n) (a : S.HeadAlgebra k)
    (ha : a ∈ S.headDegree k p) : S.headGradeProject k n a = 0 := by
  apply (S.headQuotientEquiv k).injective
  ext x
  have hc := S.headGradeProject_coordinates k n a x
  by_cases hx : S.order x.val.val = n
  · have hxp : S.order x.val.val ≠ p := by omega
    have hz := (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k p a).1 ha) x hxp
    exact hc.trans ((ite_eq_left hx).trans hz)
  · exact hc.trans (ite_eq_right_iff.mpr (fun h => (hx h).elim))

/-- The explicit coordinate filter equals mathlib's projection for the registered inherited grading. -/
theorem headGradeProject_eq_proj (n : ℕ) : S.headGradeProject k n =
    GradedAlgebra.proj (R := k) (A := S.HeadAlgebra k) (S.headDegree k) n := by
  apply (S.headBasis k).ext
  intro x
  have hx : S.headBasis k x ∈ S.headDegree k (S.order x.val.val) :=
    (S.headMonomial_eq_basis k x) ▸ S.headMonomial_mem_degree k x.val _ rfl
  change S.headGradeProject k n (S.headBasis k x) =
    (DirectSum.decompose (S.headDegree k) (S.headBasis k x) n : S.HeadAlgebra k)
  by_cases h : S.order x.val.val = n
  · subst n
    exact (S.headGradeProject_self k _ _ hx).trans
      (DirectSum.decompose_of_mem_same (S.headDegree k) hx).symm
  · exact (S.headGradeProject_other k n _ h _ hx).trans
      (DirectSum.decompose_of_mem_ne (S.headDegree k) hx h).symm

theorem nonAperyIdeal_isHomogeneous : (S.nonAperyIdeal k).IsHomogeneous (S.headDegree k) := by
  intro n a ha
  change GradedAlgebra.proj (R := k) (A := S.HeadAlgebra k) (S.headDegree k) n a ∈ S.nonAperyIdeal k
  rw [← S.headGradeProject_eq_proj]
  exact S.headGradeProject_mem_nonAperyIdeal k n a ha

end NSP14.NumericalSemigroup
