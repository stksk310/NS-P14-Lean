module

public import NSP14.Semigroup.AperyDegree

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def toHeadAlgebra : S.TangentAlgebra k →ₐ[k] S.HeadAlgebra k :=
  Ideal.Quotient.mkₐ k (S.xIdeal k)

noncomputable def headDegreeMap (n : ℕ) : S.GradedPiece k n →ₗ[k] S.HeadAlgebra k :=
  (S.toHeadAlgebra k).toLinearMap.comp (DirectSum.lof k ℕ (S.GradedPiece k) n)

noncomputable def headDegree (n : ℕ) : Submodule k (S.HeadAlgebra k) := (S.headDegreeMap k n).range

omit [Nontrivial k] in
theorem headMonomial_mem_degree (x : S.carrier) (n : ℕ) (h : S.order x.val = n) :
    S.headMonomial k x ∈ S.headDegree k n := by
  subst n
  exact ⟨S.monomialClass k (S.order x.val) x le_rfl, rfl⟩

theorem mem_headDegree_coordinates (n : ℕ) (a : S.HeadAlgebra k) : a ∈ S.headDegree k n ↔
    S.headQuotientEquiv k a ∈ Finsupp.supported k k {x : S.HeadExponent | S.order x.val.val = n} := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [Finsupp.mem_supported']
    intro x hx
    change S.headQuotientEquiv k (Ideal.Quotient.mk _ (DirectSum.of _ n b)) x = 0
    rw [S.headQuotientEquiv_mk]
    change S.tangentCoordinates k (DirectSum.of _ n b) x.val = 0
    rw [S.tangentCoordinates_apply, DirectSum.of_eq_of_ne _ _ _ hx, map_zero]
    rfl
  · intro ha
    have hsupport : ∀ x ∈ (S.headQuotientEquiv k a).support, S.order x.val.val = n :=
      (Finsupp.mem_supported k _).1 ha
    rw [← S.head_expansion k a, Finsupp.sum]
    apply (S.headDegree k n).sum_mem
    intro x hx
    apply (S.headDegree k n).smul_mem
    exact (S.headMonomial_eq_basis k x) ▸ S.headMonomial_mem_degree k x.val n (hsupport x hx)

/-- Projection onto a degree, expressed in the actual head basis. -/
noncomputable def headGradeProject (n : ℕ) : S.HeadAlgebra k →ₗ[k] S.HeadAlgebra k :=
  (S.headQuotientEquiv k).symm.toLinearMap.comp
    (((Finsupp.supported k k {x : S.HeadExponent | S.order x.val.val = n}).subtype.comp
      (Finsupp.restrictDom k k {x : S.HeadExponent | S.order x.val.val = n})).comp
      (S.headQuotientEquiv k).toLinearMap)

theorem headGradeProject_coordinates (n : ℕ) (a : S.HeadAlgebra k) (x : S.HeadExponent) :
    S.headQuotientEquiv k (S.headGradeProject k n a) x =
      if S.order x.val.val = n then S.headQuotientEquiv k a x else 0 := by
  simp [headGradeProject, Finsupp.restrictDom_apply, Finsupp.filter_apply]

theorem headGradeProject_mem_degree (n : ℕ) (a : S.HeadAlgebra k) :
    S.headGradeProject k n a ∈ S.headDegree k n := by
  rw [S.mem_headDegree_coordinates, Finsupp.mem_supported']
  intro x hx
  exact (S.headGradeProject_coordinates k n a x).trans
    (ite_eq_right_iff.mpr (fun h => (hx h).elim))

/-- N is homogeneous for the inherited degree decomposition of A. -/
theorem headGradeProject_mem_nonAperyIdeal (n : ℕ) (a : S.HeadAlgebra k)
    (ha : a ∈ S.nonAperyIdeal k) : S.headGradeProject k n a ∈ S.nonAperyIdeal k := by
  change S.headGradeProject k n a ∈ S.nonAperySpace k
  rw [S.mem_nonAperySpace]
  intro x hx
  rw [S.headGradeProject_coordinates]
  have hzero := (S.mem_nonAperySpace k a).1 ha x hx
  simp only [hzero, ite_self]

omit [Nontrivial k] in
theorem tangentCoordinates_of_ne (n : ℕ) (a : S.GradedPiece k n) (x : S.carrier)
    (h : S.order x.val ≠ n) : S.tangentCoordinates k (DirectSum.of _ n a) x = 0 := by
  rw [S.tangentCoordinates_apply, DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  rfl

/-- The coordinate projection is the projection induced from the actual G-component. -/
theorem headGradeProject_component (n : ℕ) (a : S.TangentAlgebra k) :
    S.headGradeProject k n (S.toHeadAlgebra k a) =
      S.toHeadAlgebra k (DirectSum.of (S.GradedPiece k) n (a n)) := by
  apply (S.headQuotientEquiv k).injective
  ext x
  rw [S.headGradeProject_coordinates]
  change (if S.order x.val.val = n then S.tangentCoordinates k a x.val else 0) =
    S.tangentCoordinates k (DirectSum.of _ n (a n)) x.val
  by_cases h : S.order x.val.val = n
  · subst n
    simp only [ite_true, S.tangentCoordinates_apply, DirectSum.of_eq_same]
  · exact (ite_eq_right_iff.mpr (fun he => (h he).elim)).trans
      (S.tangentCoordinates_of_ne k n (a n) x.val h).symm

theorem nonAperyHead_degree (x : S.NonAperyHeadExponent) : 3 ≤ S.order x.val.val.val := by
  have hh : S.NonAperyHead x.val.val.val := ⟨x.val.property, x.property⟩
  obtain ⟨t, ht, heq⟩ := S.head_predecessor hh
  simpa only [heq] using S.terminal_head_degree ht

end NSP14.NumericalSemigroup
