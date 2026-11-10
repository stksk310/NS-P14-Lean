module

public import NSP14.Semigroup.HeadDegree

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

theorem headDegree_to_qDegree (n : ℕ) (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k n) :
    Ideal.Quotient.mk (S.nonAperyIdeal k) a ∈ S.qDegree k n := by
  obtain ⟨f, rfl⟩ := ha
  exact ⟨f, rfl⟩

noncomputable def headToQDegree (n : ℕ) : S.headDegree k n →ₗ[k] S.qDegree k n where
  toFun a := ⟨Ideal.Quotient.mk (S.nonAperyIdeal k) a.val, S.headDegree_to_qDegree k n a.val a.property⟩
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r a := by
    apply Subtype.ext
    exact (Ideal.Quotient.mkₐ k (S.nonAperyIdeal k)).toLinearMap.map_smul r a.val

theorem headToQDegree_surjective (n : ℕ) : Function.Surjective (S.headToQDegree k n) := by
  intro a
  obtain ⟨f, hf⟩ := a.property
  refine ⟨⟨S.headDegreeMap k n f, ⟨f, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hf

/-- Non-Apéry heads start in degree three, so N has no inherited degree ≤2. -/
theorem lowDegree_nonApery_eq_zero (n : ℕ) (hn : n ≤ 2) (a : S.HeadAlgebra k)
    (ha : a ∈ S.headDegree k n) (hN : a ∈ S.nonAperyIdeal k) : a = 0 := by
  apply (S.headQuotientEquiv k).injective
  ext x
  by_cases hx : x.val.val ∈ S.aperySet
  · exact (S.mem_nonAperySpace k a).1 hN x hx
  · have hbound := S.nonAperyHead_degree (⟨x, hx⟩ : S.NonAperyHeadExponent)
    change 3 ≤ S.order x.val.val at hbound
    have hne : S.order x.val.val ≠ n := by omega
    exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n a).1 ha) x hne

theorem headToQDegree_injective (n : ℕ) (hn : n ≤ 2) : Function.Injective (S.headToQDegree k n) := by
  intro a b h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply S.lowDegree_nonApery_eq_zero k n hn (a.val - b.val)
    ((S.headDegree k n).sub_mem a.property b.property)
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (S.nonAperyIdeal k) a.val = Ideal.Quotient.mk (S.nonAperyIdeal k) b.val at he
  rw [map_sub, he, sub_self]

/-- A_n→Q_n is the actual quotient map and is an isomorphism for n=0,1,2. -/
noncomputable def lowDegreeQuotientEquiv (n : ℕ) (hn : n ≤ 2) :
    S.headDegree k n ≃ₗ[k] S.qDegree k n :=
  LinearEquiv.ofBijective (S.headToQDegree k n)
    ⟨S.headToQDegree_injective k n hn, S.headToQDegree_surjective k n⟩

end NSP14.NumericalSemigroup
