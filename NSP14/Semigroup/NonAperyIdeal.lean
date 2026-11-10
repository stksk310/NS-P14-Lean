module

public import NSP14.Semigroup.HeadMonomials

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- The subspace of A supported on its non-Apéry head coordinates. -/
noncomputable def nonAperySpace : Submodule k (S.HeadAlgebra k) :=
  (Finsupp.supported k k {x : S.HeadExponent | x.val.val ∉ S.aperySet}).comap
    (S.headQuotientEquiv k).toLinearMap

theorem mem_nonAperySpace (a : S.HeadAlgebra k) : a ∈ S.nonAperySpace k ↔
    ∀ x : S.HeadExponent, x.val.val ∈ S.aperySet → S.headQuotientEquiv k a x = 0 := by
  classical
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k _ ↔ _
  rw [Finsupp.mem_supported']
  simp only [Set.mem_ofPred_eq, not_not]

theorem headMonomial_mem_nonAperySpace (x : S.carrier) (hx : x.val ∉ S.aperySet) :
    S.headMonomial k x ∈ S.nonAperySpace k := by
  classical
  rw [S.mem_nonAperySpace]
  intro y hy
  rw [S.headMonomial_coordinates]
  have hxy : x ≠ y.val := by intro he; exact hx (he ▸ hy)
  simp [hxy]

theorem headBasis_mul_mem_nonAperySpace (x y : S.HeadExponent)
    (hy : y.val.val ∉ S.aperySet) : S.headBasis k x * S.headBasis k y ∈ S.nonAperySpace k := by
  rw [← S.headMonomial_eq_basis k x, ← S.headMonomial_eq_basis k y]
  by_cases h : S.order (x.val.val + y.val.val) = S.order x.val.val + S.order y.val.val
  · rw [S.headMonomial_mul_live k _ _ h]
    exact S.headMonomial_mem_nonAperySpace k _ (S.nonapery_add x.val y.val hy)
  · have ho := S.order_add x.val.property y.val.property
    have hlt : S.order x.val.val + S.order y.val.val < S.order (x.val.val + y.val.val) := by omega
    rw [S.headMonomial_mul_dead k _ _ hlt]
    exact (S.nonAperySpace k).zero_mem

/-- Stability under every element of A, including arbitrary coefficient combinations. -/
theorem nonAperySpace_mul (r a : S.HeadAlgebra k) (ha : a ∈ S.nonAperySpace k) :
    r * a ∈ S.nonAperySpace k := by
  classical
  have hsupport : ∀ y ∈ (S.headQuotientEquiv k a).support, y.val.val ∉ S.aperySet := by
    exact (Finsupp.mem_supported k _).1 ha
  rw [← S.head_expansion k r, Finsupp.sum, Finset.sum_mul]
  apply (S.nonAperySpace k).sum_mem
  intro x _
  rw [← S.head_expansion k a, Finsupp.sum, Finset.mul_sum]
  apply (S.nonAperySpace k).sum_mem
  intro y hy
  have hm := S.headBasis_mul_mem_nonAperySpace k x y (hsupport y hy)
  simpa only [smul_mul_assoc, mul_smul_comm] using
    (S.nonAperySpace k).smul_mem (S.headQuotientEquiv k a y)
      ((S.nonAperySpace k).smul_mem (S.headQuotientEquiv k r x) hm)

/-- N is an actual ideal of the whole ring A=G/xG. -/
noncomputable def nonAperyIdeal : Ideal (S.HeadAlgebra k) where
  carrier := S.nonAperySpace k
  zero_mem' := (S.nonAperySpace k).zero_mem
  add_mem' := (S.nonAperySpace k).add_mem
  smul_mem' r a ha := S.nonAperySpace_mul k r a ha

theorem nonAperyIdeal_restrictScalars : (S.nonAperyIdeal k).restrictScalars k = S.nonAperySpace k := rfl

def NonAperyHeadExponent := {x : S.HeadExponent // x.val.val ∉ S.aperySet}

noncomputable def nonAperyIdealEquiv :
    (S.nonAperyIdeal k).restrictScalars k ≃ₗ[k] (S.NonAperyHeadExponent →₀ k) where
  toFun a := Finsupp.subtypeDomain _ (S.headQuotientEquiv k a.val)
  invFun f := ⟨(S.headQuotientEquiv k).symm f.extendDomain, by
    change S.headQuotientEquiv k ((S.headQuotientEquiv k).symm f.extendDomain) ∈
      Finsupp.supported k k {x : S.HeadExponent | x.val.val ∉ S.aperySet}
    rw [LinearEquiv.apply_symm_apply]
    exact f.support_extendDomain_subset⟩
  left_inv a := by
    apply Subtype.ext
    apply (S.headQuotientEquiv k).injective
    rw [LinearEquiv.apply_symm_apply, Finsupp.extendDomain_subtypeDomain]
    exact (Finsupp.mem_supported k _).1 a.property
  right_inv f := by
    change Finsupp.subtypeDomain _ (S.headQuotientEquiv k ((S.headQuotientEquiv k).symm f.extendDomain)) = f
    rw [LinearEquiv.apply_symm_apply]
    exact Finsupp.subtypeDomain_extendDomain f
  map_add' a b := by
    simp only [Submodule.coe_add, map_add, Finsupp.subtypeDomain_add]
    rfl
  map_smul' r a := by
    ext y
    change S.headQuotientEquiv k (r • a.val) y.val = r • S.headQuotientEquiv k a.val y.val
    rw [map_smul]
    rfl

noncomputable def nonAperyIdealBasis :
    Module.Basis S.NonAperyHeadExponent k ((S.nonAperyIdeal k).restrictScalars k) :=
  Finsupp.basisSingleOne.map (S.nonAperyIdealEquiv k).symm

end NSP14.NumericalSemigroup
