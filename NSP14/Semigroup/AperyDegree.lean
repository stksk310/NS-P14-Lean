module

public import NSP14.Semigroup.AperyQuotient

@[expose] public section

open scoped Classical BigOperators DirectSum

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- The actual composite quotient homomorphism G→A→Q. -/
noncomputable def toAperyAlgebra : S.TangentAlgebra k →ₐ[k] S.AperyAlgebra k :=
  (Ideal.Quotient.mkₐ k (S.nonAperyIdeal k)).comp (Ideal.Quotient.mkₐ k (S.xIdeal k))

theorem toAperyAlgebra_initial (x : S.carrier) :
    S.toAperyAlgebra k (S.initialMonomial k x) = S.qMonomial k x := rfl

theorem toAperyAlgebra_coordinates (a : S.TangentAlgebra k) (x : S.AperyExponent) :
    S.aperyQuotientEquiv k (S.toAperyAlgebra k a) x = S.tangentCoordinates k a x.val := by
  change S.aperyQuotientEquiv k (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) x = _
  rw [S.aperyQuotientEquiv_mk]
  exact (S.aperyProjection_apply k _ x).trans (by rw [S.headQuotientEquiv_mk]; rfl)

noncomputable def qDegreeMap (n : ℕ) : S.GradedPiece k n →ₗ[k] S.AperyAlgebra k :=
  (S.toAperyAlgebra k).toLinearMap.comp (DirectSum.lof k ℕ (S.GradedPiece k) n)

/-- Degrees in Q are the actual images of the ideal-power homogeneous pieces. -/
noncomputable def qDegree (n : ℕ) : Submodule k (S.AperyAlgebra k) := (S.qDegreeMap k n).range

theorem qMonomial_mem_degree (x : S.carrier) (n : ℕ) (h : S.order x.val = n) :
    S.qMonomial k x ∈ S.qDegree k n := by
  subst n
  exact ⟨S.monomialClass k (S.order x.val) x le_rfl, rfl⟩

theorem mem_qDegree_coordinates (n : ℕ) (a : S.AperyAlgebra k) : a ∈ S.qDegree k n ↔
    S.aperyQuotientEquiv k a ∈ Finsupp.supported k k
      {x : S.AperyExponent | S.order x.val.val = n} := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [Finsupp.mem_supported']
    intro x hx
    change S.aperyQuotientEquiv k (S.toAperyAlgebra k (DirectSum.of _ n b)) x = 0
    rw [S.toAperyAlgebra_coordinates, S.tangentCoordinates_apply,
      DirectSum.of_eq_of_ne _ _ _ hx, map_zero]
    rfl
  · intro ha
    have hsupport : ∀ x ∈ (S.aperyQuotientEquiv k a).support, S.order x.val.val = n :=
      (Finsupp.mem_supported k _).1 ha
    have hex := (S.aperyQuotientBasis k).linearCombination_repr a
    change (S.aperyQuotientEquiv k a).sum (fun x c => c • S.aperyQuotientBasis k x) = a at hex
    rw [← hex, Finsupp.sum]
    apply (S.qDegree k n).sum_mem
    intro x hx
    apply (S.qDegree k n).smul_mem
    exact (S.aperyQuotientBasis_eq_initial k x).symm ▸ S.qMonomial_mem_degree k x.val n (hsupport x hx)

def AperyDegreeExponent (n : ℕ) := {x : S.AperyExponent // S.order x.val.val = n}

noncomputable def qDegreeEquiv (n : ℕ) : S.qDegree k n ≃ₗ[k] (S.AperyDegreeExponent n →₀ k) where
  toFun a := Finsupp.subtypeDomain _ (S.aperyQuotientEquiv k a.val)
  invFun f := ⟨(S.aperyQuotientEquiv k).symm f.extendDomain, by
    rw [S.mem_qDegree_coordinates, LinearEquiv.apply_symm_apply]
    exact f.support_extendDomain_subset⟩
  left_inv a := by
    apply Subtype.ext
    apply (S.aperyQuotientEquiv k).injective
    rw [LinearEquiv.apply_symm_apply, Finsupp.extendDomain_subtypeDomain]
    exact (Finsupp.mem_supported k _).1 ((S.mem_qDegree_coordinates k n a.val).1 a.property)
  right_inv f := by
    change Finsupp.subtypeDomain _ (S.aperyQuotientEquiv k ((S.aperyQuotientEquiv k).symm f.extendDomain)) = f
    rw [LinearEquiv.apply_symm_apply]
    exact Finsupp.subtypeDomain_extendDomain f
  map_add' a b := by
    simp only [Submodule.coe_add, map_add, Finsupp.subtypeDomain_add]
    rfl
  map_smul' r a := by
    ext y
    change S.aperyQuotientEquiv k (r • a.val) y.val = r • S.aperyQuotientEquiv k a.val y.val
    rw [map_smul]
    rfl

noncomputable def qDegreeBasis (n : ℕ) : Module.Basis (S.AperyDegreeExponent n) k (S.qDegree k n) :=
  Finsupp.basisSingleOne.map (S.qDegreeEquiv k n).symm

theorem qDegree_mul_mem {n p : ℕ} {a b : S.AperyAlgebra k}
    (ha : a ∈ S.qDegree k n) (hb : b ∈ S.qDegree k p) : a * b ∈ S.qDegree k (n + p) := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  refine ⟨S.gradedMul k n p f g, ?_⟩
  change S.toAperyAlgebra k (DirectSum.of _ (n + p) (S.gradedMul k n p f g)) =
    S.toAperyAlgebra k (DirectSum.of _ n f) * S.toAperyAlgebra k (DirectSum.of _ p g)
  rw [← S.tangent_of_mul, map_mul]

end NSP14.NumericalSemigroup
