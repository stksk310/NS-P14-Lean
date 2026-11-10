module

public import NSP14.Semigroup.KernelHeadBasis

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- An actual initial monomial followed by the actual quotient G→A. -/
noncomputable def headMonomial (x : S.carrier) : S.HeadAlgebra k :=
  Ideal.Quotient.mk (S.xIdeal k) (S.initialMonomial k x)

theorem headMonomial_coordinates (x : S.carrier) (y : S.HeadExponent) :
    S.headQuotientEquiv k (S.headMonomial k x) y = Finsupp.single x (1 : k) y.val := by
  rw [headMonomial, S.headQuotientEquiv_mk]
  change S.tangentCoordinates k (S.initialMonomial k x) y.val = _
  rw [S.tangentCoordinates_initial]

theorem headMonomial_eq_basis (x : S.HeadExponent) :
    S.headMonomial k x.val = S.headBasis k x := (S.headBasis_eq_initial k x).symm

theorem headMonomial_zero_of_not_head (x : S.carrier) (hx : ¬S.XHead x.val) :
    S.headMonomial k x = 0 := by
  classical
  apply (S.headQuotientEquiv k).injective
  ext y
  rw [S.headMonomial_coordinates, map_zero]
  have hxy : x ≠ y.val := by intro heq; exact hx (heq ▸ y.property)
  simp [hxy]

omit [Nontrivial k] in
theorem headMonomial_mul_live (x y : S.carrier)
    (h : S.order (x.val + y.val) = S.order x.val + S.order y.val) :
    S.headMonomial k x * S.headMonomial k y = S.headMonomial k (x + y) := by
  rw [headMonomial, headMonomial, ← map_mul, S.initialMonomial_mul_live k x y h]
  rfl

theorem headMonomial_mul_dead (x y : S.carrier)
    (h : S.order x.val + S.order y.val < S.order (x.val + y.val)) :
    S.headMonomial k x * S.headMonomial k y = 0 := by
  rw [headMonomial, headMonomial, ← map_mul,
    (S.initialMonomial_mul_eq_zero_iff k x y).2 h, map_zero]

theorem headBasis_repr (a : S.HeadAlgebra k) :
    (S.headBasis k).repr a = S.headQuotientEquiv k a := rfl

theorem head_expansion (a : S.HeadAlgebra k) :
    (S.headQuotientEquiv k a).sum (fun x c => c • S.headBasis k x) = a :=
  (S.headBasis k).linearCombination_repr a

theorem apery_head {x : ℕ} (hx : x ∈ S.aperySet) : S.XHead x := by
  refine ⟨((S.mem_aperySet_iff x).1 hx).1, ?_⟩
  rintro ⟨y, hy, heq, _⟩
  exact S.apery_no_predecessor hx ⟨y, hy, heq⟩

theorem nonapery_add (x y : S.carrier) (hy : y.val ∉ S.aperySet) :
    (x + y).val ∉ S.aperySet := by
  intro h
  exact hy (S.apery_summands x.property y.property h).2

end NSP14.NumericalSemigroup
