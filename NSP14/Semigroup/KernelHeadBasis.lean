module

public import NSP14.Semigroup.KernelHead

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def terminalMonomial (x : S.TerminalExponent) : (S.xMultiply k).ker :=
  ⟨S.initialMonomial k x.val,
    S.xMultiply_initial_dead k x.val ((S.not_live_iff_terminal x.val).2 x.property)⟩

theorem xKernelEquiv_terminal (x : S.TerminalExponent) :
    S.xKernelEquiv k (S.terminalMonomial k x) = Finsupp.single x 1 := by
  classical
  ext y
  change S.tangentCoordinates k (S.initialMonomial k x.val) y.val = Finsupp.single x (1 : k) y
  rw [S.tangentCoordinates_initial]
  by_cases h : x = y
  · subst y; simp
  · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
    simp [h, hv]

theorem xKernelBasis_eq_initial (x : S.TerminalExponent) :
    (S.xKernelBasis k x).val = S.initialMonomial k x.val := by
  have heq : S.xKernelBasis k x = S.terminalMonomial k x := by
    apply (S.xKernelEquiv k).injective
    rw [S.xKernelEquiv_terminal]
    simp [xKernelBasis]
  exact congrArg Subtype.val heq

theorem headQuotientEquiv_mk (a : S.TangentAlgebra k) :
    S.headQuotientEquiv k (Ideal.Quotient.mk (S.xIdeal k) a) = S.actualHeadProjection k a := rfl

theorem headQuotientEquiv_initial (x : S.HeadExponent) :
    S.headQuotientEquiv k (Ideal.Quotient.mk (S.xIdeal k) (S.initialMonomial k x.val)) =
      Finsupp.single x 1 := by
  classical
  rw [S.headQuotientEquiv_mk]
  ext y
  change S.tangentCoordinates k (S.initialMonomial k x.val) y.val = Finsupp.single x (1 : k) y
  rw [S.tangentCoordinates_initial]
  by_cases h : x = y
  · subst y; simp
  · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
    simp [h, hv]

theorem headBasis_eq_initial (x : S.HeadExponent) :
    S.headBasis k x = Ideal.Quotient.mk (S.xIdeal k) (S.initialMonomial k x.val) := by
  apply (S.headQuotientEquiv k).injective
  rw [S.headQuotientEquiv_initial]
  simp [headBasis]

theorem head_initial_ne_zero (x : S.HeadExponent) :
    Ideal.Quotient.mk (S.xIdeal k) (S.initialMonomial k x.val) ≠ 0 := by
  intro h
  have he := congrArg (S.headQuotientEquiv k) h
  rw [S.headQuotientEquiv_initial, map_zero] at he
  exact Finsupp.single_ne_zero.mpr one_ne_zero he

omit [Nontrivial k] in
/-- The multiplicity initial form is in degree one, with the actual quotient representative. -/
theorem xElement_degree_one : S.xElement k =
    DirectSum.of (S.GradedPiece k) 1
      (S.monomialClass k 1 S.multiplicityExponent (le_of_eq S.order_multiplicity.symm)) := by
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply S.homogeneous_mk_eq k S.order_multiplicity
  rfl

omit [Nontrivial k] in
theorem xMultiply_of (n : ℕ) (a : S.GradedPiece k n) :
    S.xMultiply k (DirectSum.of (S.GradedPiece k) n a) =
      DirectSum.of (S.GradedPiece k) (n + 1) (S.xAction k n a) := by
  change DirectSum.of (S.GradedPiece k) n a * S.xElement k = _
  rw [S.xElement_degree_one, S.tangent_of_mul]
  rfl

end NSP14.NumericalSemigroup
