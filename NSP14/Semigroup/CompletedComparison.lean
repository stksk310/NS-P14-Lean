module

public import NSP14.Semigroup.CompletedPieces
public import NSP14.Semigroup.FormalTangentScalars
public import NSP14.Semigroup.TerminalCoordinates

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable def completedGradedLinearEquiv : S.TangentAlgebra k ≃ₗ[k] S.FormalTangentAlgebra k :=
  DFinsupp.mapRange.linearEquiv (fun n => S.completedPieceEquiv k n)

theorem completedGradedLinearEquiv_of (n : ℕ) (a : S.GradedPiece k n) :
    S.completedGradedLinearEquiv k (DirectSum.of (S.GradedPiece k) n a) =
      DirectSum.of (S.FormalGradedPiece k) n (S.completedPieceEquiv k n a) := by
  change DFinsupp.mapRange (fun i a => S.completedPieceEquiv k i a)
    (fun i => (S.completedPieceEquiv k i).map_zero) (DFinsupp.single n a) = _
  rw [DFinsupp.mapRange_single]
  rfl

theorem completedGradedLinearEquiv_mul (a b : S.TangentAlgebra k) :
    S.completedGradedLinearEquiv k (a*b) =
      S.completedGradedLinearEquiv k a * S.completedGradedLinearEquiv k b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul,map_add,ha,hb]
  | of n a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b c hb hc => simp only [mul_add,map_add,hb,hc]
    | of p b =>
      rw [S.tangent_of_mul, S.completedGradedLinearEquiv_of, S.completedPieceEquiv_mul,
        S.completedGradedLinearEquiv_of, S.completedGradedLinearEquiv_of, S.formal_tangent_of_mul]

/-- Natural, multiplicative, degree-preserving comparison with the formal-ring tangent cone. -/
noncomputable def completedGradedAlgEquiv : S.TangentAlgebra k ≃ₐ[k] S.FormalTangentAlgebra k :=
  AlgEquiv.ofLinearEquiv (S.completedGradedLinearEquiv k) (by
    change S.completedGradedLinearEquiv k (DirectSum.of (S.GradedPiece k) 0
      (Submodule.Quotient.mk (S.zeroRepresentative k 1))) =
        DirectSum.of (S.FormalGradedPiece k) 0
          (Submodule.Quotient.mk (S.formalZeroRepresentative k 1))
    rw [S.completedGradedLinearEquiv_of, S.completedPieceEquiv_mk]
    congr 2
    apply Subtype.ext
    exact map_one (S.polynomialToFormal k)) (S.completedGradedLinearEquiv_mul k)

/-- The comparison preserves every homogeneous degree, not merely total dimensions. -/
theorem completedGradedAlgEquiv_of (n : ℕ) (a : S.GradedPiece k n) :
    S.completedGradedAlgEquiv k (DirectSum.of (S.GradedPiece k) n a) =
      DirectSum.of (S.FormalGradedPiece k) n (S.completedPieceEquiv k n a) :=
  S.completedGradedLinearEquiv_of k n a

noncomputable def formalMonomialClass (n : ℕ) (x : S.carrier) (hx : n ≤ S.order x.val) :
    S.FormalGradedPiece k n :=
  Submodule.Quotient.mk ⟨S.formalMonomial k x 1,
    Ideal.pow_le_pow_right hx (S.formalMonomial_order_mem_pow k x)⟩

noncomputable def formalInitialMonomial (x : S.carrier) : S.FormalTangentAlgebra k :=
  DirectSum.of (S.FormalGradedPiece k) (S.order x.val) (S.formalMonomialClass k _ x le_rfl)

theorem completedPieceEquiv_monomial (n : ℕ) (x : S.carrier) (hx : n ≤ S.order x.val) :
    S.completedPieceEquiv k n (S.monomialClass k n x hx) = S.formalMonomialClass k n x hx := by
  rw [monomialClass, S.completedPieceEquiv_mk]
  congr 1
  apply Subtype.ext
  exact S.polynomialToFormal_single k x 1

theorem completedGradedAlgEquiv_initial (x : S.carrier) :
    S.completedGradedAlgEquiv k (S.initialMonomial k x) = S.formalInitialMonomial k x := by
  rw [initialMonomial, S.completedGradedAlgEquiv_of, S.completedPieceEquiv_monomial]
  rfl

end NSP14.NumericalSemigroup
