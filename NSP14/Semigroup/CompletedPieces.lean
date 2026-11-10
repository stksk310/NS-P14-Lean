module

public import NSP14.Semigroup.FormalInclusion

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable def completedPowerMap (n : ℕ) : S.powerModule k n →ₗ[k] S.formalPowerModule k n where
  toFun f := ⟨S.polynomialToFormal k f.val,(S.polynomialToFormal_mem_pow k n f.val).2 f.property⟩
  map_add' _f _g := Subtype.ext (map_add _ _ _)
  map_smul' _c _f := Subtype.ext (map_smul _ _ _)

noncomputable def completedRepresentative (n : ℕ) : S.powerModule k n →ₗ[k] S.FormalGradedPiece k n :=
  (S.formalNextPower k n).mkQ.comp (S.completedPowerMap k n)

theorem completedRepresentative_ker (n : ℕ) :
    (S.completedRepresentative k n).ker = S.nextPower k n := by
  ext f
  change (Submodule.Quotient.mk (S.completedPowerMap k n f) : S.FormalGradedPiece k n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact S.polynomialToFormal_mem_pow k (n+1) f.val

theorem completedRepresentative_surjective (n : ℕ) :
    Function.Surjective (S.completedRepresentative k n) := by
  intro a
  induction a using Submodule.Quotient.induction_on with
  | _ f =>
    refine ⟨⟨S.formalTruncation k n f.val,S.formalTruncation_mem k n f.val⟩, ?_⟩
    change (Submodule.Quotient.mk _ : S.FormalGradedPiece k n) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    change S.polynomialToFormal k (S.formalTruncation k n f.val)-f.val ∈ S.formalMaximalIdeal k ^ (n+1)
    simpa only [neg_sub] using (S.formalMaximalIdeal k ^ (n+1)).neg_mem
      (S.formalTruncation_difference k n f.val f.property)

/-- The natural map of actual nth ideal-power quotients is an equivalence. -/
noncomputable def completedPieceEquiv (n : ℕ) : S.GradedPiece k n ≃ₗ[k] S.FormalGradedPiece k n :=
  (Submodule.quotEquivOfEq _ _ (S.completedRepresentative_ker k n).symm).trans
    ((S.completedRepresentative k n).quotKerEquivOfSurjective (S.completedRepresentative_surjective k n))

theorem completedPieceEquiv_mk (n : ℕ) (f : S.powerModule k n) :
    S.completedPieceEquiv k n (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (S.completedPowerMap k n f) := rfl

theorem completedPieceEquiv_mul (n p : ℕ) (a : S.GradedPiece k n) (b : S.GradedPiece k p) :
    S.completedPieceEquiv k (n+p) (S.gradedMul k n p a b) =
      S.formalGradedMul k n p (S.completedPieceEquiv k n a) (S.completedPieceEquiv k p b) := by
  induction a using Submodule.Quotient.induction_on with
  | _ f =>
    induction b using Submodule.Quotient.induction_on with
    | _ g =>
      rw [S.gradedMul_mk, S.completedPieceEquiv_mk, S.completedPieceEquiv_mk,
        S.completedPieceEquiv_mk, S.formalGradedMul_mk]
      congr 1
      apply Subtype.ext
      exact map_mul (S.polynomialToFormal k) f.val g.val

end NSP14.NumericalSemigroup
