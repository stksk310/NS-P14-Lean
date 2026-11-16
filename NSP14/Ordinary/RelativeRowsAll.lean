module
public import NSP14.Ordinary.IntrinsicFullTransfer
public import NSP14.Ordinary.ActualTorRow
public import NSP14.Homological.RegularH0Dimension
@[expose] public section
open NSP14.Homological
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

theorem relativeBetti_zero :
    letI := W.relativeG_finite
    totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG 0=1+W.cut.complementRank := by
  let := W.relativeG_finite
  have h := regularPartialH0_squareZero_length L (W.source.TangentAlgebra L) W.cut.complementRank
    W.cut.nativeCutVariables W.cut.complementPolynomialToG W.cut.nativeCutH0ZIso
  exact (W.nativeRelativeBetti 0).symm.trans h

theorem relative_Euler_above (j : ℕ) (hj : W.source.actualCutRank+1 ≤ j) :
    letI := W.relativeG_finite
    bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j=0 := by
  let := W.relativeG_finite
  induction j,hj using Nat.le_induction with
  | base => exact W.relative_Euler_terminal
  | succ j hj ih =>
    have hβ := totalBetti_eq_zero_of_gt L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1)
      (by simp only [Fintype.card_option,Fintype.card_fin];omega)
    rw [bettiEuler_succ,hβ,ih]
    rfl

/-- The actual rows above r vanish, and the target's extra rows are
nonnegative. This exports every positive row without dropping the top. -/
theorem actualTor_target_row_all (j : ℕ) (hj : 1 ≤ j) :
    letI := W.relativeG_finite
    (bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ) ≤
      TargetMargin.target W.source.embeddingDimension W.source.deficit W.source.actualCutRank j := by
  let := W.relativeG_finite
  by_cases hr : j≤W.source.actualCutRank
  · exact W.actualTor_target_row j ⟨hj,hr⟩
  · rw [W.relative_Euler_above j (by omega)]
    exact Target.targetCoefficient_nonneg _ _ _ _ (by have := W.cut.extendedHeadBasis_card;omega)
end NSP14.Ordinary.ActualWitness
