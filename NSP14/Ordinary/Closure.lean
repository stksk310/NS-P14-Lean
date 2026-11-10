module
public import NSP14.Ordinary.NumericalBettiClosure
public import NSP14.Target.IntervalBetti
public import NSP14.Semigroup.AugmentationBetti
@[expose] public section
open NSP14.Homological
namespace NSP14.Ordinary
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem ordinary_source_betti_zero_le_one :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) 0≤1 := by
  rw [S.actualG_totalBetti_zero k]

/-- The ordinary branch compares the actual completed tangent cones over
the original arbitrary field, in their own minimal presentations, in all rows. -/
theorem ordinary_actual_completion_betti_le (he : 3 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) (i : ℕ) :
    let T := S.intervalCompletion (show 2 ≤ S.embeddingDimension from by omega)
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k T.AtomExponent (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i := by
  dsimp only
  cases i with
  | zero =>
    rw [S.completed_totalBetti_zero k,S.ordinary_interval_completed_betti_zero k (by omega) hw]
  | succ i =>
    rw [← S.completed_totalBetti k,S.ordinary_interval_completed_betti k (by omega) hw (i+1) (by omega)]
    exact ordinary_betti_bound S k he (i+1) (by omega)
end NSP14.Ordinary
