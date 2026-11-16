module
public import NSP14.Main.IntervalTarget
public import NSP14.SmallEmbedding.ThreeComparison
public import NSP14.NarrowFour.Comparison
public import NSP14.Width.Closure
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup

def IntervalComparison (S : NumericalSemigroup) (k : Type) [Field k] (i : ℕ) : Prop :=
  totalBetti k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
  totalBetti k S.intervalCompletionAll.AtomExponent
    (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
      (S.intervalCompletionAll.FormalTangentAlgebra k)) i

variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem intervalComparison_base (he : S.embeddingDimension ≤ 2) (i : ℕ) :
    S.IntervalComparison k i := SmallEmbedding.base_comparison S k he i

theorem intervalComparison_three (he : S.embeddingDimension=3) (i : ℕ) :
    S.IntervalComparison k i := by
  unfold IntervalComparison
  rw [S.intervalCompletionAll_completed_totalBetti (by omega) k i]
  exact SmallEmbedding.three_comparison S k he i

theorem intervalComparison_ordinary (he : 4 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) (i : ℕ) : S.IntervalComparison k i := by
  unfold IntervalComparison
  rw [S.intervalCompletionAll_completed_totalBetti (by omega) k i]
  exact Ordinary.ordinary_actual_completion_betti_le S k (by omega) hw i

theorem intervalComparison_narrow_four (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) (i : ℕ) : S.IntervalComparison k i := by
  unfold IntervalComparison
  rw [S.intervalCompletionAll_completed_totalBetti (by omega) k i]
  exact NarrowFour.narrow_four_comparison S k he hw i

theorem intervalComparison_narrow_many (he : 5 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2) (i : ℕ) : S.IntervalComparison k i := by
  unfold IntervalComparison
  rw [S.intervalCompletionAll_completed_totalBetti (by omega) k i]
  exact S.narrow_width_comparison k he hw i
end NSP14.NumericalSemigroup
