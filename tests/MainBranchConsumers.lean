module
public import NSP14.Main.Branches
@[expose] public section
open NSP14
namespace NSP14.Tests.Run20Branches
variable (S : NumericalSemigroup) (k : Type) [Field k] (i : ℕ)
theorem base (he : S.embeddingDimension ≤ 2) : S.IntervalComparison k i := S.intervalComparison_base k he i
theorem three (he : S.embeddingDimension=3) : S.IntervalComparison k i := S.intervalComparison_three k he i
theorem ordinary (he : 4 ≤ S.embeddingDimension) (hw : S.multiplicity-1 ≤ S.width) : S.IntervalComparison k i :=
  S.intervalComparison_ordinary k he hw i
theorem four (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) : S.IntervalComparison k i :=
  S.intervalComparison_narrow_four k he hw i
theorem many (he : 5 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) : S.IntervalComparison k i :=
  S.intervalComparison_narrow_many k he hw i
end NSP14.Tests.Run20Branches
