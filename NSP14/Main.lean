module
public import NSP14.Main.Partition
public import NSP14.Main.Branches
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup

/-- P14 for every numerical semigroup, every field, and every homological row.
Both completed tangent algebras use their own actual minimal atom variables. -/
theorem p14_totalBetti_le_intervalCompletion (S : NumericalSemigroup) (k : Type) [Field k]
    (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k S.intervalCompletionAll.AtomExponent
      (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
        (S.intervalCompletionAll.FormalTangentAlgebra k)) i := by
  obtain ⟨j,hj,_⟩ := S.parameter_partition
  change S.IntervalComparison k i
  fin_cases j
  · exact S.intervalComparison_base k (by change S.embeddingDimension=1 at hj;omega) i
  · exact S.intervalComparison_base k (by change S.embeddingDimension=2 at hj;omega) i
  · exact S.intervalComparison_three k hj i
  · exact S.intervalComparison_ordinary k hj.1 hj.2 i
  · exact S.intervalComparison_narrow_four k hj.1 hj.2 i
  · exact S.intervalComparison_narrow_many k hj.1 hj.2 i

/-- Compatibility with the previous positive-width target API. -/
theorem p14_totalBetti_le_intervalCompletion_compat (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 2 ≤ S.embeddingDimension) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k)
        ((S.intervalCompletion he).FormalTangentAlgebra k)) i := by
  have h := S.p14_totalBetti_le_intervalCompletion k i
  rwa [S.intervalCompletionAll_completed_totalBetti he k i] at h
end NSP14.NumericalSemigroup
