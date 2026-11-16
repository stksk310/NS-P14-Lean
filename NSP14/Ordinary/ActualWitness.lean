module
public import NSP14.Semigroup.ActualResources
public import NSP14.Semigroup.CutGeneratorCount
@[expose] public section
namespace NSP14.Ordinary
open NSP14.NumericalSemigroup

/-- One actual source and one cut over the fixed same-characteristic extension.
All numeric parameters and H are derived from source, never chosen profiles. -/
structure ActualWitness (k : Type) [Field k] where
  source : NumericalSemigroup
  embedding : 3 ≤ source.embeddingDimension
  cut : source.LinearCutData (NSP14.Homological.InfiniteScalarField k)

noncomputable def canonicalActualWitness (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 3 ≤ S.embeddingDimension) : ActualWitness k :=
  ⟨S,he,S.infiniteFieldCut k he⟩

namespace ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
noncomputable def numericalData : NumericalClosure.Data
    W.source.actualCutRank W.source.embeddingDimension W.source.deficit :=
  W.source.actualNumericalDataWithCut k W.embedding W.cut

@[simp] theorem numericalData_layers : W.numericalData.layers=W.source.actualLayers k := rfl

theorem all_rows : ∀ i, 1 ≤ i ∧ i ≤ W.source.actualCutRank →
    TargetMargin.lower W.source.embeddingDimension W.source.actualCutRank i +
      (W.source.actualLayers k).row W.source.actualCutRank i W.source.deficit ≤
    TargetMargin.target W.source.embeddingDimension W.source.deficit W.source.actualCutRank i :=
  W.numericalData.all_rows W.source.actualNumericalBoundary

/-- Same fixed P and same cut used for every actual tower stage. -/
abbrev tower_exact (s : ℕ) (hs : 1 ≤ s) := W.cut.cutTower_exact s hs

abbrev tower_generated (s : ℕ) (hs : 1 ≤ s) := W.cut.cutTower_generated s hs

end ActualWitness
end NSP14.Ordinary
