module
public import NSP14.Ordinary.ActualTorRow
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace ActualTorRowAcceptance
abbrev L := InfiniteScalarField (ZMod 2)
noncomputable def W2 : Ordinary.ActualWitness (ZMod 2) :=
  Ordinary.canonicalActualWitness Run14Fixtures.rankTwo.source (ZMod 2)
    (by rw [Run14Fixtures.rankTwo.embedding])
noncomputable def W3 : Ordinary.ActualWitness (ZMod 2) :=
  Ordinary.canonicalActualWitness Run14Fixtures.rankThree.source (ZMod 2)
    (by rw [Run14Fixtures.rankThree.embedding];decide)

theorem actual_rank_two_target (j : ℕ) (hj : 1 ≤ j ∧ j ≤ W2.source.actualCutRank) :
    letI := W2.relativeG_finite
    (bettiEuler L (Option (Fin W2.source.actualCutRank)) W2.relativeG j : ℚ) ≤
      Ordinary.TargetMargin.target W2.source.embeddingDimension W2.source.deficit W2.source.actualCutRank j :=
  W2.actualTor_target_row j hj

theorem actual_rank_three_resource (j : ℕ) (hj : 1 ≤ j ∧ j ≤ W3.source.actualCutRank) :
    letI := W3.relativeG_finite
    (bettiEuler L (Option (Fin W3.source.actualCutRank)) W3.relativeG j : ℚ) ≤
      Ordinary.TargetMargin.lower W3.source.embeddingDimension W3.source.actualCutRank j+
        (W3.source.actualLayers (ZMod 2)).row W3.source.actualCutRank j W3.source.deficit :=
  W3.actualTor_resource_row j hj
end ActualTorRowAcceptance
