module
public import NSP14
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological NSP14.NumericalSemigroup
open scoped BigOperators
namespace TowerHarmonicAcceptance

abbrev L := InfiniteScalarField (ZMod 2)

noncomputable def rankTwoCut : Run14Fixtures.rankTwo.source.LinearCutData L :=
  Run14Fixtures.rankTwo.source.infiniteFieldCut (ZMod 2) (by rw [Run14Fixtures.rankTwo.embedding])

/-- Actual Gamma=<6,7,11>, r=2, in characteristic two. -/
theorem rank_two_row (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 2) :
    ((rankTwoCut.cutHighEuler 2 2 j+rankTwoCut.cutTEuler (j-1) : ℤ) : ℚ) ≤
      (Run14Fixtures.rankTwo.source.actualLayers L).row Run14Fixtures.rankTwo.source.actualCutRank j
        Run14Fixtures.rankTwo.source.deficit :=
  rankTwoCut.cutTower_resource_row j (by simpa only [Run14Fixtures.rankTwo.cut_rank] using hj)

theorem rank_two_top (s n : ℕ) : rankTwoCut.cutHighEuler s n 2=0 := by
  simpa only [Run14Fixtures.rankTwo.cut_rank] using rankTwoCut.cutHighEuler_top s n

theorem actual_H0 (s n : ℕ) (hn : 1 ≤ n) :
    rankTwoCut.cutHighEuler s n 0=Module.finrank L (Run14Fixtures.rankTwo.source.towerStageDegree L s n) :=
  rankTwoCut.cutHighEuler_zero s n hn

def ordinaryAP : ArithmeticSequence.Data := ArithmeticSequence.intervalData 3 2 (by decide) (by decide)

theorem ordinaryAP_embedding : ordinaryAP.source.embeddingDimension=3 := by
  rw [ordinaryAP.embeddingDimension]
  rfl

theorem ordinaryAP_deficit : ordinaryAP.source.deficit=0 := by
  rw [deficit,ordinaryAP.multiplicity,ordinaryAP_embedding]
  rfl

noncomputable def emptyTowerCut : ordinaryAP.source.LinearCutData L :=
  ordinaryAP.source.infiniteFieldCut (ZMod 2) (by rw [ordinaryAP_embedding])

/-- Delta=0 really gives the empty same-cut tower, rather than an assumed
nonempty summation interval. -/
theorem empty_tower (j : ℕ) :
    emptyTowerCut.cutHighEuler 2 2 (j+1)+emptyTowerCut.cutTEuler j ≤ 0 := by
  have hν := ordinaryAP.source.qTopDegree_le_deficit
  rw [ordinaryAP_deficit] at hν
  have he : ordinaryAP.source.qTopDegree-1=0 := by omega
  simpa only [he,Finset.range_zero,Finset.sum_empty] using emptyTowerCut.cutTower_combined j
end TowerHarmonicAcceptance
