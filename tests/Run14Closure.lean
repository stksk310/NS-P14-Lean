module
public import NSP14
public import tests.Run14Acceptance
@[expose] public section
open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary NSP14.Homological
open Run14Fixtures
open scoped Classical BigOperators
namespace Run14Closure

noncomputable def rankTwoWitness : ActualWitness (ZMod 2) :=
  canonicalActualWitness rankTwo.source (ZMod 2) (by rw [rankTwo.embedding])
noncomputable def rankThreeWitness : ActualWitness (ZMod 2) :=
  canonicalActualWitness rankThree.source (ZMod 2) (by rw [rankThree.embedding]; decide)

theorem rank_two_rows (i : ℕ) (hi : 1 ≤ i ∧ i ≤ rankTwo.source.actualCutRank) :
    TargetMargin.lower rankTwo.source.embeddingDimension rankTwo.source.actualCutRank i +
      (rankTwo.source.actualLayers (ZMod 2)).row rankTwo.source.actualCutRank i rankTwo.source.deficit ≤
    TargetMargin.target rankTwo.source.embeddingDimension rankTwo.source.deficit rankTwo.source.actualCutRank i :=
  rankTwoWitness.all_rows i hi

theorem rank_three_rows (i : ℕ) (hi : 1 ≤ i ∧ i ≤ rankThree.source.actualCutRank) :
    TargetMargin.lower rankThree.source.embeddingDimension rankThree.source.actualCutRank i +
      (rankThree.source.actualLayers (ZMod 2)).row rankThree.source.actualCutRank i rankThree.source.deficit ≤
    TargetMargin.target rankThree.source.embeddingDimension rankThree.source.deficit rankThree.source.actualCutRank i :=
  rankThreeWitness.all_rows i hi

theorem same_cut_exact (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (rankThreeWitness.cut.cutKInclusion s hs).hom ∧
    Function.Exact (rankThreeWitness.cut.cutKInclusion s hs).hom (rankThreeWitness.cut.cutTowerStep s).hom ∧
    Function.Surjective (rankThreeWitness.cut.cutTowerStep s).hom := rankThreeWitness.tower_exact s hs

theorem same_cut_generated (s : ℕ) (hs : 1 ≤ s) :
    rankThreeWitness.cut.generatorSpace s s=⊤ ∧
      rankThreeWitness.cut.generatorSpace s (s+1)=⊤ := rankThreeWitness.tower_generated s hs

theorem actual_augmentation_members (s n : ℕ) (hn : 1 ≤ n) (a : rankThreeWitness.cut.cutHigh s n) :
    a ∈ rankThreeWitness.cut.positiveSpace s n ↔
      a.val ∈ rankThree.source.towerHighIdeal (InfiniteScalarField (ZMod 2)) s (n+1) :=
  rankThreeWitness.cut.positiveSpace_mem_iff s n hn a

theorem actual_generator_quotient (s n : ℕ) :
    Module.finrank (ZMod 2) (↥(rankThree.source.towerHighIdeal (ZMod 2) s n) ⧸
      rankThree.source.truncNextSpace (ZMod 2) s n) =
      Module.finrank (ZMod 2) (rankThree.source.towerStageDegree (ZMod 2) s n) :=
  rankThree.source.trunc_generator_count (ZMod 2) s n

theorem nonzero_actual_resource : 0 < rankThree.source.towerResource (ZMod 2) 0 := by
  rw [Run14Acceptance.rank_three_H_zero]
  decide

theorem full_tail_cap (j : ℕ) :
    (rankThree.source.actualLayers (ZMod 2)).tail j ≤
      (rankThree.source.embeddingDimension : ℚ)+rankThree.source.deficit-1 :=
  rankThreeWitness.numericalData.tail_cap j

theorem all_actual_intervals (t : ℕ) :
    rankThree.source.towerResource (ZMod 2) t =
      Fintype.card (rankThree.source.ContributingHead t) := rankThree.source.towerResource_card (ZMod 2) t

theorem field_independent_resources (t : ℕ) :
    rankThree.source.towerResource (ZMod 2) t =
      rankThree.source.towerResource (InfiniteScalarField (ZMod 2)) t :=
  rankThree.source.towerResource_field_independent (ZMod 2) _ t

theorem char_two_green :
    let S := rankThree.source
    let k := InfiniteScalarField (ZMod 2)
    let a := (S.degreeSet 2).card
    let p := quadraticIndex a
    ∃ c : Fin p → S.headDegree k 1, LinearIndependent k c ∧
      ∀ s, s ≤ p → Module.finrank k (S.linearCutDegree k c s 2) ≤
        (p+1-s).choose 2+(a-quadraticTriangular p-s) := rankThree.source.actual_green_flag _

theorem changing_tower_exact (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (Run12Fixtures.changing.towerKInclusion (ZMod 2) s hs) ∧
    Function.Exact (Run12Fixtures.changing.towerKInclusion (ZMod 2) s hs)
      (Run12Fixtures.changing.towerTruncStep (ZMod 2) s (s+1)) ∧
    Function.Surjective (Run12Fixtures.changing.towerTruncStep (ZMod 2) s (s+1)) :=
  Run12Fixtures.changing.tower_exact (ZMod 2) s hs
open AperyQuotientExamples
noncomputable def deficitZeroWitness : ActualWitness (ZMod 2) :=
  canonicalActualWitness ordinaryThree (ZMod 2) (by rw [ordinaryThree_e])

theorem deficit_zero_cut_and_empty_tower :
    Nonempty (ordinaryThree.LinearCutData (InfiniteScalarField (ZMod 2))) ∧
      ∀ t, ordinaryThree.towerResource (ZMod 2) t=0 := by
  refine ⟨⟨deficitZeroWitness.cut⟩,?_⟩
  exact ordinaryThree.towerResource_eq_zero_of_deficit_zero (ZMod 2)
    (by simp [deficit,ordinaryThree_m,ordinaryThree_e])

theorem same_cut_minimal_generator_count (s n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (InfiniteScalarField (ZMod 2))
      (rankThreeWitness.cut.cutHigh s n ⧸
        (rankThreeWitness.cut.positiveSpace s n).restrictScalars (InfiniteScalarField (ZMod 2))) =
      Module.finrank (InfiniteScalarField (ZMod 2))
        (rankThree.source.towerStageDegree (InfiniteScalarField (ZMod 2)) s n) :=
  rankThreeWitness.cut.cut_minimal_generator_count s n hn

theorem changing_actual_K_nonzero : ∃ a : Run12Fixtures.changing.TowerK (ZMod 2) 2, a ≠ 0 := by
  let S := Run12Fixtures.changing
  let t : S.JumpExponent 2 := ⟨⟨Run12Fixtures.v26,Run12Fixtures.terminal_26⟩,Run12Fixtures.jump_26⟩
  let b := (S.ascendingStratumCoordinates (ZMod 2) 2 (by decide)).symm (Finsupp.single t 1)
  refine ⟨S.towerStratumEquiv (ZMod 2) 2 b,?_⟩
  intro hz
  have hb : b=0 := (S.towerStratumEquiv (ZMod 2) 2).injective (hz.trans (map_zero _).symm)
  have hf := congrArg (S.ascendingStratumCoordinates (ZMod 2) 2 (by decide)) hb
  rw [LinearEquiv.apply_symm_apply,map_zero] at hf
  have he := congrArg (fun f : S.JumpExponent 2 →₀ ZMod 2 => f t) hf
  have hh : (1 : ZMod 2)=0 := by simpa only [Finsupp.single_eq_same,Finsupp.zero_apply] using he
  exact one_ne_zero hh

end Run14Closure
