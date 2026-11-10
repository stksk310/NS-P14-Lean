module

public import NSP14
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
public import tests.Run12BasicExamples

@[expose] public section

open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary NSP14.Homological
open Run14Fixtures

namespace Run14Acceptance

instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The required rank-two counterboundary is an actual generated semigroup. -/
theorem rank_two_maximal_not_quadratic_maximal :
    rankTwo.source.actualCutRank = rankTwo.source.embeddingDimension - 1 ∧
      Module.finrank (ZMod 2) (rankTwo.source.qDegree (ZMod 2) 2) ≠
        rankTwo.source.embeddingDimension.choose 2 := by
  rw [rankTwo.cut_rank, rankTwo.embedding, rankTwo.quadratic_dimension]
  decide

theorem rank_two_no_triangular_bound :
    ¬ (rankTwo.source.actualCutRank + 1).choose 2 ≤
      Module.finrank (ZMod 2) (rankTwo.source.qDegree (ZMod 2) 2) := by
  rw [rankTwo.cut_rank, rankTwo.quadratic_dimension]
  decide

/-- An even composite multiplicity; squares and zero-containing pairs included. -/
noncomputable def even_actual_pair_data :
    AperyPairData evenMaximal.source.carrier 8 3 := by
  rw [← evenMaximal.multiplicity, ← evenMaximal.embedding]
  exact evenMaximal.source.maximalQDegreeAperyPairData (ZMod 2) (by
    rw [evenMaximal.quadratic_dimension, evenMaximal.embedding]; decide)

theorem even_actual_sidon_bound : 3 * (3 - 1) + 1 ≤ 8 :=
  even_actual_pair_data.multiplicity_bound

noncomputable def rank_three_actual_pair_data :
    AperyPairData rankThree.source.carrier 13 4 := by
  rw [← rankThree.multiplicity, ← rankThree.embedding]
  exact rankThree.source.actualAperyPairData (rankThree.source.actualCutRank_maximal
    (by rw [rankThree.cut_rank]) (by rw [rankThree.cut_rank, rankThree.embedding]))

theorem rank_three_actual_deficit : (4 - 1 : ℕ)^2 ≤ rankThree.source.deficit := by
  simpa [rankThree.embedding] using rankThree.source.maximal_qDegree_deficit_bound (ZMod 2)
    (by rw [rankThree.quadratic_dimension, rankThree.embedding]; decide)

theorem rank_three_H_zero : rankThree.source.towerResource (ZMod 2) 0 = 9 := by
  rw [rankThree.source.towerResource_zero]
  simp [deficit, rankThree.multiplicity, rankThree.embedding]

theorem rank_three_H_full_support (t : ℕ)
    (ht : t ∉ rankThree.source.towerResourceSupport) :
    rankThree.source.towerResource (ZMod 2) t = 0 :=
  rankThree.source.towerResource_outside_support (ZMod 2) t ht

theorem actual_low_stage_char_two (s n : ℕ) (hn : n ≤ s) :
    Module.finrank (ZMod 2) (rankTwo.source.towerStageDegree (ZMod 2) s n) =
      Module.finrank (ZMod 2) (rankTwo.source.qDegree (ZMod 2) n) :=
  (rankTwo.source.towerStageLowDegreeEquiv (ZMod 2) s n hn).finrank_eq

open AperyQuotientExamples

theorem multiplicity_one_shortest_paths (r : Fin naturals.multiplicity) :
    naturals.leastOffsetLength r = 0 := by
  have hb := naturals.leastOffsetLength_lt_multiplicity r
  rw [naturals_m] at hb
  omega

theorem deficit_zero_empty_resource (t : ℕ) : naturals.towerResource (ZMod 2) t = 0 :=
  naturals.towerResource_eq_zero_of_deficit_zero (ZMod 2)
    (by simp [deficit, naturals_m, naturals_e]) t

theorem actual_changing_terminal_finite : Set.Finite {n | Run12Fixtures.changing.Terminal n} :=
  Run12Fixtures.changing.terminal_finite

theorem actual_changing_finite_A : Module.Finite (ZMod 2)
    (Run12Fixtures.changing.HeadAlgebra (ZMod 2)) := inferInstance

theorem actual_changing_finite_T : Module.Finite (ZMod 2)
    ((Run12Fixtures.changing.xMultiply (ZMod 2)).ker) := inferInstance

theorem actual_changing_finite_N : Module.Finite (ZMod 2)
    ((Run12Fixtures.changing.nonAperyIdeal (ZMod 2)).restrictScalars (ZMod 2)) := inferInstance

/-- Both changing-jump labels remain present in the genuine finite basis. -/
theorem actual_changing_two_terminals : 2 ≤ Fintype.card Run12Fixtures.changing.TerminalExponent := by
  let a : Run12Fixtures.changing.TerminalExponent := ⟨Run12Fixtures.v26, Run12Fixtures.terminal_26⟩
  let b : Run12Fixtures.changing.TerminalExponent := ⟨Run12Fixtures.v41, Run12Fixtures.terminal_41⟩
  have hne : a ≠ b := by intro h; have he := congrArg (fun t => t.val.val) h; change 26 = 41 at he; omega
  exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨a,b,hne⟩⟩

/-- This extension is infinite even though its coefficient field has two elements. -/
theorem finite_field_extension_infinite : Infinite (InfiniteScalarField (ZMod 2)) := inferInstance

theorem finite_field_extension_same_characteristic : CharP (InfiniteScalarField (ZMod 2)) 2 :=
  infiniteScalarField_charP (ZMod 2) 2

theorem actual_extension_preserves_Betti (i : ℕ) (t : ℤ) :
    gradedBetti (InfiniteScalarField (ZMod 2)) Run12Fixtures.changing.NonXAtom _
      (Run12Fixtures.changing.actualAGrading (InfiniteScalarField (ZMod 2))) i t =
        gradedBetti (ZMod 2) Run12Fixtures.changing.NonXAtom _
          (Run12Fixtures.changing.actualAGrading (ZMod 2)) i t :=
  Run12Fixtures.changing.actualA_gradedBetti_baseChange (ZMod 2) (InfiniteScalarField (ZMod 2)) i t

end Run14Acceptance
