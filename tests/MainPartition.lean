module
public import audit.run20.PartitionClosed
@[expose] public section
open NSP14 NSP14.NumericalSemigroup
namespace NSP14.Tests.Run20Partition
theorem all_sources (S : NumericalSemigroup) : ∃! j : Fin 6, S.parameterRegion j := S.parameter_partition
theorem ordinary_boundary (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension)
    (hw : S.width=S.multiplicity-1) : S.parameterRegion 3 ∧ ∃! j, S.parameterRegion j :=
  ⟨⟨he,by omega⟩,S.parameter_partition⟩
theorem narrow_four_boundary (S : NumericalSemigroup) (he : S.embeddingDimension=4)
    (hw : S.width=S.multiplicity-2) : S.parameterRegion 4 ∧ ∃! j, S.parameterRegion j :=
  ⟨⟨he,by omega⟩,S.parameter_partition⟩
theorem narrow_many_boundary (S : NumericalSemigroup) (he : 5 ≤ S.embeddingDimension)
    (hw : S.width=S.multiplicity-2) : S.parameterRegion 5 ∧ ∃! j, S.parameterRegion j :=
  ⟨⟨he,by omega⟩,S.parameter_partition⟩
theorem actual_cut (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension) : S.cutParameters := S.cut_parameters he
theorem empty_tower_rank (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension)
    (h : S.deficit=0) : S.actualCutRank=2 := (S.cut_parameters he).2.2.2.2.2 h
theorem rank_boundaries : cutRegime 2 ∧ cutRegime 3 ∧ cutRegime 4 ∧ cutRegime 8 ∧ cutRegime 9 := by
  unfold cutRegime;decide
theorem normalized_boundaries (e : ℕ) (he : 6 ≤ e) :
    narrowRegime e (e-1) ∧ narrowRegime e e ∧ narrowRegime e (2*e-3) ∧
      narrowRegime e (2*e-2) := by unfold narrowRegime;omega
theorem normalization (S : NumericalSemigroup) (he : 4 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2) : S.narrowParameters he hw := S.narrow_parameters he hw
end NSP14.Tests.Run20Partition
