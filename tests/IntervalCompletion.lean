module
public import NSP14
@[expose] public section
namespace IntervalCompletionAcceptance
open NSP14
variable (S : NumericalSemigroup) (he : 2 ≤ S.embeddingDimension)
theorem literal_interval :
    (S.intervalCompletion he).carrier=AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) :=
  S.intervalCompletion_carrier he

theorem minimal_target_rank :
    (S.intervalCompletion he).embeddingDimension=min S.width (S.multiplicity-1)+1 :=
  S.intervalCompletion_embeddingDimension he
theorem ordinary_literal (hw : S.multiplicity-1 ≤ S.width) (x : ℕ) :
    x ∈ S.intervalCompletion he ↔ x=0 ∨ S.multiplicity ≤ x :=
  S.intervalCompletion_ordinary_mem he hw x
end IntervalCompletionAcceptance
