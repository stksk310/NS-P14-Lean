module
public import audit.run20.RequestedGoals
@[expose] public section
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run20Contracts
example (S : NumericalSemigroup) : S.intervalCompletionAll.carrier=
    AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) := rfl
example (S : NumericalSemigroup) (he : 2 ≤ S.embeddingDimension) (k : Type) [Field k] (i : ℕ) :=
  S.intervalCompletionAll_completed_totalBetti he k i
example : Prop := Run20.Requested.I_PARTITION
example : Prop := Run20.Requested.I_MAIN
end NSP14.Tests.Run20Contracts
