module
public import NSP14.Main.IntervalTarget
public import tests.SmallEmbeddingBase
public import NSP14.ArithmeticSequence.Width
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run20Transport
def naturalsLater : NumericalSemigroup where
  carrier := ⊤
  conductor := 17
  cofinite := by intros;trivial
theorem different_conductors : Run19Base.naturals.conductor ≠ naturalsLater.conductor := by decide
theorem same_carrier : Run19Base.naturals.carrier=naturalsLater.carrier := rfl
theorem transport (k : Type) [Field k] (i : ℕ) :
    totalBetti k Run19Base.naturals.AtomExponent
      (ModuleCat.of (Run19Base.naturals.FullPolynomialRing k) (Run19Base.naturals.FormalTangentAlgebra k)) i =
    totalBetti k naturalsLater.AtomExponent
      (ModuleCat.of (naturalsLater.FullPolynomialRing k) (naturalsLater.FormalTangentAlgebra k)) i :=
  Run19Base.naturals.carrier_completed_totalBetti naturalsLater same_carrier k i
theorem literal_one : Run19Base.naturals.multiplicity=1 ∧ Run19Base.naturals.maxAtom=1 ∧
    Run19Base.naturals.width=0 ∧ Run19Base.naturals.intervalCompletionAll.carrier=
      AddSubmonoid.closure (Set.Icc 1 1) :=
  Run19Base.naturals.intervalCompletionAll_one Run19Base.naturals_embedding
theorem different_variables : Run19Base.threeFive.source.embeddingDimension=2 ∧
    (Run19Base.threeFive.source.intervalCompletion (by rw [Run19Base.threeFive.embeddingDimension];decide)).embeddingDimension=3 := by
  constructor
  · rw [Run19Base.threeFive.embeddingDimension];rfl
  · rw [NumericalSemigroup.intervalCompletion_embeddingDimension,Run19Base.threeFive.width,Run19Base.threeFive.multiplicity]
    rfl
theorem target_identification (k : Type) [Field k] (i : ℕ) :
    totalBetti k Run19Base.threeFive.source.intervalCompletionAll.AtomExponent
      (ModuleCat.of (Run19Base.threeFive.source.intervalCompletionAll.FullPolynomialRing k)
        (Run19Base.threeFive.source.intervalCompletionAll.FormalTangentAlgebra k)) i =
    totalBetti k (Run19Base.threeFive.source.intervalCompletion (by rw [Run19Base.threeFive.embeddingDimension];decide)).AtomExponent
      (ModuleCat.of ((Run19Base.threeFive.source.intervalCompletion (by rw [Run19Base.threeFive.embeddingDimension];decide)).FullPolynomialRing k)
        ((Run19Base.threeFive.source.intervalCompletion (by rw [Run19Base.threeFive.embeddingDimension];decide)).FormalTangentAlgebra k)) i :=
  Run19Base.threeFive.source.intervalCompletionAll_completed_totalBetti
    (by rw [Run19Base.threeFive.embeddingDimension];decide) k i
end NSP14.Tests.Run20Transport
