module
public import NSP14.ArithmeticSequence.MaximalEmbeddingBetti
public import NSP14.Semigroup.IntervalCompletion
public import NSP14.Homological.ActualTorTransport
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem ordinary_interval_betti_zero (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).TangentAlgebra k)) 0=1 := by
  exact (S.intervalAP he).maximalEmbedding_betti_zero k (by exact min_eq_right hw)

theorem ordinary_interval_betti (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).TangentAlgebra k)) i=
        i*S.multiplicity.choose (i+1) :=
  (S.intervalAP he).maximalEmbedding_betti k (by exact min_eq_right hw) i hi

theorem ordinary_interval_completed_betti_zero (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).FormalTangentAlgebra k)) 0=1 := by
  rw [← (S.intervalCompletion he).completed_totalBetti k,S.ordinary_interval_betti_zero k he hw]

theorem ordinary_interval_completed_betti (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).FormalTangentAlgebra k)) i=
        i*S.multiplicity.choose (i+1) := by
  rw [← (S.intervalCompletion he).completed_totalBetti k,S.ordinary_interval_betti k he hw i hi]
end NSP14.NumericalSemigroup
