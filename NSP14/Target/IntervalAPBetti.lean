module
public import NSP14.ArithmeticSequence.ProfileBounds
public import NSP14.Target.IntervalBetti
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem interval_betti_profile (he : 2 ≤ S.embeddingDimension) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).TangentAlgebra k)) i=
        (S.intervalAP he).positiveBettiProfile i :=
  (S.intervalAP he).cone_totalBetti_pos k i hi

theorem interval_completed_betti_profile (he : 2 ≤ S.embeddingDimension) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).FormalTangentAlgebra k)) i=
        (S.intervalAP he).positiveBettiProfile i := by
  rw [← (S.intervalCompletion he).completed_totalBetti k,S.interval_betti_profile k he i hi]

theorem interval_completed_betti_zero (he : 2 ≤ S.embeddingDimension) :
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).FormalTangentAlgebra k)) 0=1 :=
  (S.intervalCompletion he).completed_totalBetti_zero k

theorem interval_completed_betti_lower (he : 2 ≤ S.embeddingDimension) (i : ℕ) (hi : 1 ≤ i) :
    NSP14.Target.apLowerProfile (min S.width (S.multiplicity-1)) i ≤
      totalBetti k (S.intervalCompletion he).AtomExponent
        (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k) ((S.intervalCompletion he).FormalTangentAlgebra k)) i := by
  rw [S.interval_completed_betti_profile k he i hi]
  exact (S.intervalAP he).positiveBettiProfile_lower i
end NSP14.NumericalSemigroup
