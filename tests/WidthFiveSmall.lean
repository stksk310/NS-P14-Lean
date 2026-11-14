module
public import NSP14.Width.FiveSmall
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.Tests.FiveSmall
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem actual_all_rows (he : S.embeddingDimension=5) (hw : S.width ≤ S.multiplicity-2)
    (hu : S.normalizedWidth=6 ∨ S.normalizedWidth=7) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i :=
  S.narrow_five_small_comparison k he hw hu i
end NSP14.Tests.FiveSmall
