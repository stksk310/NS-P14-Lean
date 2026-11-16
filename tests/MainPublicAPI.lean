module
public import NSP14.Main
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run20Public
theorem arbitrary_field (S : NumericalSemigroup) (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k S.intervalCompletionAll.AtomExponent
      (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
        (S.intervalCompletionAll.FormalTangentAlgebra k)) i :=
  S.p14_totalBetti_le_intervalCompletion k i
theorem rational (S : NumericalSemigroup) (i : ℕ) : S.IntervalComparison ℚ i := S.p14_totalBetti_le_intervalCompletion ℚ i
theorem char_two (S : NumericalSemigroup) (i : ℕ) : S.IntervalComparison (ZMod 2) i := S.p14_totalBetti_le_intervalCompletion (ZMod 2) i
theorem char_three (S : NumericalSemigroup) (i : ℕ) : S.IntervalComparison (ZMod 3) i := S.p14_totalBetti_le_intervalCompletion (ZMod 3) i
end NSP14.Tests.Run20Public
