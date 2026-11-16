module
public import NSP14.NarrowFour.HigherRows
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open NSP14 NSP14.Homological

example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hu : 6 ≤ D.u)
    (i : ℕ) (hi : 2 ≤ i) : totalBetti k D.Variables (D.fullG k) i ≤ i*D.u.choose (i+1) :=
  NarrowFour.actual_large_higher D k hq hu i hi
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hu : D.u=4) :
    totalBetti k D.Variables (D.fullG k) 2 ≤ 12 ∧
    totalBetti k D.Variables (D.fullG k) 3 ≤ 5 ∧
    totalBetti k D.Variables (D.fullG k) 4=0 := NarrowFour.actual_width_four_higher D k hq hu
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hu : D.u=5) :
    totalBetti k D.Variables (D.fullG k) 2 ≤ 18 ∧
    totalBetti k D.Variables (D.fullG k) 3 ≤ 7 ∧
    totalBetti k D.Variables (D.fullG k) 4=0 := NarrowFour.actual_small_higher D k hq (by omega)

namespace NSP14.Tests.Run19Higher
theorem heTwo (S : NumericalSemigroup) (he : S.embeddingDimension=4) : 2 ≤ S.embeddingDimension := by omega
theorem all_fields (S : NumericalSemigroup) (he : S.embeddingDimension=4)
  (hw : S.width ≤ S.multiplicity-2) (k : Type) [Field k] (i : ℕ) (hi : 2 ≤ i) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion (heTwo S he)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (heTwo S he)).FullPolynomialRing k)
          ((S.intervalCompletion (heTwo S he)).FormalTangentAlgebra k)) i :=
  NarrowFour.narrow_four_higher S k he hw i hi
variable (S : NumericalSemigroup) (he : S.embeddingDimension=4)
  (hw : S.width ≤ S.multiplicity-2)
example := all_fields S he hw ℚ 2 (by omega)
example := all_fields S he hw (ZMod 2) 3 (by omega)
example := all_fields S he hw (ZMod 3) 4 (by omega)
example := all_fields S he hw ℚ 5 (by omega)
example (ht : 2 ≤ (S.intervalCompletion (heTwo S he)).embeddingDimension) :=
  all_fields S he hw (ZMod 2) (S.intervalCompletion (heTwo S he)).embeddingDimension ht
end NSP14.Tests.Run19Higher
