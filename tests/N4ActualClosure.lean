module
import NSP14.NarrowFour.Comparison
import Mathlib.Algebra.Field.ZMod
open NSP14

example (S : NumericalSemigroup) (k : Type) [Field k] (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) := NarrowFour.narrow_four_comparison S k he hw
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S ℚ he hw 0
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S (ZMod 2) he hw 4
example (S : NumericalSemigroup) (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :=
  NarrowFour.narrow_four_comparison S (ZMod 3) he hw 5
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hm : D.d*D.u+2 ≤ D.m) :=
  NarrowFour.narrow_four_comparison D.source k (by rw [D.embeddingDimension,hq])
    (by rw [D.width,D.multiplicity];omega)
