module
import NSP14.NarrowFour.SmallWidths
import Mathlib.Algebra.Field.ZMod
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run19Small

def six : Endpoint.Data where
  m := 8
  d := 1
  u := 6
  a := {1,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def seven : Endpoint.Data where
  m := 9
  d := 1
  u := 7
  a := {2,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def eight : Endpoint.Data where
  m := 10
  d := 1
  u := 8
  a := {1,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

example (k : Type) [Field k] : totalBetti k six.Variables (six.fullG k) 1 ≤ 16 :=
  NarrowFour.actual_first_six six k rfl rfl
example : totalBetti ℚ seven.Variables (seven.fullG ℚ) 1 ≤ 22 := NarrowFour.actual_first_7 seven ℚ rfl rfl
example : totalBetti (ZMod 2) seven.Variables (seven.fullG (ZMod 2)) 1 ≤ 22 :=
  NarrowFour.actual_first_7 seven (ZMod 2) rfl rfl
example : totalBetti (ZMod 3) eight.Variables (eight.fullG (ZMod 3)) 1 ≤ 29 :=
  NarrowFour.actual_first_8 eight (ZMod 3) rfl rfl

example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (a b : D.a)
    (hab : NarrowFour.OrderedPair D a b) (hS : ¬NarrowFour.Standard D a b (2,0))
    (hT : ¬NarrowFour.Standard D a b (0,2)) : D.coreP k+D.internalSigma k hq ≤ 5 :=
  NarrowFour.box_two_joint D k hq a b hab hS hT

example (S : NumericalSemigroup) (k : Type) [Field k] (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) := NarrowFour.narrow_four_small S k he hw
end NSP14.Tests.Run19Small
