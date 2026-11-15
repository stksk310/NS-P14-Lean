module
public import NSP14.Width.AntipodalComparison
public import tests.WidthFiveHigher
@[expose] public section
open NSP14.Homological
namespace NSP14.Tests.V06IntegerPayment

/-- The smallest antipodal height exercises the integer slack at h = 4. -/
example : 29 ≤ (2*4).choose 2+1 :=
  Width.antipodal_integer_payment 4 29 (by decide) (by norm_num)

/-- All four formerly separate widths use the same integer-payment lemma. -/
example (u b : ℕ) (hu : 8 ≤ u)
    (hb : (12:ℚ)*b+7*u ≤ 5*(u:ℚ)^2+90) : b ≤ u.choose 2+1 :=
  Width.nonAntipodal_integer_payment u b hu hb

example : 29 ≤ Nat.choose 8 2+1 :=
  Width.nonAntipodal_integer_payment 8 29 (by decide) (by norm_num)
example : 36 ≤ Nat.choose 9 2+1 :=
  Width.nonAntipodal_integer_payment 9 36 (by decide) (by norm_num)
example : 43 ≤ Nat.choose 10 2+1 :=
  Width.nonAntipodal_integer_payment 10 43 (by decide) (by norm_num)
example : 51 ≤ Nat.choose 11 2+1 :=
  Width.nonAntipodal_integer_payment 11 51 (by decide) (by norm_num)

def antipodal_four : Endpoint.Data where
  m := 10
  d := 1
  u := 8
  a := {1,4,5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem antipodal_four_shape :
    Additive.CyclicAntipodal antipodal_four.u antipodal_four.residueAlphabet := by
  refine ⟨4,1,rfl,by decide,by decide,by decide,?_⟩
  decide

theorem antipodal_four_actual (k : Type) [Field k] :
    totalBetti k antipodal_four.Variables (antipodal_four.fullG k) 1 ≤
      antipodal_four.u.choose 2+1 :=
  antipodal_four.actual_antipodal_first k rfl (by decide) antipodal_four_shape

/-- Coprimality is modulo h = 5, while t = 2 is not a unit modulo u = 10. -/
theorem antipodal_nonunit_shape :
    Additive.CyclicAntipodal FiveHigher.antipodal_nonunit.u
      FiveHigher.antipodal_nonunit.residueAlphabet := by
  refine ⟨5,2,rfl,by decide,by decide,by decide,?_⟩
  decide

theorem antipodal_nonunit_not_unit : ¬Nat.Coprime 2 FiveHigher.antipodal_nonunit.u := by
  decide

theorem antipodal_nonunit_actual (k : Type) [Field k] :
    totalBetti k FiveHigher.antipodal_nonunit.Variables
      (FiveHigher.antipodal_nonunit.fullG k) 1 ≤ FiveHigher.antipodal_nonunit.u.choose 2+1 :=
  FiveHigher.antipodal_nonunit.actual_antipodal_first k rfl (by decide)
    antipodal_nonunit_shape

example : totalBetti ℚ antipodal_four.Variables (antipodal_four.fullG ℚ) 1 ≤ 29 :=
  antipodal_four_actual ℚ
example : totalBetti (ZMod 2) antipodal_four.Variables
    (antipodal_four.fullG (ZMod 2)) 1 ≤ 29 := antipodal_four_actual (ZMod 2)
example : totalBetti (ZMod 3) antipodal_four.Variables
    (antipodal_four.fullG (ZMod 3)) 1 ≤ 29 := antipodal_four_actual (ZMod 3)
example : totalBetti ℚ FiveHigher.antipodal_nonunit.Variables
    (FiveHigher.antipodal_nonunit.fullG ℚ) 1 ≤ 46 := antipodal_nonunit_actual ℚ
example : totalBetti (ZMod 2) FiveHigher.antipodal_nonunit.Variables
    (FiveHigher.antipodal_nonunit.fullG (ZMod 2)) 1 ≤ 46 := antipodal_nonunit_actual (ZMod 2)
example : totalBetti (ZMod 3) FiveHigher.antipodal_nonunit.Variables
    (FiveHigher.antipodal_nonunit.fullG (ZMod 3)) 1 ≤ 46 := antipodal_nonunit_actual (ZMod 3)

end NSP14.Tests.V06IntegerPayment
