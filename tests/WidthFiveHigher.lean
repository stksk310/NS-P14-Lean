module
public import NSP14.Width.FiveHigher
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14.Homological
namespace NSP14.Tests.FiveHigher
theorem actual_positive_rows (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=3) (hu : 8 ≤ D.u) (i : ℕ) (hi : 2 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ i*D.u.choose (i+1) :=
  D.actual_five_higher k hq hu i hi


def eight : Endpoint.Data where
  m := 10
  d := 1
  u := 8
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem eight_Q (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ℚ) eight.Variables (eight.fullG (ℚ)) i ≤ i*eight.u.choose (i+1) :=
  eight.actual_five_higher (ℚ) rfl (by decide) i hi
theorem eight_char2 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 2) eight.Variables (eight.fullG (ZMod 2)) i ≤ i*eight.u.choose (i+1) :=
  eight.actual_five_higher (ZMod 2) rfl (by decide) i hi
theorem eight_char3 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 3) eight.Variables (eight.fullG (ZMod 3)) i ≤ i*eight.u.choose (i+1) :=
  eight.actual_five_higher (ZMod 3) rfl (by decide) i hi

def nine : Endpoint.Data where
  m := 11
  d := 1
  u := 9
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem nine_Q (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ℚ) nine.Variables (nine.fullG (ℚ)) i ≤ i*nine.u.choose (i+1) :=
  nine.actual_five_higher (ℚ) rfl (by decide) i hi
theorem nine_char2 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 2) nine.Variables (nine.fullG (ZMod 2)) i ≤ i*nine.u.choose (i+1) :=
  nine.actual_five_higher (ZMod 2) rfl (by decide) i hi
theorem nine_char3 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 3) nine.Variables (nine.fullG (ZMod 3)) i ≤ i*nine.u.choose (i+1) :=
  nine.actual_five_higher (ZMod 3) rfl (by decide) i hi

def ten : Endpoint.Data where
  m := 12
  d := 1
  u := 10
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem ten_Q (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ℚ) ten.Variables (ten.fullG (ℚ)) i ≤ i*ten.u.choose (i+1) :=
  ten.actual_five_higher (ℚ) rfl (by decide) i hi
theorem ten_char2 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 2) ten.Variables (ten.fullG (ZMod 2)) i ≤ i*ten.u.choose (i+1) :=
  ten.actual_five_higher (ZMod 2) rfl (by decide) i hi
theorem ten_char3 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 3) ten.Variables (ten.fullG (ZMod 3)) i ≤ i*ten.u.choose (i+1) :=
  ten.actual_five_higher (ZMod 3) rfl (by decide) i hi

def antipodal_nonunit : Endpoint.Data where
  m := 32
  d := 3
  u := 10
  a := {2,5,7}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem antipodal_nonunit_Q (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ℚ) antipodal_nonunit.Variables (antipodal_nonunit.fullG (ℚ)) i ≤ i*antipodal_nonunit.u.choose (i+1) :=
  antipodal_nonunit.actual_five_higher (ℚ) rfl (by decide) i hi
theorem antipodal_nonunit_char2 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 2) antipodal_nonunit.Variables (antipodal_nonunit.fullG (ZMod 2)) i ≤ i*antipodal_nonunit.u.choose (i+1) :=
  antipodal_nonunit.actual_five_higher (ZMod 2) rfl (by decide) i hi
theorem antipodal_nonunit_char3 (i : ℕ) (hi : 2 ≤ i) :
    totalBetti (ZMod 3) antipodal_nonunit.Variables (antipodal_nonunit.fullG (ZMod 3)) i ≤ i*antipodal_nonunit.u.choose (i+1) :=
  antipodal_nonunit.actual_five_higher (ZMod 3) rfl (by decide) i hi
end NSP14.Tests.FiveHigher
