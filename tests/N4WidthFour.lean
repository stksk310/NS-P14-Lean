module
public import NSP14.NarrowFour.WidthFourComparison
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.NarrowFour.WidthFour
namespace NSP14.Tests.Run19WidthFour

def data (m : ℕ) (hm : 6 ≤ m) : Endpoint.Data where
  m := m
  d := 1
  u := 4
  a := {1,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by omega
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by simp

example (m : ℕ) (hm : 6 ≤ m) (p : Column) (k : Type) [Field k] :
    (data m hm).coreToG k ((data m hm).coreMonomial k (columnPoint (data m hm) rfl p))=0 ↔
      theta m (anchorN p.anchor) ≤ p.K := column_zero_iff (data m hm) k hm rfl rfl rfl p
example (m : ℕ) (hm : 6 ≤ m) (p : Column) := column_zero_iff (data m hm) ℚ hm rfl rfl rfl p
example (m : ℕ) (hm : 6 ≤ m) (p : Column) := column_zero_iff (data m hm) (ZMod 2) hm rfl rfl rfl p
example (m : ℕ) (hm : 6 ≤ m) (p : Column) := column_zero_iff (data m hm) (ZMod 3) hm rfl rfl rfl p
example (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) (j : ℕ) (hj : 1 ≤ j) : delta m i j<0 := delta_neg m hm i j hj
example (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) (K : ℕ) := all_j_threshold m hm i K

example (m : ℕ) (hm : 6 ≤ m) (k : Type) [Field k] :=
  actual_first_bound (data m hm) k hm rfl rfl rfl
example (m : ℕ) (hm : 6 ≤ m) (k : Type) [Field k] :=
  width_four_comparison (data m hm) k rfl hm rfl rfl rfl
example := actual_first_bound (data 6 (by omega)) ℚ (by change 6 ≤ 6;omega) rfl rfl rfl
example := actual_first_bound (data 7 (by omega)) (ZMod 2) (by change 6 ≤ 7;omega) rfl rfl rfl
example := actual_first_bound (data 8 (by omega)) (ZMod 3) (by change 6 ≤ 8;omega) rfl rfl rfl
example := actual_first_bound (data 9 (by omega)) (ZMod 2) (by change 6 ≤ 9;omega) rfl rfl rfl
example := actual_first_bound (data 10 (by omega)) ℚ (by change 6 ≤ 10;omega) rfl rfl rfl
example (Q : ℕ) (hQ : 2 ≤ Q) := theta_four_zero Q hQ
example (Q : ℕ) (hQ : 2 ≤ Q) := theta_four_one Q hQ
example (Q : ℕ) (hQ : 2 ≤ Q) := theta_four_two Q hQ
example (Q : ℕ) (hQ : 1 ≤ Q) := theta_four_three Q hQ
end NSP14.Tests.Run19WidthFour
