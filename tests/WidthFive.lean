module
public import audit.run18.FiveClosedGoals
public import NSP14.Width.AntipodalVolume
public import tests.WidthFiveHigher
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.Tests.Five

theorem frozen_contract : Run18.Requested.W_FIVE := Run18.five_closed

theorem original_all_rows (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=5) (hw : S.width ≤ S.multiplicity-2) :
    Run18.Requested.Comparison S k (by omega) := by
  exact Run18.five_closed S k he hw

def hole0 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem hole0_positive (k : Type) [Field k] (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k hole0.Variables (hole0.fullG k) i ≤ Target.apLowerProfile 5 i :=
  hole0.actual_five_hole_positive k rfl rfl i hi
theorem hole0_Q_row1 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 1 (by decide)
theorem hole0_Q_row2 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 2 (by decide)
theorem hole0_Q_row3 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 3 (by decide)
theorem hole0_Q_row4 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 4 (by decide)
theorem hole0_Q_row5 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 5 (by decide)
theorem hole0_Q_row6 : totalBetti (ℚ) hole0.Variables (hole0.fullG (ℚ)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ℚ) 6 (by decide)
theorem hole0_char2_row1 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 1 (by decide)
theorem hole0_char2_row2 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 2 (by decide)
theorem hole0_char2_row3 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 3 (by decide)
theorem hole0_char2_row4 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 4 (by decide)
theorem hole0_char2_row5 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 5 (by decide)
theorem hole0_char2_row6 : totalBetti (ZMod 2) hole0.Variables (hole0.fullG (ZMod 2)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 2) 6 (by decide)
theorem hole0_char3_row1 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 1 (by decide)
theorem hole0_char3_row2 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 2 (by decide)
theorem hole0_char3_row3 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 3 (by decide)
theorem hole0_char3_row4 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 4 (by decide)
theorem hole0_char3_row5 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 5 (by decide)
theorem hole0_char3_row6 : totalBetti (ZMod 3) hole0.Variables (hole0.fullG (ZMod 3)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole0_positive (ZMod 3) 6 (by decide)

def hole1 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := {1,2,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem hole1_positive (k : Type) [Field k] (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k hole1.Variables (hole1.fullG k) i ≤ Target.apLowerProfile 5 i :=
  hole1.actual_five_hole_positive k rfl rfl i hi
theorem hole1_Q_row1 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 1 (by decide)
theorem hole1_Q_row2 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 2 (by decide)
theorem hole1_Q_row3 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 3 (by decide)
theorem hole1_Q_row4 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 4 (by decide)
theorem hole1_Q_row5 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 5 (by decide)
theorem hole1_Q_row6 : totalBetti (ℚ) hole1.Variables (hole1.fullG (ℚ)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ℚ) 6 (by decide)
theorem hole1_char2_row1 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 1 (by decide)
theorem hole1_char2_row2 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 2 (by decide)
theorem hole1_char2_row3 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 3 (by decide)
theorem hole1_char2_row4 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 4 (by decide)
theorem hole1_char2_row5 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 5 (by decide)
theorem hole1_char2_row6 : totalBetti (ZMod 2) hole1.Variables (hole1.fullG (ZMod 2)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 2) 6 (by decide)
theorem hole1_char3_row1 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 1 (by decide)
theorem hole1_char3_row2 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 2 (by decide)
theorem hole1_char3_row3 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 3 (by decide)
theorem hole1_char3_row4 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 4 (by decide)
theorem hole1_char3_row5 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 5 (by decide)
theorem hole1_char3_row6 : totalBetti (ZMod 3) hole1.Variables (hole1.fullG (ZMod 3)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole1_positive (ZMod 3) 6 (by decide)

def hole2 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := {1,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem hole2_positive (k : Type) [Field k] (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k hole2.Variables (hole2.fullG k) i ≤ Target.apLowerProfile 5 i :=
  hole2.actual_five_hole_positive k rfl rfl i hi
theorem hole2_Q_row1 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 1 (by decide)
theorem hole2_Q_row2 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 2 (by decide)
theorem hole2_Q_row3 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 3 (by decide)
theorem hole2_Q_row4 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 4 (by decide)
theorem hole2_Q_row5 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 5 (by decide)
theorem hole2_Q_row6 : totalBetti (ℚ) hole2.Variables (hole2.fullG (ℚ)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ℚ) 6 (by decide)
theorem hole2_char2_row1 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 1 (by decide)
theorem hole2_char2_row2 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 2 (by decide)
theorem hole2_char2_row3 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 3 (by decide)
theorem hole2_char2_row4 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 4 (by decide)
theorem hole2_char2_row5 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 5 (by decide)
theorem hole2_char2_row6 : totalBetti (ZMod 2) hole2.Variables (hole2.fullG (ZMod 2)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 2) 6 (by decide)
theorem hole2_char3_row1 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 1 (by decide)
theorem hole2_char3_row2 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 2 (by decide)
theorem hole2_char3_row3 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 3 (by decide)
theorem hole2_char3_row4 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 4 (by decide)
theorem hole2_char3_row5 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 5 (by decide)
theorem hole2_char3_row6 : totalBetti (ZMod 3) hole2.Variables (hole2.fullG (ZMod 3)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole2_positive (ZMod 3) 6 (by decide)

def hole3 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := {2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

theorem hole3_positive (k : Type) [Field k] (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k hole3.Variables (hole3.fullG k) i ≤ Target.apLowerProfile 5 i :=
  hole3.actual_five_hole_positive k rfl rfl i hi
theorem hole3_Q_row1 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 1 (by decide)
theorem hole3_Q_row2 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 2 (by decide)
theorem hole3_Q_row3 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 3 (by decide)
theorem hole3_Q_row4 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 4 (by decide)
theorem hole3_Q_row5 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 5 (by decide)
theorem hole3_Q_row6 : totalBetti (ℚ) hole3.Variables (hole3.fullG (ℚ)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ℚ) 6 (by decide)
theorem hole3_char2_row1 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 1 (by decide)
theorem hole3_char2_row2 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 2 (by decide)
theorem hole3_char2_row3 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 3 (by decide)
theorem hole3_char2_row4 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 4 (by decide)
theorem hole3_char2_row5 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 5 (by decide)
theorem hole3_char2_row6 : totalBetti (ZMod 2) hole3.Variables (hole3.fullG (ZMod 2)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 2) 6 (by decide)
theorem hole3_char3_row1 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 1 ≤ 11 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 1 (by decide)
theorem hole3_char3_row2 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 2 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 2 (by decide)
theorem hole3_char3_row3 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 3 ≤ 25 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 3 (by decide)
theorem hole3_char3_row4 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 4 ≤ 9 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 4 (by decide)
theorem hole3_char3_row5 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 5 ≤ 1 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 5 (by decide)
theorem hole3_char3_row6 : totalBetti (ZMod 3) hole3.Variables (hole3.fullG (ZMod 3)) 6 ≤ 0 := by
  simpa [Target.apLowerProfile,Nat.choose] using hole3_positive (ZMod 3) 6 (by decide)

theorem original_data_all_rows (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=3) (hphys : D.d*D.u ≤ D.m-2) :
    Run18.Requested.Comparison D.source k (by rw [D.embeddingDimension,hq]; decide) := by
  apply Run18.five_closed D.source k
  · rw [D.embeddingDimension,hq]
  · rw [D.width,D.multiplicity]
    exact hphys

def boundary4 : Endpoint.Data where
  m := 14
  d := 3
  u := 4
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def boundary6 : Endpoint.Data where
  m := 20
  d := 3
  u := 6
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def boundary7 : Endpoint.Data where
  m := 23
  d := 3
  u := 7
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem boundary4_Q_original :
    Run18.Requested.Comparison boundary4.source (ℚ) (by rw [boundary4.embeddingDimension]; decide) :=
  original_data_all_rows boundary4 (ℚ) rfl (by decide)
theorem boundary4_char2_original :
    Run18.Requested.Comparison boundary4.source (ZMod 2) (by rw [boundary4.embeddingDimension]; decide) :=
  original_data_all_rows boundary4 (ZMod 2) rfl (by decide)
theorem boundary4_char3_original :
    Run18.Requested.Comparison boundary4.source (ZMod 3) (by rw [boundary4.embeddingDimension]; decide) :=
  original_data_all_rows boundary4 (ZMod 3) rfl (by decide)
theorem hole0_Q_original :
    Run18.Requested.Comparison hole0.source (ℚ) (by rw [hole0.embeddingDimension]; decide) :=
  original_data_all_rows hole0 (ℚ) rfl (by decide)
theorem hole0_char2_original :
    Run18.Requested.Comparison hole0.source (ZMod 2) (by rw [hole0.embeddingDimension]; decide) :=
  original_data_all_rows hole0 (ZMod 2) rfl (by decide)
theorem hole0_char3_original :
    Run18.Requested.Comparison hole0.source (ZMod 3) (by rw [hole0.embeddingDimension]; decide) :=
  original_data_all_rows hole0 (ZMod 3) rfl (by decide)
theorem hole1_Q_original :
    Run18.Requested.Comparison hole1.source (ℚ) (by rw [hole1.embeddingDimension]; decide) :=
  original_data_all_rows hole1 (ℚ) rfl (by decide)
theorem hole1_char2_original :
    Run18.Requested.Comparison hole1.source (ZMod 2) (by rw [hole1.embeddingDimension]; decide) :=
  original_data_all_rows hole1 (ZMod 2) rfl (by decide)
theorem hole1_char3_original :
    Run18.Requested.Comparison hole1.source (ZMod 3) (by rw [hole1.embeddingDimension]; decide) :=
  original_data_all_rows hole1 (ZMod 3) rfl (by decide)
theorem hole2_Q_original :
    Run18.Requested.Comparison hole2.source (ℚ) (by rw [hole2.embeddingDimension]; decide) :=
  original_data_all_rows hole2 (ℚ) rfl (by decide)
theorem hole2_char2_original :
    Run18.Requested.Comparison hole2.source (ZMod 2) (by rw [hole2.embeddingDimension]; decide) :=
  original_data_all_rows hole2 (ZMod 2) rfl (by decide)
theorem hole2_char3_original :
    Run18.Requested.Comparison hole2.source (ZMod 3) (by rw [hole2.embeddingDimension]; decide) :=
  original_data_all_rows hole2 (ZMod 3) rfl (by decide)
theorem hole3_Q_original :
    Run18.Requested.Comparison hole3.source (ℚ) (by rw [hole3.embeddingDimension]; decide) :=
  original_data_all_rows hole3 (ℚ) rfl (by decide)
theorem hole3_char2_original :
    Run18.Requested.Comparison hole3.source (ZMod 2) (by rw [hole3.embeddingDimension]; decide) :=
  original_data_all_rows hole3 (ZMod 2) rfl (by decide)
theorem hole3_char3_original :
    Run18.Requested.Comparison hole3.source (ZMod 3) (by rw [hole3.embeddingDimension]; decide) :=
  original_data_all_rows hole3 (ZMod 3) rfl (by decide)
theorem boundary6_Q_original :
    Run18.Requested.Comparison boundary6.source (ℚ) (by rw [boundary6.embeddingDimension]; decide) :=
  original_data_all_rows boundary6 (ℚ) rfl (by decide)
theorem boundary6_char2_original :
    Run18.Requested.Comparison boundary6.source (ZMod 2) (by rw [boundary6.embeddingDimension]; decide) :=
  original_data_all_rows boundary6 (ZMod 2) rfl (by decide)
theorem boundary6_char3_original :
    Run18.Requested.Comparison boundary6.source (ZMod 3) (by rw [boundary6.embeddingDimension]; decide) :=
  original_data_all_rows boundary6 (ZMod 3) rfl (by decide)
theorem boundary7_Q_original :
    Run18.Requested.Comparison boundary7.source (ℚ) (by rw [boundary7.embeddingDimension]; decide) :=
  original_data_all_rows boundary7 (ℚ) rfl (by decide)
theorem boundary7_char2_original :
    Run18.Requested.Comparison boundary7.source (ZMod 2) (by rw [boundary7.embeddingDimension]; decide) :=
  original_data_all_rows boundary7 (ZMod 2) rfl (by decide)
theorem boundary7_char3_original :
    Run18.Requested.Comparison boundary7.source (ZMod 3) (by rw [boundary7.embeddingDimension]; decide) :=
  original_data_all_rows boundary7 (ZMod 3) rfl (by decide)
theorem eight_Q_original :
    Run18.Requested.Comparison FiveHigher.eight.source (ℚ) (by rw [FiveHigher.eight.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.eight (ℚ) rfl (by decide)
theorem eight_char2_original :
    Run18.Requested.Comparison FiveHigher.eight.source (ZMod 2) (by rw [FiveHigher.eight.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.eight (ZMod 2) rfl (by decide)
theorem eight_char3_original :
    Run18.Requested.Comparison FiveHigher.eight.source (ZMod 3) (by rw [FiveHigher.eight.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.eight (ZMod 3) rfl (by decide)
theorem nine_Q_original :
    Run18.Requested.Comparison FiveHigher.nine.source (ℚ) (by rw [FiveHigher.nine.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.nine (ℚ) rfl (by decide)
theorem nine_char2_original :
    Run18.Requested.Comparison FiveHigher.nine.source (ZMod 2) (by rw [FiveHigher.nine.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.nine (ZMod 2) rfl (by decide)
theorem nine_char3_original :
    Run18.Requested.Comparison FiveHigher.nine.source (ZMod 3) (by rw [FiveHigher.nine.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.nine (ZMod 3) rfl (by decide)
theorem antipodal_nonunit_Q_original :
    Run18.Requested.Comparison FiveHigher.antipodal_nonunit.source (ℚ) (by rw [FiveHigher.antipodal_nonunit.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.antipodal_nonunit (ℚ) rfl (by decide)
theorem antipodal_nonunit_char2_original :
    Run18.Requested.Comparison FiveHigher.antipodal_nonunit.source (ZMod 2) (by rw [FiveHigher.antipodal_nonunit.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.antipodal_nonunit (ZMod 2) rfl (by decide)
theorem antipodal_nonunit_char3_original :
    Run18.Requested.Comparison FiveHigher.antipodal_nonunit.source (ZMod 3) (by rw [FiveHigher.antipodal_nonunit.embeddingDimension]; decide) :=
  original_data_all_rows FiveHigher.antipodal_nonunit (ZMod 3) rfl (by decide)
end NSP14.Tests.Five
