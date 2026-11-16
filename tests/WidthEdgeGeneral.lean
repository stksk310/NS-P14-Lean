module
public import audit.run18.EdgeClosedGoals
public import NSP14.Width.SourceNormalization
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.Tests.EdgeGeneral

theorem frozen_contract : Run18.Requested.W_EDGE := Run18.edge_closed

theorem original_one_hole (D : Endpoint.Data) (k : Type) [Field k]
    (hq : 3 ≤ D.q) (hu : D.u=D.q+2) (hphys : D.d*D.u ≤ D.m-2) :
    Run18.Requested.Comparison D.source k (by rw [D.embeddingDimension]; omega) := by
  have he : 5 ≤ D.source.embeddingDimension := by rw [D.embeddingDimension]; omega
  have hw : D.source.width ≤ D.source.multiplicity-2 := by rw [D.width,D.multiplicity]; exact hphys
  have hq' := D.source.endpointData_embedding (by omega) hw
  have hu' : (D.source.endpointData (by omega) hw).u=(D.source.endpointData (by omega) hw).q+2 := by
    change D.source.normalizedWidth=_
    rw [D.source_normalizedWidth]
    have hqq := hq'.trans D.embeddingDimension
    omega
  exact fun i => D.source.narrow_oneHole_comparison k he hw hu' i

def q3_hole1 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := Finset.Ioo 0 5 \ {1}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_hole1_Q :
    Run18.Requested.Comparison q3_hole1.source (ℚ) (by rw [q3_hole1.embeddingDimension]; decide) :=
  original_one_hole q3_hole1 (ℚ) (by decide) (by decide) (by decide)
theorem q3_hole1_char2 :
    Run18.Requested.Comparison q3_hole1.source (ZMod 2) (by rw [q3_hole1.embeddingDimension]; decide) :=
  original_one_hole q3_hole1 (ZMod 2) (by decide) (by decide) (by decide)
theorem q3_hole1_char3 :
    Run18.Requested.Comparison q3_hole1.source (ZMod 3) (by rw [q3_hole1.embeddingDimension]; decide) :=
  original_one_hole q3_hole1 (ZMod 3) (by decide) (by decide) (by decide)

def q3_hole2 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := Finset.Ioo 0 5 \ {2}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_hole2_Q :
    Run18.Requested.Comparison q3_hole2.source (ℚ) (by rw [q3_hole2.embeddingDimension]; decide) :=
  original_one_hole q3_hole2 (ℚ) (by decide) (by decide) (by decide)
theorem q3_hole2_char2 :
    Run18.Requested.Comparison q3_hole2.source (ZMod 2) (by rw [q3_hole2.embeddingDimension]; decide) :=
  original_one_hole q3_hole2 (ZMod 2) (by decide) (by decide) (by decide)
theorem q3_hole2_char3 :
    Run18.Requested.Comparison q3_hole2.source (ZMod 3) (by rw [q3_hole2.embeddingDimension]; decide) :=
  original_one_hole q3_hole2 (ZMod 3) (by decide) (by decide) (by decide)

def q3_hole3 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := Finset.Ioo 0 5 \ {3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_hole3_Q :
    Run18.Requested.Comparison q3_hole3.source (ℚ) (by rw [q3_hole3.embeddingDimension]; decide) :=
  original_one_hole q3_hole3 (ℚ) (by decide) (by decide) (by decide)
theorem q3_hole3_char2 :
    Run18.Requested.Comparison q3_hole3.source (ZMod 2) (by rw [q3_hole3.embeddingDimension]; decide) :=
  original_one_hole q3_hole3 (ZMod 2) (by decide) (by decide) (by decide)
theorem q3_hole3_char3 :
    Run18.Requested.Comparison q3_hole3.source (ZMod 3) (by rw [q3_hole3.embeddingDimension]; decide) :=
  original_one_hole q3_hole3 (ZMod 3) (by decide) (by decide) (by decide)

def q3_hole4 : Endpoint.Data where
  m := 17
  d := 3
  u := 5
  a := Finset.Ioo 0 5 \ {4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_hole4_Q :
    Run18.Requested.Comparison q3_hole4.source (ℚ) (by rw [q3_hole4.embeddingDimension]; decide) :=
  original_one_hole q3_hole4 (ℚ) (by decide) (by decide) (by decide)
theorem q3_hole4_char2 :
    Run18.Requested.Comparison q3_hole4.source (ZMod 2) (by rw [q3_hole4.embeddingDimension]; decide) :=
  original_one_hole q3_hole4 (ZMod 2) (by decide) (by decide) (by decide)
theorem q3_hole4_char3 :
    Run18.Requested.Comparison q3_hole4.source (ZMod 3) (by rw [q3_hole4.embeddingDimension]; decide) :=
  original_one_hole q3_hole4 (ZMod 3) (by decide) (by decide) (by decide)

def q4_hole1 : Endpoint.Data where
  m := 20
  d := 3
  u := 6
  a := Finset.Ioo 0 6 \ {1}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_hole1_Q :
    Run18.Requested.Comparison q4_hole1.source (ℚ) (by rw [q4_hole1.embeddingDimension]; decide) :=
  original_one_hole q4_hole1 (ℚ) (by decide) (by decide) (by decide)
theorem q4_hole1_char2 :
    Run18.Requested.Comparison q4_hole1.source (ZMod 2) (by rw [q4_hole1.embeddingDimension]; decide) :=
  original_one_hole q4_hole1 (ZMod 2) (by decide) (by decide) (by decide)
theorem q4_hole1_char3 :
    Run18.Requested.Comparison q4_hole1.source (ZMod 3) (by rw [q4_hole1.embeddingDimension]; decide) :=
  original_one_hole q4_hole1 (ZMod 3) (by decide) (by decide) (by decide)

def q4_hole3 : Endpoint.Data where
  m := 20
  d := 3
  u := 6
  a := Finset.Ioo 0 6 \ {3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_hole3_Q :
    Run18.Requested.Comparison q4_hole3.source (ℚ) (by rw [q4_hole3.embeddingDimension]; decide) :=
  original_one_hole q4_hole3 (ℚ) (by decide) (by decide) (by decide)
theorem q4_hole3_char2 :
    Run18.Requested.Comparison q4_hole3.source (ZMod 2) (by rw [q4_hole3.embeddingDimension]; decide) :=
  original_one_hole q4_hole3 (ZMod 2) (by decide) (by decide) (by decide)
theorem q4_hole3_char3 :
    Run18.Requested.Comparison q4_hole3.source (ZMod 3) (by rw [q4_hole3.embeddingDimension]; decide) :=
  original_one_hole q4_hole3 (ZMod 3) (by decide) (by decide) (by decide)

def q4_hole5 : Endpoint.Data where
  m := 20
  d := 3
  u := 6
  a := Finset.Ioo 0 6 \ {5}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_hole5_Q :
    Run18.Requested.Comparison q4_hole5.source (ℚ) (by rw [q4_hole5.embeddingDimension]; decide) :=
  original_one_hole q4_hole5 (ℚ) (by decide) (by decide) (by decide)
theorem q4_hole5_char2 :
    Run18.Requested.Comparison q4_hole5.source (ZMod 2) (by rw [q4_hole5.embeddingDimension]; decide) :=
  original_one_hole q4_hole5 (ZMod 2) (by decide) (by decide) (by decide)
theorem q4_hole5_char3 :
    Run18.Requested.Comparison q4_hole5.source (ZMod 3) (by rw [q4_hole5.embeddingDimension]; decide) :=
  original_one_hole q4_hole5 (ZMod 3) (by decide) (by decide) (by decide)

def q5_hole1 : Endpoint.Data where
  m := 23
  d := 3
  u := 7
  a := Finset.Ioo 0 7 \ {1}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q5_hole1_Q :
    Run18.Requested.Comparison q5_hole1.source (ℚ) (by rw [q5_hole1.embeddingDimension]; decide) :=
  original_one_hole q5_hole1 (ℚ) (by decide) (by decide) (by decide)
theorem q5_hole1_char2 :
    Run18.Requested.Comparison q5_hole1.source (ZMod 2) (by rw [q5_hole1.embeddingDimension]; decide) :=
  original_one_hole q5_hole1 (ZMod 2) (by decide) (by decide) (by decide)
theorem q5_hole1_char3 :
    Run18.Requested.Comparison q5_hole1.source (ZMod 3) (by rw [q5_hole1.embeddingDimension]; decide) :=
  original_one_hole q5_hole1 (ZMod 3) (by decide) (by decide) (by decide)

def q5_hole3 : Endpoint.Data where
  m := 23
  d := 3
  u := 7
  a := Finset.Ioo 0 7 \ {3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q5_hole3_Q :
    Run18.Requested.Comparison q5_hole3.source (ℚ) (by rw [q5_hole3.embeddingDimension]; decide) :=
  original_one_hole q5_hole3 (ℚ) (by decide) (by decide) (by decide)
theorem q5_hole3_char2 :
    Run18.Requested.Comparison q5_hole3.source (ZMod 2) (by rw [q5_hole3.embeddingDimension]; decide) :=
  original_one_hole q5_hole3 (ZMod 2) (by decide) (by decide) (by decide)
theorem q5_hole3_char3 :
    Run18.Requested.Comparison q5_hole3.source (ZMod 3) (by rw [q5_hole3.embeddingDimension]; decide) :=
  original_one_hole q5_hole3 (ZMod 3) (by decide) (by decide) (by decide)

def q5_hole6 : Endpoint.Data where
  m := 23
  d := 3
  u := 7
  a := Finset.Ioo 0 7 \ {6}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q5_hole6_Q :
    Run18.Requested.Comparison q5_hole6.source (ℚ) (by rw [q5_hole6.embeddingDimension]; decide) :=
  original_one_hole q5_hole6 (ℚ) (by decide) (by decide) (by decide)
theorem q5_hole6_char2 :
    Run18.Requested.Comparison q5_hole6.source (ZMod 2) (by rw [q5_hole6.embeddingDimension]; decide) :=
  original_one_hole q5_hole6 (ZMod 2) (by decide) (by decide) (by decide)
theorem q5_hole6_char3 :
    Run18.Requested.Comparison q5_hole6.source (ZMod 3) (by rw [q5_hole6.embeddingDimension]; decide) :=
  original_one_hole q5_hole6 (ZMod 3) (by decide) (by decide) (by decide)

def q6_hole4 : Endpoint.Data where
  m := 26
  d := 3
  u := 8
  a := Finset.Ioo 0 8 \ {4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q6_hole4_Q :
    Run18.Requested.Comparison q6_hole4.source (ℚ) (by rw [q6_hole4.embeddingDimension]; decide) :=
  original_one_hole q6_hole4 (ℚ) (by decide) (by decide) (by decide)
theorem q6_hole4_char2 :
    Run18.Requested.Comparison q6_hole4.source (ZMod 2) (by rw [q6_hole4.embeddingDimension]; decide) :=
  original_one_hole q6_hole4 (ZMod 2) (by decide) (by decide) (by decide)
theorem q6_hole4_char3 :
    Run18.Requested.Comparison q6_hole4.source (ZMod 3) (by rw [q6_hole4.embeddingDimension]; decide) :=
  original_one_hole q6_hole4 (ZMod 3) (by decide) (by decide) (by decide)

def q9_hole2 : Endpoint.Data where
  m := 35
  d := 3
  u := 11
  a := Finset.Ioo 0 11 \ {2}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q9_hole2_Q :
    Run18.Requested.Comparison q9_hole2.source (ℚ) (by rw [q9_hole2.embeddingDimension]; decide) :=
  original_one_hole q9_hole2 (ℚ) (by decide) (by decide) (by decide)
theorem q9_hole2_char2 :
    Run18.Requested.Comparison q9_hole2.source (ZMod 2) (by rw [q9_hole2.embeddingDimension]; decide) :=
  original_one_hole q9_hole2 (ZMod 2) (by decide) (by decide) (by decide)
theorem q9_hole2_char3 :
    Run18.Requested.Comparison q9_hole2.source (ZMod 3) (by rw [q9_hole2.embeddingDimension]; decide) :=
  original_one_hole q9_hole2 (ZMod 3) (by decide) (by decide) (by decide)
end NSP14.Tests.EdgeGeneral
