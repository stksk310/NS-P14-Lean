module
public import NSP14.Width.DenseResources
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace NSP14.Tests.DenseResources
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_resources (t : ℕ) (hu : D.u=D.q+1+t) (ht : t ≤ D.q) :
    D.wordVolume=D.q+1+2*t ∧ D.coreP k ≤ D.q+1+2*t ∧ D.actualR k ≤ t ∧
    (t ≤ 2 → D.actualR k=0) ∧ D.coreHeight ≤ t :=
  D.dense_resources k t hu ht


def q3_t0 : Endpoint.Data where
  m := 6
  d := 1
  u := 4
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_t0_Q :
    q3_t0.wordVolume=4 ∧ q3_t0.coreP (ℚ) ≤ 4 ∧
    q3_t0.actualR (ℚ) ≤ 0 ∧ (0 ≤ 2 → q3_t0.actualR (ℚ)=0) ∧
    q3_t0.coreHeight ≤ 0 := by
  simpa only [show q3_t0.q=3 from rfl] using
    q3_t0.dense_resources (ℚ) 0 (by decide) (by decide)
theorem q3_t0_char2 :
    q3_t0.wordVolume=4 ∧ q3_t0.coreP (ZMod 2) ≤ 4 ∧
    q3_t0.actualR (ZMod 2) ≤ 0 ∧ (0 ≤ 2 → q3_t0.actualR (ZMod 2)=0) ∧
    q3_t0.coreHeight ≤ 0 := by
  simpa only [show q3_t0.q=3 from rfl] using
    q3_t0.dense_resources (ZMod 2) 0 (by decide) (by decide)
theorem q3_t0_char3 :
    q3_t0.wordVolume=4 ∧ q3_t0.coreP (ZMod 3) ≤ 4 ∧
    q3_t0.actualR (ZMod 3) ≤ 0 ∧ (0 ≤ 2 → q3_t0.actualR (ZMod 3)=0) ∧
    q3_t0.coreHeight ≤ 0 := by
  simpa only [show q3_t0.q=3 from rfl] using
    q3_t0.dense_resources (ZMod 3) 0 (by decide) (by decide)
def q3_t1 : Endpoint.Data where
  m := 7
  d := 1
  u := 5
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_t1_Q :
    q3_t1.wordVolume=6 ∧ q3_t1.coreP (ℚ) ≤ 6 ∧
    q3_t1.actualR (ℚ) ≤ 1 ∧ (1 ≤ 2 → q3_t1.actualR (ℚ)=0) ∧
    q3_t1.coreHeight ≤ 1 := by
  simpa only [show q3_t1.q=3 from rfl] using
    q3_t1.dense_resources (ℚ) 1 (by decide) (by decide)
theorem q3_t1_char2 :
    q3_t1.wordVolume=6 ∧ q3_t1.coreP (ZMod 2) ≤ 6 ∧
    q3_t1.actualR (ZMod 2) ≤ 1 ∧ (1 ≤ 2 → q3_t1.actualR (ZMod 2)=0) ∧
    q3_t1.coreHeight ≤ 1 := by
  simpa only [show q3_t1.q=3 from rfl] using
    q3_t1.dense_resources (ZMod 2) 1 (by decide) (by decide)
theorem q3_t1_char3 :
    q3_t1.wordVolume=6 ∧ q3_t1.coreP (ZMod 3) ≤ 6 ∧
    q3_t1.actualR (ZMod 3) ≤ 1 ∧ (1 ≤ 2 → q3_t1.actualR (ZMod 3)=0) ∧
    q3_t1.coreHeight ≤ 1 := by
  simpa only [show q3_t1.q=3 from rfl] using
    q3_t1.dense_resources (ZMod 3) 1 (by decide) (by decide)
def q3_t2 : Endpoint.Data where
  m := 8
  d := 1
  u := 6
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_t2_Q :
    q3_t2.wordVolume=8 ∧ q3_t2.coreP (ℚ) ≤ 8 ∧
    q3_t2.actualR (ℚ) ≤ 2 ∧ (2 ≤ 2 → q3_t2.actualR (ℚ)=0) ∧
    q3_t2.coreHeight ≤ 2 := by
  simpa only [show q3_t2.q=3 from rfl] using
    q3_t2.dense_resources (ℚ) 2 (by decide) (by decide)
theorem q3_t2_char2 :
    q3_t2.wordVolume=8 ∧ q3_t2.coreP (ZMod 2) ≤ 8 ∧
    q3_t2.actualR (ZMod 2) ≤ 2 ∧ (2 ≤ 2 → q3_t2.actualR (ZMod 2)=0) ∧
    q3_t2.coreHeight ≤ 2 := by
  simpa only [show q3_t2.q=3 from rfl] using
    q3_t2.dense_resources (ZMod 2) 2 (by decide) (by decide)
theorem q3_t2_char3 :
    q3_t2.wordVolume=8 ∧ q3_t2.coreP (ZMod 3) ≤ 8 ∧
    q3_t2.actualR (ZMod 3) ≤ 2 ∧ (2 ≤ 2 → q3_t2.actualR (ZMod 3)=0) ∧
    q3_t2.coreHeight ≤ 2 := by
  simpa only [show q3_t2.q=3 from rfl] using
    q3_t2.dense_resources (ZMod 3) 2 (by decide) (by decide)
def q3_t3 : Endpoint.Data where
  m := 9
  d := 1
  u := 7
  a := {1,2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q3_t3_Q :
    q3_t3.wordVolume=10 ∧ q3_t3.coreP (ℚ) ≤ 10 ∧
    q3_t3.actualR (ℚ) ≤ 3 ∧ (3 ≤ 2 → q3_t3.actualR (ℚ)=0) ∧
    q3_t3.coreHeight ≤ 3 := by
  simpa only [show q3_t3.q=3 from rfl] using
    q3_t3.dense_resources (ℚ) 3 (by decide) (by decide)
theorem q3_t3_char2 :
    q3_t3.wordVolume=10 ∧ q3_t3.coreP (ZMod 2) ≤ 10 ∧
    q3_t3.actualR (ZMod 2) ≤ 3 ∧ (3 ≤ 2 → q3_t3.actualR (ZMod 2)=0) ∧
    q3_t3.coreHeight ≤ 3 := by
  simpa only [show q3_t3.q=3 from rfl] using
    q3_t3.dense_resources (ZMod 2) 3 (by decide) (by decide)
theorem q3_t3_char3 :
    q3_t3.wordVolume=10 ∧ q3_t3.coreP (ZMod 3) ≤ 10 ∧
    q3_t3.actualR (ZMod 3) ≤ 3 ∧ (3 ≤ 2 → q3_t3.actualR (ZMod 3)=0) ∧
    q3_t3.coreHeight ≤ 3 := by
  simpa only [show q3_t3.q=3 from rfl] using
    q3_t3.dense_resources (ZMod 3) 3 (by decide) (by decide)
def q4_t2 : Endpoint.Data where
  m := 9
  d := 1
  u := 7
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_t2_Q :
    q4_t2.wordVolume=9 ∧ q4_t2.coreP (ℚ) ≤ 9 ∧
    q4_t2.actualR (ℚ) ≤ 2 ∧ (2 ≤ 2 → q4_t2.actualR (ℚ)=0) ∧
    q4_t2.coreHeight ≤ 2 := by
  simpa only [show q4_t2.q=4 from rfl] using
    q4_t2.dense_resources (ℚ) 2 (by decide) (by decide)
theorem q4_t2_char2 :
    q4_t2.wordVolume=9 ∧ q4_t2.coreP (ZMod 2) ≤ 9 ∧
    q4_t2.actualR (ZMod 2) ≤ 2 ∧ (2 ≤ 2 → q4_t2.actualR (ZMod 2)=0) ∧
    q4_t2.coreHeight ≤ 2 := by
  simpa only [show q4_t2.q=4 from rfl] using
    q4_t2.dense_resources (ZMod 2) 2 (by decide) (by decide)
theorem q4_t2_char3 :
    q4_t2.wordVolume=9 ∧ q4_t2.coreP (ZMod 3) ≤ 9 ∧
    q4_t2.actualR (ZMod 3) ≤ 2 ∧ (2 ≤ 2 → q4_t2.actualR (ZMod 3)=0) ∧
    q4_t2.coreHeight ≤ 2 := by
  simpa only [show q4_t2.q=4 from rfl] using
    q4_t2.dense_resources (ZMod 3) 2 (by decide) (by decide)
def q4_t3 : Endpoint.Data where
  m := 10
  d := 1
  u := 8
  a := {1,2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_t3_Q :
    q4_t3.wordVolume=11 ∧ q4_t3.coreP (ℚ) ≤ 11 ∧
    q4_t3.actualR (ℚ) ≤ 3 ∧ (3 ≤ 2 → q4_t3.actualR (ℚ)=0) ∧
    q4_t3.coreHeight ≤ 3 := by
  simpa only [show q4_t3.q=4 from rfl] using
    q4_t3.dense_resources (ℚ) 3 (by decide) (by decide)
theorem q4_t3_char2 :
    q4_t3.wordVolume=11 ∧ q4_t3.coreP (ZMod 2) ≤ 11 ∧
    q4_t3.actualR (ZMod 2) ≤ 3 ∧ (3 ≤ 2 → q4_t3.actualR (ZMod 2)=0) ∧
    q4_t3.coreHeight ≤ 3 := by
  simpa only [show q4_t3.q=4 from rfl] using
    q4_t3.dense_resources (ZMod 2) 3 (by decide) (by decide)
theorem q4_t3_char3 :
    q4_t3.wordVolume=11 ∧ q4_t3.coreP (ZMod 3) ≤ 11 ∧
    q4_t3.actualR (ZMod 3) ≤ 3 ∧ (3 ≤ 2 → q4_t3.actualR (ZMod 3)=0) ∧
    q4_t3.coreHeight ≤ 3 := by
  simpa only [show q4_t3.q=4 from rfl] using
    q4_t3.dense_resources (ZMod 3) 3 (by decide) (by decide)
def q4_t4 : Endpoint.Data where
  m := 11
  d := 1
  u := 9
  a := {1,2,7,8}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
theorem q4_t4_Q :
    q4_t4.wordVolume=13 ∧ q4_t4.coreP (ℚ) ≤ 13 ∧
    q4_t4.actualR (ℚ) ≤ 4 ∧ (4 ≤ 2 → q4_t4.actualR (ℚ)=0) ∧
    q4_t4.coreHeight ≤ 4 := by
  simpa only [show q4_t4.q=4 from rfl] using
    q4_t4.dense_resources (ℚ) 4 (by decide) (by decide)
theorem q4_t4_char2 :
    q4_t4.wordVolume=13 ∧ q4_t4.coreP (ZMod 2) ≤ 13 ∧
    q4_t4.actualR (ZMod 2) ≤ 4 ∧ (4 ≤ 2 → q4_t4.actualR (ZMod 2)=0) ∧
    q4_t4.coreHeight ≤ 4 := by
  simpa only [show q4_t4.q=4 from rfl] using
    q4_t4.dense_resources (ZMod 2) 4 (by decide) (by decide)
theorem q4_t4_char3 :
    q4_t4.wordVolume=13 ∧ q4_t4.coreP (ZMod 3) ≤ 13 ∧
    q4_t4.actualR (ZMod 3) ≤ 4 ∧ (4 ≤ 2 → q4_t4.actualR (ZMod 3)=0) ∧
    q4_t4.coreHeight ≤ 4 := by
  simpa only [show q4_t4.q=4 from rfl] using
    q4_t4.dense_resources (ZMod 3) 4 (by decide) (by decide)
def dilated_q3_t2 : Endpoint.Data where
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
theorem dilated_q3_t2_Q :
    dilated_q3_t2.wordVolume=8 ∧ dilated_q3_t2.coreP (ℚ) ≤ 8 ∧
    dilated_q3_t2.actualR (ℚ) ≤ 2 ∧ (2 ≤ 2 → dilated_q3_t2.actualR (ℚ)=0) ∧
    dilated_q3_t2.coreHeight ≤ 2 := by
  simpa only [show dilated_q3_t2.q=3 from rfl] using
    dilated_q3_t2.dense_resources (ℚ) 2 (by decide) (by decide)
theorem dilated_q3_t2_char2 :
    dilated_q3_t2.wordVolume=8 ∧ dilated_q3_t2.coreP (ZMod 2) ≤ 8 ∧
    dilated_q3_t2.actualR (ZMod 2) ≤ 2 ∧ (2 ≤ 2 → dilated_q3_t2.actualR (ZMod 2)=0) ∧
    dilated_q3_t2.coreHeight ≤ 2 := by
  simpa only [show dilated_q3_t2.q=3 from rfl] using
    dilated_q3_t2.dense_resources (ZMod 2) 2 (by decide) (by decide)
theorem dilated_q3_t2_char3 :
    dilated_q3_t2.wordVolume=8 ∧ dilated_q3_t2.coreP (ZMod 3) ≤ 8 ∧
    dilated_q3_t2.actualR (ZMod 3) ≤ 2 ∧ (2 ≤ 2 → dilated_q3_t2.actualR (ZMod 3)=0) ∧
    dilated_q3_t2.coreHeight ≤ 2 := by
  simpa only [show dilated_q3_t2.q=3 from rfl] using
    dilated_q3_t2.dense_resources (ZMod 3) 2 (by decide) (by decide)
end NSP14.Tests.DenseResources
